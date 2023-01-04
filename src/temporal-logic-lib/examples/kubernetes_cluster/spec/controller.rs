// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::kubernetes_cluster::spec::common::*;
use crate::pervasive::{map::*, option::*, seq::*, set::*, string::*};
use crate::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

/// let's start from simple and forget about CreateStsDone for now
pub enum ReconcileCoreStep {
    Init,
    GetCRDone,
    CreateCMDone,
    // CreateStsDone,
    Done,
    Error
}

pub open spec fn ending_step(step: ReconcileCoreStep) -> bool {
    ||| step === ReconcileCoreStep::Done
    ||| step === ReconcileCoreStep::Error
}

pub struct ReconcileState {
    pub reconcile_step: ReconcileCoreStep,
    pub pending_req_msg: Option<Message>,
}

pub struct State {
    pub ongoing_reconciles: Map<ResourceKey, ReconcileState>,
    pub scheduled_reconciles: Set<ResourceKey>,
}

pub struct ControllerActionInput {
    pub recv: Option<Message>,
    pub scheduled_cr_key: Option<ResourceKey>,
}

#[is_variant]
pub enum Step {
    TriggerReconcile,
    RunScheduledReconcile,
    ContinueReconcile,
    EndReconcile,
}

pub type ControllerStateMachine = StateMachine<State, ControllerActionInput, ControllerActionInput, Set<Message>, Step>;

pub type ControllerAction = Action<State, ControllerActionInput, Set<Message>>;

pub type ControllerActionResult = ActionResult<State, Set<Message>>;

pub open spec fn msg_to_kubernetes_api(msg_content: MessageContent) -> Message {
    form_msg(HostId::CustomController, HostId::KubernetesAPI, msg_content)
}

/// This is a highly simplified triggering condition
/// which only considers creation/update to CR objects.
/// TODO: Reason about ownership and other relationships.
pub open spec fn relevant_cr_key(msg: Message) -> Option<ResourceKey>
    recommends
        msg.content.is_WatchEvent(),
{
    if msg.is_watch_event_of_kind(ResourceKind::CustomResourceKind) {
        if msg.is_added_event() {
            Option::Some(msg.get_added_event().obj.key)
        } else if msg.is_modified_event() {
            Option::Some(msg.get_modified_event().obj.key)
        } else {
            Option::None
        }
    } else {
        Option::None
    }
}

pub open spec fn subresource_configmap(cr_key: ResourceKey) -> ResourceObj
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    ResourceObj {
        key: ResourceKey {
            name: cr_key.name + cm_suffix(),
            namespace: cr_key.namespace,
            kind: ResourceKind::ConfigMapKind
        },
    }
}

pub open spec fn create_cm_req(cr_key: ResourceKey) -> APIRequest
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    APIRequest::CreateRequest(CreateRequest{
        obj: subresource_configmap(cr_key),
    })
}

pub open spec fn create_sts_req(cr_key: ResourceKey) -> APIRequest
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    APIRequest::CreateRequest(CreateRequest{
        obj: ResourceObj {
            key: ResourceKey {
                name: cr_key.name + sts_suffix(),
                namespace: cr_key.namespace,
                kind: ResourceKind::StatefulSetKind
            },
        },
    })
}

/// This is a highly simplified reconcile core spec:
/// it sends requests to create a configmap and a statefulset for the cr.
pub open spec fn reconcile_core(cr_key: ResourceKey, step: ReconcileCoreStep, resp_o: Option<APIResponse>) -> (ReconcileCoreStep, Option<APIRequest>)
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    match step {
        ReconcileCoreStep::Init => {
            (ReconcileCoreStep::GetCRDone, Option::Some(APIRequest::GetRequest(GetRequest{key: cr_key})))
        },
        ReconcileCoreStep::GetCRDone => {
            (ReconcileCoreStep::CreateCMDone, Option::Some(create_cm_req(cr_key)))
            // if resp_o.is_None() {
            //     (ReconcileCoreStep::Error, Option::None)
            // } else {
            //     if is_ok_resp(resp_o.get_Some_0()) {
            //         (ReconcileCoreStep::CreateCMDone, Option::Some(create_cm_req(cr_key)))
            //     } else {
            //         (ReconcileCoreStep::Done, Option::None)
            //     }
            // }
        },
        ReconcileCoreStep::CreateCMDone => {
            (ReconcileCoreStep::Done, Option::None)
            // if resp_o.is_None() {
            //     (ReconcileCoreStep::Error, Option::None)
            // } else {
            //     if is_ok_resp(resp_o.get_Some_0()) {
            //         (ReconcileCoreStep::Done, Option::None)
            //         // (ReconcileCoreStep::CreateStsDone, Option::Some(create_sts_req(cr_key)))
            //     } else {
            //         (ReconcileCoreStep::Error, Option::None)
            //     }
            // }
        },
        // ReconcileCoreStep::CreateStsDone => {
        //     if resp_o.is_None() {
        //         (ReconcileCoreStep::Error, Option::None)
        //     } else {
        //         if is_ok_resp(resp_o.get_Some_0()) {
        //             (ReconcileCoreStep::Done, Option::None)
        //         } else {
        //             (ReconcileCoreStep::Error, Option::None)
        //         }
        //     }
        // },
        ReconcileCoreStep::Done => {
            (ReconcileCoreStep::Done, Option::None)
        },
        ReconcileCoreStep::Error => {
            (ReconcileCoreStep::Error, Option::None)
        }
    }
}

/// This action specifies how the watcher triggers reconcile.
/// It is highly simplified compared to the actual watcher implementation in kube-rs:
/// (1) The triggering condition should come from the developer. Currently we hardcode it in
/// relevant_cr_key.
/// (2) The watcher and reconciler run concurrently: the watcher can take incoming events while
/// the reconciler is in reconcile. If the reconciler is working on object X, all the incoming
/// events related to X will stay pending in a queue.
/// (3) The watcher deduplicates triggering events for the same object: if an event for object X
/// comes but there is already another pending event for the same object, the incoming event is
/// discarded.
pub open spec fn trigger_reconcile() -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: State| {
            // TODO: we should have an action for requeued reconcile
            // TODO: We should have multiple queues for storing triggering events.
            // Each queue stores the event relates to the same cr key.
            &&& input.scheduled_cr_key.is_None()
            &&& input.recv.is_Some()
            &&& input.recv.get_Some_0().dst === HostId::CustomController
            &&& input.recv.get_Some_0().content.is_WatchEvent()
            &&& relevant_cr_key(input.recv.get_Some_0()).is_Some()
            &&& !s.ongoing_reconciles.dom().contains(relevant_cr_key(input.recv.get_Some_0()).get_Some_0())
        },
        transition: |input: ControllerActionInput, s: State| {
            let cr_key = relevant_cr_key(input.recv.get_Some_0()).get_Some_0();
            let initialized_reconcile_state = ReconcileState {
                reconcile_step: ReconcileCoreStep::Init,
                pending_req_msg: Option::None,
            };
            let s_prime = State {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, initialized_reconcile_state),
                ..s
            };
            let send = Set::empty();
            (s_prime, send)
        },
    }
}

pub open spec fn run_scheduled_reconcile() -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: State| {
            &&& input.scheduled_cr_key.is_Some()
            &&& s.scheduled_reconciles.contains(input.scheduled_cr_key.get_Some_0())
            &&& input.recv.is_None()
            &&& !s.ongoing_reconciles.dom().contains(input.scheduled_cr_key.get_Some_0())
        },
        transition: |input: ControllerActionInput, s: State| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let initialized_reconcile_state = ReconcileState {
                reconcile_step: ReconcileCoreStep::Init,
                pending_req_msg: Option::None,
            };
            let s_prime = State {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, initialized_reconcile_state),
                scheduled_reconciles: s.scheduled_reconciles.remove(cr_key),
                ..s
            };
            let send = Set::empty();
            (s_prime, send)
        },
    }
}

pub open spec fn continue_reconcile() -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: State| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();
                let reconcile_state = s.ongoing_reconciles[cr_key];

                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& if input.recv.is_Some() {
                    &&& input.recv.get_Some_0().content.is_APIResponse()
                    &&& reconcile_state.pending_req_msg.is_Some()
                    &&& resp_msg_matches_req_msg(input.recv.get_Some_0(), reconcile_state.pending_req_msg.get_Some_0())
                } else {
                    reconcile_state.pending_req_msg.is_None()
                }
                &&& !ending_step(reconcile_state.reconcile_step)
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: State| {
            let resp_o = if input.recv.is_Some() {
                Option::Some(input.recv.get_Some_0().content.get_APIResponse_0())
            } else {
                Option::None
            };
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let reconcile_state = s.ongoing_reconciles[cr_key];

            let (next_step, req_o) = reconcile_core(cr_key, reconcile_state.reconcile_step, resp_o);

            let pending_req_msg = if req_o.is_Some() {
                Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(req_o.get_Some_0())))
            } else {
                Option::None
            };
            let reconcile_state_prime = ReconcileState {
                reconcile_step: next_step,
                pending_req_msg: pending_req_msg,
            };
            let s_prime = State {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, reconcile_state_prime),
                ..s
            };
            let send = if pending_req_msg.is_Some() {
                set![pending_req_msg.get_Some_0()]
            } else {
                Set::empty()
            };
            (s_prime, send)
        }
    }
}

pub open spec fn end_reconcile() -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: State| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();
                let reconcile_state = s.ongoing_reconciles[cr_key];

                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& input.recv.is_None()
                &&& ending_step(reconcile_state.reconcile_step)
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: State| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let s_prime = State {
                ongoing_reconciles: s.ongoing_reconciles.remove(cr_key),
                scheduled_reconciles: s.scheduled_reconciles.insert(cr_key),
                ..s
            };
            (s_prime, Set::empty())
        }
    }
}

pub open spec fn controller() -> ControllerStateMachine {
    StateMachine {
        init: |s: State| {
            s === State {
                ongoing_reconciles: Map::empty(),
                scheduled_reconciles: Set::empty(),
            }
        },
        actions: set![trigger_reconcile(), run_scheduled_reconcile(), continue_reconcile(), end_reconcile()],
        step_to_action: |step: Step| {
            match step {
                Step::TriggerReconcile => trigger_reconcile(),
                Step::RunScheduledReconcile => run_scheduled_reconcile(),
                Step::ContinueReconcile => continue_reconcile(),
                Step::EndReconcile => end_reconcile(),
            }
        },
        action_input: |step: Step, input: ControllerActionInput| {
            input
        }
    }
}

}
