// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, dynamic::*, error::*, resource::*};
use crate::kubernetes_cluster::spec::{
    client::{client, ClientActionInput, ClientState},
    controller::{
        common::{
            init_controller_state, ControllerAction, ControllerActionInput, ControllerState,
            OngoingReconcile,
        },
        state_machine::controller,
    },
    kubernetes_api::{
        common::{KubernetesAPIAction, KubernetesAPIActionInput, KubernetesAPIState},
        state_machine::kubernetes_api,
    },
    message::*,
    network::{network, NetworkState},
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct State<K: ResourceView, T> {
    pub kubernetes_api_state: KubernetesAPIState,
    pub controller_state: ControllerState<K, T>,
    pub client_state: ClientState,
    pub network_state: NetworkState,
    pub rest_id_allocator: RestIdAllocator,
    pub crash_enabled: bool,
    pub busy_enabled: bool,
}

impl<K: ResourceView, T> State<K, T> {
    #[verifier(inline)]
    pub open spec fn message_in_flight(self, msg: Message) -> bool {
        self.network_state.in_flight.contains(msg)
    }

    pub open spec fn resource_key_exists(self, key: ObjectRef) -> bool {
        self.kubernetes_api_state.resources.dom().contains(key)
    }

    pub open spec fn resource_obj_exists(self, obj: DynamicObjectView) -> bool {
        &&& self.kubernetes_api_state.resources.dom().contains(obj.object_ref())
        &&& self.kubernetes_api_state.resources[obj.object_ref()] == obj
    }

    pub open spec fn resource_obj_of(self, key: ObjectRef) -> DynamicObjectView
        recommends self.resource_key_exists(key)
    {
        self.kubernetes_api_state.resources[key]
    }

    #[verifier(inline)]
    pub open spec fn reconcile_state_contains(self, key: ObjectRef) -> bool {
        self.controller_state.ongoing_reconciles.dom().contains(key)
    }

    pub open spec fn reconcile_state_of(self, key: ObjectRef) -> OngoingReconcile<K, T>
        recommends
            self.reconcile_state_contains(key),
    {
        self.controller_state.ongoing_reconciles[key]
    }

    pub open spec fn triggering_cr_of(self, key: ObjectRef) -> K
        recommends
            self.reconcile_state_contains(key),
    {
        self.controller_state.ongoing_reconciles[key].triggering_cr
    }

    #[verifier(inline)]
    pub open spec fn pending_req_of(self, key: ObjectRef) -> Message
        recommends
            self.reconcile_state_contains(key),
            self.reconcile_state_of(key).pending_req_msg.is_Some(),
    {
        self.controller_state.ongoing_reconciles[key].pending_req_msg.get_Some_0()
    }

    pub open spec fn reconcile_scheduled_for(self, key: ObjectRef) -> bool {
        self.controller_state.scheduled_reconciles.contains_key(key)
    }

    pub open spec fn reconcile_scheduled_obj_of(self, key: ObjectRef) -> K
        recommends
            self.reconcile_scheduled_for(key),
    {
        self.controller_state.scheduled_reconciles[key]
    }

    pub open spec fn rest_id_counter_is_no_smaller_than(self, rest_id: nat) -> bool {
        self.rest_id_allocator.rest_id_counter >= rest_id
    }
}

pub open spec fn init<K: ResourceView, T, ReconcilerType: Reconciler<K ,T>>() -> StatePred<State<K, T>> {
    |s: State<K, T>| {
        &&& (kubernetes_api().init)(s.kubernetes_api_state)
        &&& (controller::<K, T, ReconcilerType>().init)(s.controller_state)
        &&& (client::<K>().init)(s.client_state)
        &&& (network().init)(s.network_state)
        &&& s.crash_enabled
        &&& s.busy_enabled
    }
}

pub open spec fn received_msg_destined_for(recv: Option<Message>, host_id: HostId) -> bool {
    if recv.is_Some() {
        recv.get_Some_0().dst == host_id
    } else {
        true
    }
}

pub open spec fn kubernetes_api_next<K: ResourceView, T>() -> Action<State<K, T>, Option<Message>, ()> {
    let result = |input: Option<Message>, s: State<K, T>| {
        let host_result = kubernetes_api().next_result(
            KubernetesAPIActionInput{recv: input, rest_id_allocator: s.rest_id_allocator},
            s.kubernetes_api_state
        );
        let msg_ops = MessageOps {
            recv: input,
            send: host_result.get_Enabled_1().0,
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |input: Option<Message>, s: State<K, T>| {
            &&& received_msg_destined_for(input, HostId::KubernetesAPI)
            &&& result(input, s).0.is_Enabled()
            &&& result(input, s).1.is_Enabled()
        },
        transition: |input: Option<Message>, s: State<K, T>| {
            (State {
                kubernetes_api_state: result(input, s).0.get_Enabled_0(),
                network_state: result(input, s).1.get_Enabled_0(),
                rest_id_allocator: result(input, s).0.get_Enabled_1().1,
                ..s
            }, ())
        },
    }
}

pub open spec fn controller_next<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>() -> Action<State<K, T>, (Option<Message>, Option<ObjectRef>), ()> {
    let result = |input: (Option<Message>, Option<ObjectRef>), s: State<K, T>| {
        let host_result = controller::<K, T, ReconcilerType>().next_result(
            ControllerActionInput{recv: input.0, scheduled_cr_key: input.1, rest_id_allocator: s.rest_id_allocator},
            s.controller_state
        );
        let msg_ops = MessageOps {
            recv: input.0,
            send: host_result.get_Enabled_1().0,
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |input: (Option<Message>, Option<ObjectRef>), s: State<K, T>| {
            &&& received_msg_destined_for(input.0, HostId::CustomController)
            &&& result(input, s).0.is_Enabled()
            &&& result(input, s).1.is_Enabled()
        },
        transition: |input: (Option<Message>, Option<ObjectRef>), s: State<K, T>| {
            (State {
                controller_state: result(input, s).0.get_Enabled_0(),
                network_state: result(input, s).1.get_Enabled_0(),
                rest_id_allocator: result(input, s).0.get_Enabled_1().1,
                ..s
            }, ())
        },
    }
}

/// This action checks whether a custom resource exists in the Kubernetes API and if so schedule a controller
/// reconcile for it. It is used to set up the assumption for liveness proof: for a existing cr, the reconcile is
/// infinitely frequently invoked for it. The assumption that cr always exists and the weak fairness assumption on this
/// action allow us to prove reconcile is always eventually scheduled.
///
/// This action abstracts away a lot of implementation details in the Kubernetes API and kube framework,
/// such as the list-then-watch pattern.
///
/// In general, this action assumes the following key behavior:
/// (1) The kube library always invokes `reconcile_with` (defined in the shim layer) whenever a cr object gets created
///   -- so the first creation event will schedule a reconcile
/// (2) The shim layer always re-queues `reconcile_with` unless the corresponding cr object does not exist,
/// and the kube library always eventually invokes the re-queued `reconcile_with`
///   -- so as long as the cr still exists, the reconcile will still be scheduled over and over again
/// (3) The shim layer always performs a quorum read to etcd to get the cr object and passes it to `reconcile_core`
///   -- so the reconcile is scheduled with the most recent view of the cr object when this action happens
/// (4) The shim layer never invokes `reconcile_core` if the cr object does not exist
///   -- this is not assumed by `schedule_controller_reconcile` because it never talks about what should happen if the
///   cr object does not exist, but it is still important because `schedule_controller_reconcile` is the only
///   action that can schedule a reconcile in our state machine.
pub open spec fn schedule_controller_reconcile<K: ResourceView, T>() -> Action<State<K, T>, ObjectRef, ()> {
    Action {
        precondition: |input: ObjectRef, s: State<K, T>| {
            &&& s.resource_key_exists(input)
            &&& input.kind.is_CustomResourceKind()
            &&& K::from_dynamic_object(s.resource_obj_of(input)).is_Ok()
        },
        transition: |input: ObjectRef, s: State<K, T>| {
            (State {
                controller_state: ControllerState {
                    scheduled_reconciles: s.controller_state.scheduled_reconciles.insert(input, K::from_dynamic_object(s.resource_obj_of(input)).get_Ok_0()),
                    ..s.controller_state
                },
                ..s
            }, ())
        }
    }
}

/// This action restarts the crashed controller.
pub open spec fn restart_controller<K: ResourceView, T>() -> Action<State<K, T>, (), ()> {
    Action {
        precondition: |input: (), s: State<K, T>| {
            s.crash_enabled
        },
        transition: |input: (), s: State<K, T>| {
            (State {
                controller_state: init_controller_state(),
                ..s
            }, ())
        },
    }
}

/// This action disallows the controller to crash from this point.
/// This is used to constraint the crash behavior for liveness proof:
/// the controller eventually stops crashing.
pub open spec fn disable_crash<K: ResourceView, T>() -> Action<State<K, T>, (), ()> {
    Action {
        precondition: |input: (), s: State<K, T>| {
            true
        },
        transition: |input: (), s: State<K, T>| {
            (State {
                crash_enabled: false,
                ..s
            }, ())
        },
    }
}

pub open spec fn busy_kubernetes_api_rejects_request<K: ResourceView, T>() -> Action<State<K, T>, Option<Message>, ()> {
    let network_result = |input: Option<Message>, s: State<K, T>| {
        let req_msg = input.get_Some_0();
        let resp = form_matched_resp_msg(req_msg, Result::Err(APIError::ServerTimeout));
        let msg_ops = MessageOps {
            recv: input,
            send: Multiset::singleton(resp),
        };
        let result = network().next_result(msg_ops, s.network_state);
        result
    };
    Action {
        precondition: |input: Option<Message>, s: State<K, T>| {
            &&& s.busy_enabled
            &&& input.is_Some()
            &&& input.get_Some_0().content.is_APIRequest()
            &&& network_result(input, s).is_Enabled()
        },
        transition: |input: Option<Message>, s: State<K, T>| {
            (State {
                network_state: network_result(input, s).get_Enabled_0(),
                ..s
            }, ())
        }
    }
}

/// This action disallows the kubernetes api to be busy from this point.
/// This is used to constraint the crash behavior for liveness proof:
/// the controller eventually stops rejecting requests.
pub open spec fn disable_busy<K: ResourceView, T>() -> Action<State<K, T>, (), ()> {
    Action {
        precondition: |input:(), s: State<K, T>| {
            true
        },
        transition: |input: (), s: State<K, T>| {
            (State {
                busy_enabled: false,
                ..s
            }, ())
        }
    }
}

pub open spec fn client_next<K: ResourceView, T>() -> Action<State<K, T>, (Option<Message>, K), ()> {
    let result = |input: (Option<Message>, K), s: State<K, T>| {
        let host_result = client().next_result(
            ClientActionInput{recv: input.0, cr: input.1, rest_id_allocator: s.rest_id_allocator},
            s.client_state
        );
        let msg_ops = MessageOps {
            recv: input.0,
            send: host_result.get_Enabled_1().0,
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |input: (Option<Message>, K), s: State<K, T>| {
            &&& received_msg_destined_for(input.0, HostId::Client)
            &&& result(input, s).0.is_Enabled()
            &&& result(input, s).1.is_Enabled()
        },
        transition: |input: (Option<Message>, K), s: State<K, T>| {
            (State {
                client_state: result(input, s).0.get_Enabled_0(),
                network_state: result(input, s).1.get_Enabled_0(),
                rest_id_allocator: result(input, s).0.get_Enabled_1().1,
                ..s
            }, ())
        },
    }
}

pub open spec fn stutter<K: ResourceView, T>() -> Action<State<K, T>, (), ()> {
    Action {
        precondition: |input: (), s: State<K, T>| {
            true
        },
        transition: |input: (), s: State<K, T>| {
            (s, ())
        },
    }
}

#[is_variant]
pub enum Step<K> {
    KubernetesAPIStep(Option<Message>),
    ControllerStep((Option<Message>, Option<ObjectRef>)),
    ClientStep((Option<Message>, K)),
    ScheduleControllerReconcileStep(ObjectRef),
    RestartController(),
    DisableCrash(),
    KubernetesBusy(Option<Message>),
    DisableBusy(),
    StutterStep(),
}

pub open spec fn next_step<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>
    (s: State<K, T>, s_prime: State<K, T>, step: Step<K>) -> bool {
    match step {
        Step::KubernetesAPIStep(input) => kubernetes_api_next().forward(input)(s, s_prime),
        Step::ControllerStep(input) => controller_next::<K, T, ReconcilerType>().forward(input)(s, s_prime),
        Step::ClientStep(input) => client_next().forward(input)(s, s_prime),
        Step::ScheduleControllerReconcileStep(input) => schedule_controller_reconcile().forward(input)(s, s_prime),
        Step::RestartController() => restart_controller().forward(())(s, s_prime),
        Step::DisableCrash() => disable_crash().forward(())(s, s_prime),
        Step::KubernetesBusy(input) => busy_kubernetes_api_rejects_request().forward(input)(s, s_prime),
        Step::DisableBusy() => disable_busy().forward(())(s, s_prime),
        Step::StutterStep() => stutter().forward(())(s, s_prime),
    }
}

/// `next` chooses:
/// * which host to take the next action (`Step`)
/// * whether to deliver a message and which message to deliver (`Option<Message>` in `Step`)
pub open spec fn next<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>() -> ActionPred<State<K, T>> {
    |s: State<K, T>, s_prime: State<K, T>| exists |step: Step<K>| next_step::<K, T, ReconcilerType>(s, s_prime, step)
}

/// We install the reconciler to the Kubernetes cluster state machine spec
/// TODO: develop a struct for the compound state machine and make reconciler its member
/// so that we don't have to pass reconciler to init and next in the proof.
pub open spec fn sm_spec<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>() -> TempPred<State<K, T>> {
    lift_state(init::<K, T, ReconcilerType>()).and(sm_partial_spec::<K, T, ReconcilerType>())
}

pub open spec fn sm_partial_spec<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>() -> TempPred<State<K, T>> {
    always(lift_action(next::<K, T, ReconcilerType>()))
    .and(tla_forall(|input| kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| controller_next::<K, T, ReconcilerType>().weak_fairness(input)))
    .and(tla_forall(|input| schedule_controller_reconcile().weak_fairness(input)))
    .and(disable_crash().weak_fairness(()))
    .and(disable_busy().weak_fairness(()))
}

pub open spec fn kubernetes_api_action_pre<K: ResourceView, T>(action: KubernetesAPIAction, input: Option<Message>) -> StatePred<State<K, T>> {
    |s: State<K, T>| {
        let host_result = kubernetes_api().next_action_result(
            action,
            KubernetesAPIActionInput{recv: input, rest_id_allocator: s.rest_id_allocator},
            s.kubernetes_api_state
        );
        let msg_ops = MessageOps {
            recv: input,
            send: host_result.get_Enabled_1().0,
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        &&& received_msg_destined_for(input, HostId::KubernetesAPI)
        &&& host_result.is_Enabled()
        &&& network_result.is_Enabled()
    }
}

pub open spec fn controller_action_pre<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(action: ControllerAction<K, T>, input: (Option<Message>, Option<ObjectRef>)) -> StatePred<State<K, T>> {
    |s: State<K, T>| {
        let host_result = controller::<K, T, ReconcilerType>().next_action_result(
            action,
            ControllerActionInput{recv: input.0, scheduled_cr_key: input.1, rest_id_allocator: s.rest_id_allocator},
            s.controller_state
        );
        let msg_ops = MessageOps {
            recv: input.0,
            send: host_result.get_Enabled_1().0,
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        &&& received_msg_destined_for(input.0, HostId::CustomController)
        &&& host_result.is_Enabled()
        &&& network_result.is_Enabled()
    }
}

pub open spec fn crash_disabled<K: ResourceView, T>() -> StatePred<State<K, T>> {
    |s: State<K, T>| !s.crash_enabled
}

pub open spec fn busy_disabled<K: ResourceView, T>() -> StatePred<State<K, T>> {
    |s: State<K, T>| !s.busy_enabled
}

pub open spec fn rest_id_counter_is<K: ResourceView, T>(rest_id: nat) -> StatePred<State<K, T>> {
    |s: State<K, T>| s.rest_id_allocator.rest_id_counter == rest_id
}

pub open spec fn rest_id_counter_is_no_smaller_than<K: ResourceView, T>(rest_id: nat) -> StatePred<State<K, T>> {
    |s: State<K, T>| s.rest_id_allocator.rest_id_counter >= rest_id
}

}
