// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::kubernetes_cluster::spec::common::*;
use crate::pervasive::{map::*, option::*, result::*, seq::*, set::*, string::*};
use crate::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct State {
    pub resources: Map<ResourceKey, ResourceObj>,
}

pub enum Step {
    HandleRequest,
}

pub type KubernetesAPIActionInput = Option<Message>;

pub type KubernetesAPIStateMachine = StateMachine<State, KubernetesAPIActionInput, KubernetesAPIActionInput, Set<Message>, Step>;

pub type KubernetesAPIAction = Action<State, KubernetesAPIActionInput, Set<Message>>;

pub type KubernetesAPIActionResult = ActionResult<State, Set<Message>>;

pub open spec fn transition_by_etcd(msg: Message, s: State) -> (State, Message, KubernetesAPIActionInput)
    recommends
        msg.content.is_APIRequest(),
{
    let src = msg.dst;
    let dst = msg.src;
    if msg.is_get_request() {
        let req = msg.get_get_request();
        if !s.resources.dom().contains(req.key) {
            // Get fails
            let s_prime = s;
            let result = Result::Err(APIError::ObjectNotFound);
            let resp = form_get_resp_msg(msg, result);
            (s_prime, resp, Option::None)
        } else {
            // Get succeeds
            let s_prime = s;
            let result = Result::Ok(s.resources[req.key]);
            let resp = form_get_resp_msg(msg, result);
            (s_prime, resp, Option::None)
        }
    } else if msg.is_list_request() {
        // TODO: implement list request handling
        let req = msg.get_list_request();
        let s_prime = s;
        let result = Result::Err(APIError::ObjectNotFound);
        let resp = form_msg(src, dst, list_resp_msg(result, req));
        (s_prime, resp, Option::None)
    } else if msg.is_create_request() {
        let req = msg.get_create_request();
        if s.resources.dom().contains(req.obj.key) {
            // Creation fails
            let s_prime = s;
            let result = Result::Err(APIError::ObjectAlreadyExists);
            let resp = form_msg(src, dst, create_resp_msg(result, req));
            (s_prime, resp, Option::None)
        } else {
            // Creation succeeds
            let s_prime = State{
                resources: s.resources.insert(req.obj.key, req.obj),
                ..s
            };
            let result = Result::Ok(req.obj);
            let resp = form_msg(src, dst, create_resp_msg(result, req));
            // The cluster state is updated, so we send a notification to the custom controller
            // TODO: notification should be sent to custom controller selectively
            let notify = form_msg(src, HostId::CustomController, added_event_msg(req.obj));
            (s_prime, resp, Option::Some(notify))
        }
    } else {
        // content is DeleteRequest
        let req = msg.get_delete_request();
        if !s.resources.dom().contains(req.key) {
            // Deletion fails
            let s_prime = s;
            let result = Result::Err(APIError::ObjectNotFound);
            let resp = form_msg(src, dst, delete_resp_msg(result, req));
            (s_prime, resp, Option::None)
        } else {
            // Path where deletion succeeds
            let obj_before_deletion = s.resources[req.key];
            let s_prime = State{
                resources: s.resources.remove(req.key),
                ..s
            };
            // The cluster state is updated, so we send a notification to the custom controller
            // TODO: watch event should be sent to custom controller selectively
            let result = Result::Ok(obj_before_deletion);
            let resp = form_msg(src, dst, delete_resp_msg(result, req));
            let notify = form_msg(src, HostId::CustomController, deleted_event_msg(obj_before_deletion));
            (s_prime, resp, Option::Some(notify))
        }
    }
}

pub open spec fn transition_by_statefulset_controller(msg: Message, s: State) -> Set<Message>
    recommends
        msg.content.is_WatchEvent(),
{
    let src = HostId::KubernetesAPI;
    // Here dst is also KubernetesAPI because etcd, apiserver and built-in controllers are all in the same state machine.
    // In reality, the message is sent from the built-in controller to apiserver then to etcd.
    let dst = HostId::KubernetesAPI;
    if msg.is_watch_event_of_kind(ResourceKind::StatefulSetKind) {
        if msg.is_added_event() {
            let obj = msg.get_added_event().obj;
            set![
                form_msg(src, dst, create_req_msg(ResourceObj{key: ResourceKey{name: obj.key.name + pod_suffix(), namespace: obj.key.namespace, kind: ResourceKind::PodKind}})),
                form_msg(src, dst, create_req_msg(ResourceObj{key: ResourceKey{name: obj.key.name + vol_suffix(), namespace: obj.key.namespace, kind: ResourceKind::VolumeKind}}))
            ]
        } else if msg.is_modified_event() {
            set![]
        } else {
            let obj = msg.get_deleted_event().obj;
            set![
                    form_msg(src, dst, delete_req_msg(ResourceKey{name: obj.key.name + pod_suffix(), namespace: obj.key.namespace, kind: ResourceKind::PodKind})),
                    form_msg(src, dst, delete_req_msg(ResourceKey{name: obj.key.name + vol_suffix(), namespace: obj.key.namespace, kind: ResourceKind::VolumeKind}))
                ]
        }
    } else {
        set![]
    }
}

pub open spec fn transition_by_builtin_controllers(msg: Message, s: State) -> Set<Message>
    recommends
        msg.content.is_WatchEvent(),
{
    transition_by_statefulset_controller(msg, s)
}

pub open spec fn handle_request() -> KubernetesAPIAction {
    Action {
        precondition: |input: KubernetesAPIActionInput, s: State| {
            &&& input.is_Some()
            &&& input.get_Some_0().content.is_APIRequest()
            // This dst check is redundant since the compound state machine has checked it
            &&& input.get_Some_0().dst === HostId::KubernetesAPI
        },
        transition: |input: KubernetesAPIActionInput, s: State| {
            // This transition stitches etcd, built-in controllers and apiserver together.
            // In reality, apiserver receives the request from some controller,
            // then forwards the request to etcd;
            // etcd updates the cluster state and responds to apiserver;
            // apiserver then forwards the response to the controller;
            // Meanwhile, any updates of objects in the cluster state leads to a notification from etcd to apiserver.
            // Apiserver streams the notification to all the (built-in or custom) controllers that subscribe
            // for the particular kind (i.e., object resource type).
            // The notification might activate reconciliation of controllers,
            // which further leads to more requests.
            //
            // For example, the statefulset controller, when seeing a new statefulset is created,
            // will send requests to create pods and volumes owned by this statefulset.
            //
            // Here we simplify the process by
            // (1) removing apiserver and making etcd directly interacting with the request sender;
            // (2) omitting the notification stream from etcd to apiserver to built-in controller)
            // and making built-in controllers immediately activated by updates to cluster state.
            let (s_prime, etcd_resp, etcd_notify_o) = transition_by_etcd(input.get_Some_0(), s);
            if etcd_notify_o.is_Some() {
                let controller_requests = transition_by_builtin_controllers(etcd_notify_o.get_Some_0(), s_prime);
                (s_prime, set![etcd_resp, etcd_notify_o.get_Some_0()] + controller_requests)
            } else {
                (s_prime, set![etcd_resp])
            }
        },
    }
}

pub open spec fn kubernetes_api() -> KubernetesAPIStateMachine {
    StateMachine {
        init: |s: State| s === State{
            resources: Map::empty(),
        },
        actions: set![handle_request()],
        step_to_action: |step: Step| {
            match step {
                Step::HandleRequest => handle_request(),
            }
        },
        action_input: |step: Step, input: KubernetesAPIActionInput| {
            input
        }
    }
}

}
