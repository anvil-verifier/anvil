// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, object::*};
use crate::kubernetes_cluster::spec::{
    channel::*,
    kubernetes_api::{builtin_controllers::statefulset_controller, common::*},
    message::*,
};
use crate::pervasive::{map::*, multiset::*, option::*, result::*, seq::*, set::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn handle_get_request(msg: Message, s: KubernetesAPIState) -> (EtcdState, Message, Option<WatchEvent>)
    recommends
        msg.content.is_get_request(),
{
    let req = msg.content.get_get_request();
    if !s.resources.dom().contains(req.key) {
        // Get fails
        let result = Result::Err(APIError::ObjectNotFound);
        let resp = form_get_resp_msg(msg, result);
        (s.resources, resp, Option::None)
    } else {
        // Get succeeds
        let result = Result::Ok(s.resources[req.key]);
        let resp = form_get_resp_msg(msg, result);
        (s.resources, resp, Option::None)
    }
}

pub open spec fn list_query(list_req: ListRequest, s: KubernetesAPIState) -> Seq<KubernetesObject> {
    // TODO: the returned seq should contain all the objects of the resource kind in the resources map
    Seq::empty()
}

pub open spec fn handle_list_request(msg: Message, s: KubernetesAPIState) -> (EtcdState, Message, Option<WatchEvent>)
    recommends
        msg.content.is_list_request(),
{
    let req = msg.content.get_list_request();
    let result = Result::Ok(list_query(req, s));
    let resp = form_list_resp_msg(msg, result);
    (s.resources, resp, Option::None)
}

pub open spec fn handle_create_request(msg: Message, s: KubernetesAPIState) -> (EtcdState, Message, Option<WatchEvent>)
    recommends
        msg.content.is_create_request(),
{
    let req = msg.content.get_create_request();
    if s.resources.dom().contains(req.obj.object_ref()) {
        // Creation fails
        let result = Result::Err(APIError::ObjectAlreadyExists);
        let resp = form_create_resp_msg(msg, result);
        (s.resources, resp, Option::None)
    } else {
        // Creation succeeds
        let result = Result::Ok(req.obj);
        let resp = form_create_resp_msg(msg, result);
        // The cluster state is updated, so we send a notification to the custom controller
        // TODO: notification should be sent to custom controller selectively
        let notify = added_event(req.obj);
        (s.resources.insert(req.obj.object_ref(), req.obj), resp, Option::Some(notify))
    }
}

pub open spec fn handle_delete_request(msg: Message, s: KubernetesAPIState) -> (EtcdState, Message, Option<WatchEvent>)
    recommends
        msg.content.is_delete_request(),
{
    let req = msg.content.get_delete_request();
    if !s.resources.dom().contains(req.key) {
        // Deletion fails
        let result = Result::Err(APIError::ObjectNotFound);
        let resp = form_delete_resp_msg(msg, result);
        (s.resources, resp, Option::None)
    } else {
        // Path where deletion succeeds
        let obj_before_deletion = s.resources[req.key];
        // The cluster state is updated, so we send a notification to the custom controller
        // TODO: watch event should be sent to custom controller selectively
        let result = Result::Ok(obj_before_deletion);
        let resp = form_delete_resp_msg(msg, result);
        let notify = deleted_event(obj_before_deletion);
        (s.resources.remove(req.key), resp, Option::Some(notify))
    }
}

// etcd is modeled as a centralized map that handles get/create/delete
// TODO: support list/update/statusupdate
pub open spec fn transition_by_etcd(msg: Message, s: KubernetesAPIState) -> (EtcdState, Message, Option<WatchEvent>)
    recommends
        msg.content.is_APIRequest(),
{
    if msg.content.is_get_request() {
        handle_get_request(msg, s)
    } else if msg.content.is_list_request() {
        handle_list_request(msg, s)
    } else if msg.content.is_create_request() {
        handle_create_request(msg, s)
    } else {
        handle_delete_request(msg, s)
    }
}

/// Collect the requests from the builtin controllers
pub open spec fn transition_by_builtin_controllers(event: WatchEvent, s: KubernetesAPIState, chan_manager: ChannelManager) -> (ChannelManager, Multiset<Message>) {
    // We only have spec of statefulset_controller for now
    statefulset_controller::transition_by_statefulset_controller(event, s, chan_manager)
}

pub open spec fn handle_request() -> KubernetesAPIAction {
    Action {
        precondition: |input: KubernetesAPIActionInput, s: KubernetesAPIState| {
            &&& input.0.is_Some()
            &&& input.0.get_Some_0().content.is_APIRequest()
            // This dst check is redundant since the compound state machine has checked it
            &&& input.0.get_Some_0().dst == HostId::KubernetesAPI
        },
        transition: |input: KubernetesAPIActionInput, s: KubernetesAPIState| {
            // This transition describes how Kubernetes API server handles requests,
            // which consists of multiple steps in reality:
            //
            // (1) apiserver receives the request from some controller/client,
            //  perform some validation (e.g., through webhook)
            //  and forwards the request to the underlying datastore (e.g., etcd);
            // (2) The datastore reads/writes the cluster state and replies to apiserver;
            // (3) The datastore also sends a notification of state update caused by the request to apiserver;
            // (4) apiserver replies to the controller/client that sent the request;
            // (5) apiserver forwards the notification to any controllers/clients that subscribes for the updates.
            //
            // Note that built-in controllers often subscribes for updates to several kinds of resources.
            // For example, the statefulset controller subscribes updates to all statefulset objects.
            // When seeing a new statefulset is created,
            // it will send requests to create pods and volumes owned by this statefulset.
            //
            // Here we simplify step (1) ~ (5) and make the following compromise in this specification:
            // (a) making the apiserver directly forward requests to the datastore without validation;
            // (b) omitting the notification stream from the datastore to apiserver then to built-in controller,
            //  and making built-in controllers immediately activated by updates to cluster state;
            // (c) baking them into one action, which makes them atomic.
            let input_msg = input.0;
            let input_chan_manager = input.1;

            let (etcd_state, etcd_resp, etcd_notify_o) = transition_by_etcd(input_msg.get_Some_0(), s);
            let s_after_etcd_transition = KubernetesAPIState {
                resources: etcd_state,
                ..s
            };
            if etcd_notify_o.is_Some() {
                let (chan_manager_prime, controller_requests) = transition_by_builtin_controllers(etcd_notify_o.get_Some_0(), s_after_etcd_transition, input_chan_manager);
                let s_prime = KubernetesAPIState {
                    ..s_after_etcd_transition
                };
                (s_prime, (Multiset::empty().insert(etcd_resp).add(controller_requests), chan_manager_prime))
            } else {
                let s_prime = s_after_etcd_transition;
                (s_prime, (Multiset::singleton(etcd_resp), input_chan_manager))
            }
        },
    }
}

pub open spec fn kubernetes_api() -> KubernetesAPIStateMachine {
    StateMachine {
        init: |s: KubernetesAPIState| s == KubernetesAPIState {
            resources: Map::empty(),
        },
        actions: set![handle_request()],
        step_to_action: |step: KubernetesAPIStep| {
            match step {
                KubernetesAPIStep::HandleRequest => handle_request(),
            }
        },
        action_input: |step: KubernetesAPIStep, input: KubernetesAPIActionInput| {
            input
        }
    }
}

}
