// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, error::*, object_meta::*,
    persistent_volume_claim::*, pod::*, resource::*, role::*, role_binding::*, secret::*,
    service::*, service_account::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::Cluster,
    kubernetes_api::{builtin_controllers::statefulset_controller, common::*},
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

// TODO:
// + Need more validation checks.
//   For example, RoleBinding's roleRef is immutable: https://kubernetes.io/docs/reference/access-authn-authz/rbac/#clusterrolebinding-example
//
// + Create and update should ignore the status fields provided by the object
//
// + Delete should be done in two phases
//
// + Update should not update the rv if the object remains unchanged
//
// + Set uid when creating and set deletiontimestamp when deleting
//
// + Support more operations like List

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

// TODO: maybe make it a method of DynamicObjectView?
pub open spec fn object_has_well_formed_spec(obj: DynamicObjectView) -> bool {
    &&& obj.kind == ConfigMapView::kind() ==> ConfigMapView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == PersistentVolumeClaimView::kind() ==> PersistentVolumeClaimView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == PodView::kind() ==> PodView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == RoleBindingView::kind() ==> RoleBindingView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == RoleView::kind() ==> RoleView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == SecretView::kind() ==> SecretView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == ServiceView::kind() ==> ServiceView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == StatefulSetView::kind() ==> StatefulSetView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == K::kind() ==> K::unmarshal_spec(obj.spec).is_Ok()
}

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

pub open spec fn list_query(list_req: ListRequest, s: KubernetesAPIState) -> Seq<DynamicObjectView> {
    // TODO: the returned seq should contain all the objects of the resource kind in the resources map
    Seq::empty()
}

pub open spec fn handle_list_request(msg: Message, s: KubernetesAPIState) -> (EtcdState, Message, Option<WatchEvent>)
    recommends
        msg.content.is_list_request(),
{
    let req = msg.content.get_list_request();
    let result = Result::Ok(Self::list_query(req, s));
    let resp = form_list_resp_msg(msg, result);
    (s.resources, resp, Option::None)
}

pub open spec fn validate_create_request(req: CreateRequest, s: KubernetesAPIState) -> Option<APIError> {
    if req.obj.metadata.name.is_None() {
        // Creation fails because the name of the provided object is not provided
        Option::Some(APIError::Invalid)
    } else if req.obj.metadata.namespace.is_Some() && req.namespace != req.obj.metadata.namespace.get_Some_0() {
        // Creation fails because the namespace of the provided object does not match the namespace sent on the request
        Option::Some(APIError::BadRequest)
    } else if !Self::object_has_well_formed_spec(req.obj) {
        // Creation fails because the spec of the provided object is not well formed
        Option::Some(APIError::BadRequest) // TODO: should the error be BadRequest?
    } else if s.resources.dom().contains(req.obj.set_namespace(req.namespace).object_ref()) {
        // Creation fails because the object already exists
        Option::Some(APIError::ObjectAlreadyExists)
    } else if req.obj.kind == K::kind() && !K::rule(K::from_dynamic_object(req.obj).get_Ok_0()) {
        Option::Some(APIError::Invalid)
    } else {
        Option::None
    }
}

pub open spec fn handle_create_request(msg: Message, s: KubernetesAPIState) -> (EtcdState, Message, Option<WatchEvent>)
    recommends
        msg.content.is_create_request(),
{
    let req = msg.content.get_create_request();
    if Self::validate_create_request(req, s).is_Some() {
        // Creation fails because the name of the provided object is not provided
        let result = Result::Err(Self::validate_create_request(req, s).get_Some_0());
        let resp = form_create_resp_msg(msg, result);
        (s.resources, resp, Option::None)
    } else {
        // Creation succeeds
        // Set the namespace and the resource_version of the created object
        let created_obj = req.obj.set_namespace(req.namespace).set_resource_version(s.resource_version_counter);
        let result = Result::Ok(created_obj);
        let resp = form_create_resp_msg(msg, result);
        // The cluster state is updated, so we send a notification to the built-in controllers
        let notify = added_event(created_obj);
        (s.resources.insert(created_obj.object_ref(), created_obj), resp, Option::Some(notify))
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

pub open spec fn update_is_noop(o1: DynamicObjectView, o2: DynamicObjectView) -> bool {
    &&& o1.metadata.generate_name == o2.metadata.generate_name
    &&& o1.metadata.labels == o2.metadata.labels
    &&& o1.spec == o2.spec
}

pub open spec fn validate_update_request(req: UpdateRequest, s: KubernetesAPIState) -> Option<APIError> {
    // let req = msg.content.get_update_request();
    if req.obj.metadata.name.is_None() {
        // Update fails because the name of the object is not provided
        Option::Some(APIError::BadRequest)
    } else if req.key.name != req.obj.metadata.name.get_Some_0() {
        // Update fails because the name of the provided object
        // does not match the name sent on the request
        Option::Some(APIError::BadRequest)
    } else if req.obj.metadata.namespace.is_Some()
        && req.key.namespace != req.obj.metadata.namespace.get_Some_0() {
        // Update fails because the namespace of the provided object
        // does not match the namespace sent on the request
        Option::Some(APIError::BadRequest)
    } else if req.obj.kind != req.key.kind {
        // Update fails because the kind of the provided object
        // does not match the kind sent on the request
        Option::Some(APIError::BadRequest)
    } else if !Self::object_has_well_formed_spec(req.obj) {
        // Update fails because the spec of the provided object is not well formed
        Option::Some(APIError::BadRequest) // TODO: should the error be BadRequest?
    } else if !s.resources.dom().contains(req.key) {
        // Update fails because the object does not exist
        Option::Some(APIError::ObjectNotFound)
    } else if req.obj.metadata.resource_version.is_Some()
        && req.obj.metadata.resource_version != s.resources[req.key].metadata.resource_version {
        // Update fails because the object has a wrong rv
        Option::Some(APIError::Conflict)
    } else if req.obj.kind == K::kind() && !(
        K::rule(K::from_dynamic_object(req.obj).get_Ok_0())
        && K::transition_rule(K::from_dynamic_object(req.obj).get_Ok_0(), K::from_dynamic_object(s.resources[req.key]).get_Ok_0())
    ) {
        Option::Some(APIError::Invalid)
    } else {
        Option::None
    }
}

pub open spec fn handle_update_request(msg: Message, s: KubernetesAPIState) -> (EtcdState, Message, Option<WatchEvent>)
    recommends
        msg.content.is_update_request(),
{
    let req = msg.content.get_update_request();
    if Self::validate_update_request(req, s).is_Some() {
        let result = Result::Err(Self::validate_update_request(req, s).get_Some_0());
        let resp = form_update_resp_msg(msg, result);
        (s.resources, resp, Option::None)
    } else if Self::update_is_noop(req.obj, s.resources[req.key]) {
        // Update is a noop because there is nothing to update
        // so the resource version counter does not increase here
        let result = Result::Ok(s.resources[req.key]);
        let resp = form_update_resp_msg(msg, result);
        (s.resources, resp, Option::None)
    } else {
        // Update succeeds
        // Updates the resource version of the object
        let updated_obj = req.obj.set_namespace(req.key.namespace).set_resource_version(s.resource_version_counter);
        let result = Result::Ok(updated_obj);
        let resp = form_update_resp_msg(msg, result);
        // The cluster state is updated, so we send a notification to the built-in controllers
        let notify = modified_event(updated_obj);
        (s.resources.insert(updated_obj.object_ref(), updated_obj), resp, Option::Some(notify))
    }
}

// etcd is modeled as a centralized map that handles get/create/delete
pub open spec fn transition_by_etcd(msg: Message, s: KubernetesAPIState) -> (EtcdState, Message, Option<WatchEvent>)
    recommends
        msg.content.is_APIRequest(),
{
    match msg.content.get_APIRequest_0() {
        APIRequest::GetRequest(_) => Self::handle_get_request(msg, s),
        APIRequest::ListRequest(_) => Self::handle_list_request(msg, s),
        APIRequest::CreateRequest(_) => Self::handle_create_request(msg, s),
        APIRequest::DeleteRequest(_) => Self::handle_delete_request(msg, s),
        APIRequest::UpdateRequest(_) => Self::handle_update_request(msg, s),
    }
}

/// Collect the requests from the builtin controllers
pub open spec fn transition_by_builtin_controllers(
    event: WatchEvent, s: KubernetesAPIState, rest_id_allocator: RestIdAllocator
) -> (RestIdAllocator, Multiset<Message>) {
    // We only have spec of statefulset_controller for now
    statefulset_controller::transition_by_statefulset_controller(event, s, rest_id_allocator)
}

pub open spec fn handle_request() -> KubernetesAPIAction {
    Action {
        precondition: |input: KubernetesAPIActionInput, s: KubernetesAPIState| {
            &&& input.recv.is_Some()
            &&& input.recv.get_Some_0().content.is_APIRequest()
            // This dst check is redundant since the compound state machine has checked it
            &&& input.recv.get_Some_0().dst == HostId::KubernetesAPI
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
            let input_msg = input.recv;
            let input_rest_id_allocator = input.rest_id_allocator;

            let (etcd_state, etcd_resp, etcd_notify_o) = Self::transition_by_etcd(input_msg.get_Some_0(), s);
            let rv_counter_increment = if etcd_notify_o.is_Some() { 1 as nat } else { 0 as nat };
            let s_after_etcd_transition = KubernetesAPIState {
                resources: etcd_state,
                resource_version_counter: s.resource_version_counter + rv_counter_increment,
                ..s
            };
            if etcd_notify_o.is_Some() {
                let (rest_id_allocator_prime, controller_requests) = Self::transition_by_builtin_controllers(
                    etcd_notify_o.get_Some_0(), s_after_etcd_transition, input_rest_id_allocator
                );
                let s_prime = KubernetesAPIState {
                    ..s_after_etcd_transition
                };
                (s_prime, (Multiset::empty().insert(etcd_resp).add(controller_requests), rest_id_allocator_prime))
            } else {
                let s_prime = s_after_etcd_transition;
                (s_prime, (Multiset::singleton(etcd_resp), input_rest_id_allocator))
            }
        },
    }
}

pub open spec fn kubernetes_api() -> KubernetesAPIStateMachine {
    StateMachine {
        init: |s: KubernetesAPIState| {
            s.resources == Map::<ObjectRef, DynamicObjectView>::empty()
        },
        actions: set![Self::handle_request()],
        step_to_action: |step: KubernetesAPIStep| {
            match step {
                KubernetesAPIStep::HandleRequest => Self::handle_request(),
            }
        },
        action_input: |step: KubernetesAPIStep, input: KubernetesAPIActionInput| {
            input
        }
    }
}

}

}
