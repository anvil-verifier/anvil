// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{error::*, prelude::*};
use crate::kubernetes_cluster::spec::{cluster::Cluster, kubernetes_api::common::*, message::*};
use crate::pervasive_ext::string_view::*;
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
// + Support more operations like List
//
// + Check kind-specific strategy like AllowUnconditionalUpdate() and AllowCreateOnUpdate()
//
// + Support graceful deletion

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

// TODO: maybe make it a method of DynamicObjectView?
pub open spec fn spec_integrity_check(obj: DynamicObjectView) -> bool {
    &&& obj.kind == ConfigMapView::kind() ==> ConfigMapView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == DaemonSetView::kind() ==> DaemonSetView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == PersistentVolumeClaimView::kind() ==> PersistentVolumeClaimView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == PodView::kind() ==> PodView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == RoleBindingView::kind() ==> RoleBindingView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == RoleView::kind() ==> RoleView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == SecretView::kind() ==> SecretView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == ServiceView::kind() ==> ServiceView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == StatefulSetView::kind() ==> StatefulSetView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == ServiceAccountView::kind() ==> ServiceAccountView::unmarshal_spec(obj.spec).is_Ok()
    &&& obj.kind == K::kind() ==> K::unmarshal_spec(obj.spec).is_Ok()
}

pub open spec fn state_validity_check(obj: DynamicObjectView) -> bool {
    &&& obj.kind == ConfigMapView::kind() ==> ConfigMapView::unmarshal(obj).get_Ok_0().state_validation()
    &&& obj.kind == DaemonSetView::kind() ==> DaemonSetView::unmarshal(obj).get_Ok_0().state_validation()
    &&& obj.kind == PersistentVolumeClaimView::kind() ==> PersistentVolumeClaimView::unmarshal(obj).get_Ok_0().state_validation()
    &&& obj.kind == PodView::kind() ==> PodView::unmarshal(obj).get_Ok_0().state_validation()
    &&& obj.kind == RoleBindingView::kind() ==> RoleBindingView::unmarshal(obj).get_Ok_0().state_validation()
    &&& obj.kind == RoleView::kind() ==> RoleView::unmarshal(obj).get_Ok_0().state_validation()
    &&& obj.kind == SecretView::kind() ==> SecretView::unmarshal(obj).get_Ok_0().state_validation()
    &&& obj.kind == ServiceView::kind() ==> ServiceView::unmarshal(obj).get_Ok_0().state_validation()
    &&& obj.kind == StatefulSetView::kind() ==> StatefulSetView::unmarshal(obj).get_Ok_0().state_validation()
    &&& obj.kind == ServiceAccountView::kind() ==> ServiceAccountView::unmarshal(obj).get_Ok_0().state_validation()
    &&& obj.kind == K::kind() ==> K::unmarshal(obj).get_Ok_0().state_validation()
}

pub open spec fn transition_validity_check(obj: DynamicObjectView, old_obj: DynamicObjectView) -> bool {
    &&& obj.kind == ConfigMapView::kind() ==> ConfigMapView::unmarshal(obj).get_Ok_0().transition_validation(ConfigMapView::unmarshal(old_obj).get_Ok_0())
    &&& obj.kind == DaemonSetView::kind() ==> DaemonSetView::unmarshal(obj).get_Ok_0().transition_validation(DaemonSetView::unmarshal(old_obj).get_Ok_0())
    &&& obj.kind == PersistentVolumeClaimView::kind() ==> PersistentVolumeClaimView::unmarshal(obj).get_Ok_0().transition_validation(PersistentVolumeClaimView::unmarshal(old_obj).get_Ok_0())
    &&& obj.kind == PodView::kind() ==> PodView::unmarshal(obj).get_Ok_0().transition_validation(PodView::unmarshal(old_obj).get_Ok_0())
    &&& obj.kind == RoleBindingView::kind() ==> RoleBindingView::unmarshal(obj).get_Ok_0().transition_validation(RoleBindingView::unmarshal(old_obj).get_Ok_0())
    &&& obj.kind == RoleView::kind() ==> RoleView::unmarshal(obj).get_Ok_0().transition_validation(RoleView::unmarshal(old_obj).get_Ok_0())
    &&& obj.kind == SecretView::kind() ==> SecretView::unmarshal(obj).get_Ok_0().transition_validation(SecretView::unmarshal(old_obj).get_Ok_0())
    &&& obj.kind == ServiceView::kind() ==> ServiceView::unmarshal(obj).get_Ok_0().transition_validation(ServiceView::unmarshal(old_obj).get_Ok_0())
    &&& obj.kind == StatefulSetView::kind() ==> StatefulSetView::unmarshal(obj).get_Ok_0().transition_validation(StatefulSetView::unmarshal(old_obj).get_Ok_0())
    &&& obj.kind == ServiceAccountView::kind() ==> ServiceAccountView::unmarshal(obj).get_Ok_0().transition_validation(ServiceAccountView::unmarshal(old_obj).get_Ok_0())
    &&& obj.kind == K::kind() ==> K::unmarshal(obj).get_Ok_0().transition_validation(K::unmarshal(old_obj).get_Ok_0())
}

pub open spec fn handle_get_request(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
    recommends
        msg.content.is_get_request(),
{
    let req = msg.content.get_get_request();
    if !s.resources.contains_key(req.key) {
        // Get fails
        let result = Err(APIError::ObjectNotFound);
        let resp = Message::form_get_resp_msg(msg, result);
        (s, resp)
    } else {
        // Get succeeds
        let result = Ok(s.resources[req.key]);
        let resp = Message::form_get_resp_msg(msg, result);
        (s, resp)
    }
}

pub open spec fn list_query(list_req: ListRequest, s: KubernetesAPIState) -> Seq<DynamicObjectView> {
    // TODO: the returned seq should contain all the objects of the resource kind in the resources map
    Seq::empty()
}

pub open spec fn handle_list_request(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
    recommends
        msg.content.is_list_request(),
{
    let req = msg.content.get_list_request();
    let result = Ok(Self::list_query(req, s));
    let resp = Message::form_list_resp_msg(msg, result);
    (s, resp)
}

pub open spec fn validate_create_request(req: CreateRequest, s: KubernetesAPIState) -> Option<APIError> {
    if req.obj.metadata.name.is_None() {
        // Creation fails because the name of the provided object is not provided
        Some(APIError::Invalid)
    } else if req.obj.metadata.namespace.is_Some() && req.namespace != req.obj.metadata.namespace.get_Some_0() {
        // Creation fails because the namespace of the provided object does not match the namespace sent on the request
        Some(APIError::BadRequest)
    } else if !Self::spec_integrity_check(req.obj) {
        // Creation fails because the spec of the provided object is not well formed
        Some(APIError::BadRequest) // TODO: should the error be BadRequest?
    } else if s.resources.contains_key(req.obj.set_namespace(req.namespace).object_ref()) {
        // Creation fails because the object already exists
        Some(APIError::ObjectAlreadyExists)
    } else if req.obj.metadata.owner_references.is_Some()
        && req.obj.metadata.owner_references.get_Some_0().len() > 1
        && exists |i, j| #![auto] (
            i != j
            && 0 <= i < req.obj.metadata.owner_references.get_Some_0().len()
            && 0 <= j < req.obj.metadata.owner_references.get_Some_0().len()
            && req.obj.metadata.owner_references.get_Some_0()[i].is_controller_ref()
            && req.obj.metadata.owner_references.get_Some_0()[j].is_controller_ref()
        ) {
        // Creation fails because the object has multiple controller owner references
        Some(APIError::Invalid)
    } else if !Self::state_validity_check(req.obj) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn handle_create_request(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
    recommends
        msg.content.is_create_request(),
{
    let req = msg.content.get_create_request();
    if Self::validate_create_request(req, s).is_Some() {
        // Creation fails.
        let result = Err(Self::validate_create_request(req, s).get_Some_0());
        let resp = Message::form_create_resp_msg(msg, result);
        (s, resp)
    } else {
        // Creation succeeds.
        // Set the namespace, the resource_version and the uid of the created object.
        let created_obj = req.obj.set_namespace(req.namespace)
                            .set_resource_version(s.resource_version_counter)
                            .set_uid(s.uid_counter)
                            .unset_deletion_timestamp();
        let result = Ok(created_obj);
        let resp = Message::form_create_resp_msg(msg, result);
        (KubernetesAPIState {
            resources: s.resources.insert(created_obj.object_ref(), created_obj),
            uid_counter: s.uid_counter + 1,
            resource_version_counter: s.resource_version_counter + 1,
            ..s
        }, resp)
    }
}

pub closed spec fn deletion_timestamp() -> StringView;

pub open spec fn handle_delete_request(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
    recommends
        msg.content.is_delete_request(),
{
    let req = msg.content.get_delete_request();
    if !s.resources.contains_key(req.key) {
        // Deletion fails.
        let result = Err(APIError::ObjectNotFound);
        let resp = Message::form_delete_resp_msg(msg, result);
        (s, resp)
    } else {
        // Deletion succeeds.
        let obj = s.resources[req.key];
        if obj.metadata.finalizers.is_Some() && obj.metadata.finalizers.get_Some_0().len() > 0 {
            // With the finalizer(s) in the object, we cannot immediately delete it from the key-value store.
            // Instead, we set the deletion timestamp of this object.
            let stamped_obj = obj.set_deletion_timestamp(Self::deletion_timestamp());
            if stamped_obj == obj {
                let result = Ok(stamped_obj);
                let resp = Message::form_delete_resp_msg(msg, result);
                (s, resp)
            } else {
                let stamped_obj_with_new_rv = stamped_obj.set_resource_version(s.resource_version_counter);
                let result = Ok(stamped_obj_with_new_rv);
                let resp = Message::form_delete_resp_msg(msg, result);
                (KubernetesAPIState {
                    // Here we use req.key, instead of stamped_obj.object_ref(), to insert to the map.
                    // This is intended because using stamped_obj.object_ref() will require us to use
                    // the invariant each_object_in_etcd_is_well_formed a lot more frequently:
                    // we need this invariant to convince Verus that the stamped_obj is well formed
                    // so the key we use to insert to the map is the same as req.key.
                    resources: s.resources.insert(req.key, stamped_obj_with_new_rv),
                    resource_version_counter: s.resource_version_counter + 1,
                    ..s
                }, resp)
            }

        } else {
            // The object can be immediately removed from the key-value store.
            let result = Ok(obj);
            let resp = Message::form_delete_resp_msg(msg, result);
            (KubernetesAPIState {
                resources: s.resources.remove(req.key),
                resource_version_counter: s.resource_version_counter + 1,
                ..s
            }, resp)
        }
    }
}

// Unconditional update means one can update the object without providing a resource version.
// For all the supported kinds, unconditional update is disallowed for CustomResource only.
// Note that if the resource version is provided, it has to be the correct one.
pub open spec fn allow_unconditional_update(kind: Kind) -> bool {
    match kind {
        Kind::CustomResourceKind => false,
        _ => true,
    }
}

pub open spec fn validate_update_request(req: UpdateRequest, s: KubernetesAPIState) -> Option<APIError> {
    if req.obj.metadata.name.is_None() {
        // Update fails because the name of the object is not provided
        Some(APIError::BadRequest)
    } else if req.name != req.obj.metadata.name.get_Some_0() {
        // Update fails because the name of the provided object
        // does not match the name sent on the request
        Some(APIError::BadRequest)
    } else if req.obj.metadata.namespace.is_Some()
        && req.namespace != req.obj.metadata.namespace.get_Some_0() {
        // Update fails because the namespace of the provided object
        // does not match the namespace sent on the request
        Some(APIError::BadRequest)
    } else if !Self::spec_integrity_check(req.obj) {
        // Update fails because the spec of the provided object is not well formed
        // TODO: should the error be BadRequest?
        Some(APIError::BadRequest)
    } else if !s.resources.contains_key(req.key()) {
        // Update fails because the object does not exist
        // TODO: check AllowCreateOnUpdate() to see whether to support create-on-update
        Some(APIError::ObjectNotFound)
    } else if req.obj.metadata.resource_version.is_None()
        && !Self::allow_unconditional_update(req.key().kind) {
        // Update fails because the object does not provide a rv and unconditional update is not supported
        Some(APIError::Invalid)
    } else if req.obj.metadata.resource_version.is_Some()
        && req.obj.metadata.resource_version != s.resources[req.key()].metadata.resource_version {
        // Update fails because the object has a wrong rv
        Some(APIError::Conflict)
    } else if req.obj.metadata.uid.is_Some()
        && req.obj.metadata.uid != s.resources[req.key()].metadata.uid {
        // Update fails because the object has a wrong uid
        // TODO: double check the Error type
        Some(APIError::InternalError)
    } else if req.obj.metadata.owner_references.is_Some()
        && req.obj.metadata.owner_references.get_Some_0().len() > 1
        && exists |i, j| #![auto] (
            i != j
            && 0 <= i < req.obj.metadata.owner_references.get_Some_0().len()
            && 0 <= j < req.obj.metadata.owner_references.get_Some_0().len()
            && req.obj.metadata.owner_references.get_Some_0()[i].is_controller_ref()
            && req.obj.metadata.owner_references.get_Some_0()[j].is_controller_ref()
        ) {
        // Update fails because the object has multiple controller owner references
        Some(APIError::Invalid)
    } else if s.resources[req.key()].metadata.deletion_timestamp.is_Some()
        && req.obj.metadata.finalizers.is_Some() // Short circuit: we don't need to reason about the set difference if the finalizers is None
        && !req.obj.metadata.finalizers_as_set().subset_of(s.resources[req.key()].metadata.finalizers_as_set()) {
        // Update fails because the object is marked to be deleted but the update tries to add more finalizers
        Some(APIError::Forbidden)
    } else if !Self::state_validity_check(req.obj) {
        Some(APIError::Invalid)
    } else if !Self::transition_validity_check(req.obj, s.resources[req.key()]) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn updated_object(req: UpdateRequest, s: KubernetesAPIState) -> DynamicObjectView {
    let old_obj = s.resources[req.key()];
    let updated_obj = req.obj.set_namespace(req.namespace)
                        // Update cannot change the rv; if rv is provided and inconsistent, validation fails.
                        .set_resource_version(old_obj.metadata.resource_version.get_Some_0())
                        // Update cannot change the uid; if uid is provided and inconsistent, validation fails.
                        .set_uid(old_obj.metadata.uid.get_Some_0())
                        // Update cannot change the deletion timestamp.
                        .overwrite_deletion_timestamp(old_obj.metadata.deletion_timestamp);
    // TODO: enforce that finalizer cannot be added if deletion timestamp is set.
    // TODO: status should also be ignored here, after we support it.
    updated_obj
}

pub open spec fn handle_update_request(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
    recommends
        msg.content.is_update_request(),
{
    let req = msg.content.get_update_request();
    if Self::validate_update_request(req, s).is_Some() {
        // Update fails.
        let result = Err(Self::validate_update_request(req, s).get_Some_0());
        let resp = Message::form_update_resp_msg(msg, result);
        (s, resp)
    } else {
        // Update succeeds.
        let updated_obj = Self::updated_object(req, s);
        if updated_obj == s.resources[req.key()] {
            // Update is a noop because there is nothing to update
            // so the resource version counter does not increase here,
            // and the resource version of this object remains the same.
            let result = Ok(s.resources[req.key()]);
            let resp = Message::form_update_resp_msg(msg, result);
            (s, resp)
        } else {
            // Update changes something in the object (either in spec or metadata), so we set it a newer resource version,
            // which is the current rv counter.
            let updated_obj_with_new_rv = updated_obj.set_resource_version(s.resource_version_counter);
            let result = Ok(updated_obj_with_new_rv);
            let resp = Message::form_update_resp_msg(msg, result);
            if updated_obj_with_new_rv.metadata.deletion_timestamp.is_None()
                || (updated_obj_with_new_rv.metadata.finalizers.is_Some()
                    && updated_obj_with_new_rv.metadata.finalizers.get_Some_0().len() > 0) {
                // The regular update case, where the object has no deletion timestamp set
                // or has at least one finalizer.
                (KubernetesAPIState {
                    resources: s.resources.insert(updated_obj_with_new_rv.object_ref(), updated_obj_with_new_rv),
                    resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                    ..s
                }, resp)
            } else {
                // The delete-during-update case, where the update removes the finalizer from
                // the object that has a deletion timestamp, so the object needs to be deleted now.
                // NOTE: in the actual implementation, when handling an update request,
                // the API server first applies the update to the object in the key-value store,
                // then checks whether object can be deleted.
                // If so, it continues to delete the object from the key-value store before replying
                // to the update request.
                // This means that there is a super short window where the object has been updated in the store
                // (with a deletion timestamp and without any finalizer), but has not been deleted yet.
                // We choose not to model this short window and instead merge the update and delete into one atomic action
                // because the controller that issues the update request in an non-async manner will not observe
                // this intermediate state within the short window.
                // When the update request returns, the object has been deleted anyway.
                (KubernetesAPIState {
                    resources: s.resources.remove(updated_obj_with_new_rv.object_ref()),
                    resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                    ..s
                }, resp)
            }
        }
    }
}

// etcd is modeled as a centralized map that handles get/list/create/delete/update
pub open spec fn transition_by_etcd(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
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

pub open spec fn handle_request() -> KubernetesAPIAction<E::Input, E::Output> {
    Action {
        precondition: |input: KubernetesAPIActionInput<E::Input, E::Output>, s: KubernetesAPIState| {
            &&& input.recv.is_Some()
            &&& input.recv.get_Some_0().content.is_APIRequest()
            // This dst check is redundant since the compound state machine has checked it
            &&& input.recv.get_Some_0().dst == HostId::KubernetesAPI
        },
        transition: |input: KubernetesAPIActionInput<E::Input, E::Output>, s: KubernetesAPIState| {
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
            // Here we simplify step (1) ~ (5) by omitting the process that state changes are streamed
            // to built-in controllers and activate their reconciliation.
            // Built-in controllers will be specified as actions of the top level cluster state machine.
            let (s_prime, etcd_resp) = Self::transition_by_etcd(input.recv.get_Some_0(), s);
            (s_prime, KubernetesAPIActionOutput {
                send: Multiset::singleton(etcd_resp)
            })
        },
    }
}

pub open spec fn kubernetes_api() -> KubernetesAPIStateMachine<E::Input, E::Output> {
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
        action_input: |step: KubernetesAPIStep, input: KubernetesAPIActionInput<E::Input, E::Output>| {
            input
        }
    }
}

}

}
