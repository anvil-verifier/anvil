// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::Cluster, kubernetes_api::common::*, message::*};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{multiset::*, prelude::*};

verus! {

// TODO:
// + Need more validation checks.
//   For example, RoleBinding's roleRef is immutable: https://kubernetes.io/docs/reference/access-authn-authz/rbac/#clusterrolebinding-example
//
// + Create and update should ignore the status fields provided by the object
//
// + Check kind-specific strategy like AllowUnconditionalUpdate() and AllowCreateOnUpdate()
//
// + Support graceful deletion

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

// TODO: maybe make it a method of DynamicObjectView?
// TODO: we should just use pattern matching here; but a problem is that K::kind() is not guaranteed to be CustomResourceKind
pub open spec fn unmarshallable_object(obj: DynamicObjectView) -> bool {
    if obj.kind == ConfigMapView::kind() { ConfigMapView::unmarshal_spec(obj.spec).is_Ok() && ConfigMapView::unmarshal_status(obj.status).is_Ok() }
    else if obj.kind == DaemonSetView::kind() { DaemonSetView::unmarshal_spec(obj.spec).is_Ok() && DaemonSetView::unmarshal_status(obj.status).is_Ok() }
    else if obj.kind == PersistentVolumeClaimView::kind() { PersistentVolumeClaimView::unmarshal_spec(obj.spec).is_Ok() && PersistentVolumeClaimView::unmarshal_status(obj.status).is_Ok() }
    else if obj.kind == PodView::kind() { PodView::unmarshal_spec(obj.spec).is_Ok() && PodView::unmarshal_status(obj.status).is_Ok() }
    else if obj.kind == RoleBindingView::kind() { RoleBindingView::unmarshal_spec(obj.spec).is_Ok() && RoleBindingView::unmarshal_status(obj.status).is_Ok() }
    else if obj.kind == RoleView::kind() { RoleView::unmarshal_spec(obj.spec).is_Ok() && RoleView::unmarshal_status(obj.status).is_Ok() }
    else if obj.kind == SecretView::kind() { SecretView::unmarshal_spec(obj.spec).is_Ok() && SecretView::unmarshal_status(obj.status).is_Ok() }
    else if obj.kind == ServiceView::kind() { ServiceView::unmarshal_spec(obj.spec).is_Ok() && ServiceView::unmarshal_status(obj.status).is_Ok() }
    else if obj.kind == StatefulSetView::kind() { StatefulSetView::unmarshal_spec(obj.spec).is_Ok() && StatefulSetView::unmarshal_status(obj.status).is_Ok() }
    else if obj.kind == ServiceAccountView::kind() { ServiceAccountView::unmarshal_spec(obj.spec).is_Ok() && ServiceAccountView::unmarshal_status(obj.status).is_Ok() }
    else if obj.kind == K::kind() { K::unmarshal_spec(obj.spec).is_Ok() && K::unmarshal_status(obj.status).is_Ok() }
    else { true }
}

pub open spec fn metadata_validity_check(obj: DynamicObjectView) -> Option<APIError> {
    if obj.metadata.owner_references.is_Some()
    && obj.metadata.owner_references.get_Some_0().len() > 1
    && obj.metadata.owner_references.get_Some_0().filter(|o: OwnerReferenceView| o.is_controller_ref()).len() >= 2 {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn metadata_transition_validity_check(obj: DynamicObjectView, old_obj: DynamicObjectView) -> Option<APIError> {
    if old_obj.metadata.deletion_timestamp.is_Some()
    && obj.metadata.finalizers.is_Some() // Short circuit: we don't need to reason about the set difference if the finalizers is None
    && !obj.metadata.finalizers_as_set().subset_of(old_obj.metadata.finalizers_as_set()) {
        Some(APIError::Forbidden)
    } else {
        None
    }
}

pub open spec fn valid_object(obj: DynamicObjectView) -> bool {
    if obj.kind == ConfigMapView::kind() { ConfigMapView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == DaemonSetView::kind() { DaemonSetView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == PersistentVolumeClaimView::kind() { PersistentVolumeClaimView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == PodView::kind() { PodView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == RoleBindingView::kind() { RoleBindingView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == RoleView::kind() { RoleView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == SecretView::kind() { SecretView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == ServiceView::kind() { ServiceView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == StatefulSetView::kind() { StatefulSetView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == ServiceAccountView::kind() { ServiceAccountView::unmarshal(obj).get_Ok_0().state_validation() }
    else if obj.kind == K::kind() { K::unmarshal(obj).get_Ok_0().state_validation() }
    else { true }
}

pub open spec fn object_validity_check(obj: DynamicObjectView) -> Option<APIError> {
    if !Self::valid_object(obj) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn valid_transition(obj: DynamicObjectView, old_obj: DynamicObjectView) -> bool {
    if obj.kind == ConfigMapView::kind() { ConfigMapView::unmarshal(obj).get_Ok_0().transition_validation(ConfigMapView::unmarshal(old_obj).get_Ok_0()) }
    else if obj.kind == DaemonSetView::kind() { DaemonSetView::unmarshal(obj).get_Ok_0().transition_validation(DaemonSetView::unmarshal(old_obj).get_Ok_0()) }
    else if obj.kind == PersistentVolumeClaimView::kind() { PersistentVolumeClaimView::unmarshal(obj).get_Ok_0().transition_validation(PersistentVolumeClaimView::unmarshal(old_obj).get_Ok_0()) }
    else if obj.kind == PodView::kind() { PodView::unmarshal(obj).get_Ok_0().transition_validation(PodView::unmarshal(old_obj).get_Ok_0()) }
    else if obj.kind == RoleBindingView::kind() { RoleBindingView::unmarshal(obj).get_Ok_0().transition_validation(RoleBindingView::unmarshal(old_obj).get_Ok_0()) }
    else if obj.kind == RoleView::kind() { RoleView::unmarshal(obj).get_Ok_0().transition_validation(RoleView::unmarshal(old_obj).get_Ok_0()) }
    else if obj.kind == SecretView::kind() { SecretView::unmarshal(obj).get_Ok_0().transition_validation(SecretView::unmarshal(old_obj).get_Ok_0()) }
    else if obj.kind == ServiceView::kind() { ServiceView::unmarshal(obj).get_Ok_0().transition_validation(ServiceView::unmarshal(old_obj).get_Ok_0()) }
    else if obj.kind == StatefulSetView::kind() { StatefulSetView::unmarshal(obj).get_Ok_0().transition_validation(StatefulSetView::unmarshal(old_obj).get_Ok_0()) }
    else if obj.kind == ServiceAccountView::kind() { ServiceAccountView::unmarshal(obj).get_Ok_0().transition_validation(ServiceAccountView::unmarshal(old_obj).get_Ok_0()) }
    else if obj.kind == K::kind() { K::unmarshal(obj).get_Ok_0().transition_validation(K::unmarshal(old_obj).get_Ok_0()) }
    else { true }
}

pub open spec fn object_transition_validity_check(obj: DynamicObjectView, old_obj: DynamicObjectView) -> Option<APIError> {
    if !Self::valid_transition(obj, old_obj) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn marshalled_default_status(obj: DynamicObjectView) -> Value {
    if obj.kind == ConfigMapView::kind() { ConfigMapView::marshal_status(ConfigMapView::default().status()) }
    else if obj.kind == DaemonSetView::kind() { DaemonSetView::marshal_status(DaemonSetView::default().status()) }
    else if obj.kind == PersistentVolumeClaimView::kind() { PersistentVolumeClaimView::marshal_status(PersistentVolumeClaimView::default().status()) }
    else if obj.kind == PodView::kind() { PodView::marshal_status(PodView::default().status()) }
    else if obj.kind == RoleBindingView::kind() { RoleBindingView::marshal_status(RoleBindingView::default().status()) }
    else if obj.kind == RoleView::kind() { RoleView::marshal_status(RoleView::default().status()) }
    else if obj.kind == SecretView::kind() { SecretView::marshal_status(SecretView::default().status()) }
    else if obj.kind == ServiceView::kind() { ServiceView::marshal_status(ServiceView::default().status()) }
    else if obj.kind == StatefulSetView::kind() { StatefulSetView::marshal_status(StatefulSetView::default().status()) }
    else if obj.kind == ServiceAccountView::kind() { ServiceAccountView::marshal_status(ServiceAccountView::default().status()) }
    else if obj.kind == K::kind() { K::marshal_status(K::default().status()) }
    else { arbitrary() }
}

#[verifier(inline)]
pub open spec fn handle_get_request_inner(req: GetRequest, s: KubernetesAPIState) -> Result<DynamicObjectView, APIError> {
    if !s.resources.contains_key(req.key) {
        // Get fails
        let result = Err(APIError::ObjectNotFound);
        result
    } else {
        // Get succeeds
        let result = Ok(s.resources[req.key]);
        result
    }
}

pub open spec fn handle_get_request(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
    recommends
        msg.content.is_get_request(),
{
    let req = msg.content.get_get_request();
    (s, Message::form_get_resp_msg(msg, Self::handle_get_request_inner(req, s)))
}

#[verifier(inline)]
pub open spec fn handle_list_request_inner(req: ListRequest, s: KubernetesAPIState) -> Result<Seq<DynamicObjectView>, APIError> {
    // TODO: List should consider other fields
    let selector = |o: DynamicObjectView| {
        &&& o.object_ref().namespace == req.namespace
        &&& o.object_ref().kind == req.kind
    };
    Ok(map_to_seq(s.resources, selector))
}

pub open spec fn handle_list_request(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
    recommends
        msg.content.is_list_request(),
{
    let req = msg.content.get_list_request();
    (s, Message::form_list_resp_msg(msg, Self::handle_list_request_inner(req, s)))
}

pub open spec fn create_request_admission_check(req: CreateRequest, s: KubernetesAPIState) -> Option<APIError> {
    if req.obj.metadata.name.is_None() {
        // Creation fails because the name of the provided object is not provided
        Some(APIError::Invalid)
    } else if req.obj.metadata.namespace.is_Some() && req.namespace != req.obj.metadata.namespace.get_Some_0() {
        // Creation fails because the namespace of the provided object does not match the namespace sent on the request
        Some(APIError::BadRequest)
    } else if !Self::unmarshallable_object(req.obj) {
        // Creation fails because the provided object is not well formed
        Some(APIError::BadRequest) // TODO: should the error be BadRequest?
    } else if s.resources.contains_key(req.obj.set_namespace(req.namespace).object_ref()) {
        // Creation fails because the object already exists
        Some(APIError::ObjectAlreadyExists)
    } else {
        None
    }
}

pub open spec fn created_object_validity_check(created_obj: DynamicObjectView) -> Option<APIError> {
    if Self::metadata_validity_check(created_obj).is_Some() {
        Self::metadata_validity_check(created_obj)
    } else if Self::object_validity_check(created_obj).is_Some() {
        Self::object_validity_check(created_obj)
    } else {
        None
    }
}

#[verifier(inline)]
pub open spec fn handle_create_request_inner(req: CreateRequest, s: KubernetesAPIState) -> (KubernetesAPIState, Result<DynamicObjectView, APIError>) {
    if Self::create_request_admission_check(req, s).is_Some() {
        // Creation fails.
        (s, Err(Self::create_request_admission_check(req, s).get_Some_0()))
    } else {
        let created_obj = DynamicObjectView {
            kind: req.obj.kind,
            metadata: ObjectMetaView {
                namespace: Some(req.namespace), // Set namespace for new object
                resource_version: Some(s.resource_version_counter), // Set rv for new object
                uid: Some(s.uid_counter), // Set uid for new object
                deletion_timestamp: None, // Unset deletion timestamp for new object
                ..req.obj.metadata
            },
            spec: req.obj.spec,
            status: Self::marshalled_default_status(req.obj), // Overwrite the status with the default one
        };
        if Self::created_object_validity_check(created_obj).is_Some() {
            // Creation fails.
            (s, Err(Self::created_object_validity_check(created_obj).get_Some_0()))
        } else {
            // Creation succeeds.
            (KubernetesAPIState {
                resources: s.resources.insert(created_obj.object_ref(), created_obj),
                // The object just gets created so it is not stable yet: built-in controller might update it
                stable_resources: s.stable_resources.remove(created_obj.object_ref()),
                uid_counter: s.uid_counter + 1,
                resource_version_counter: s.resource_version_counter + 1,
                ..s
            }, Ok(created_obj))
        }
    }
}

pub open spec fn handle_create_request(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
    recommends
        msg.content.is_create_request(),
{
    let req = msg.content.get_create_request();
    let (s_prime, result) = Self::handle_create_request_inner(req, s);
    (s_prime, Message::form_create_resp_msg(msg, result))
}

pub closed spec fn deletion_timestamp() -> StringView;

pub open spec fn handle_delete_request_inner(req: DeleteRequest, s: KubernetesAPIState) -> (KubernetesAPIState, Result<(), APIError>) {
    if !s.resources.contains_key(req.key) {
        // Deletion fails.
        (s, Err(APIError::ObjectNotFound))
    } else {
        // Deletion succeeds.
        let obj = s.resources[req.key];
        if obj.metadata.finalizers.is_Some() && obj.metadata.finalizers.get_Some_0().len() > 0 {
            // With the finalizer(s) in the object, we cannot immediately delete it from the key-value store.
            // Instead, we set the deletion timestamp of this object.
            let stamped_obj = obj.set_deletion_timestamp(Self::deletion_timestamp());
            if stamped_obj == obj {
                (s, Ok(()))
            } else {
                let stamped_obj_with_new_rv = stamped_obj.set_resource_version(s.resource_version_counter);
                (KubernetesAPIState {
                    // Here we use req.key, instead of stamped_obj.object_ref(), to insert to the map.
                    // This is intended because using stamped_obj.object_ref() will require us to use
                    // the invariant each_object_in_etcd_is_well_formed a lot more frequently:
                    // we need this invariant to convince Verus that the stamped_obj is well formed
                    // so the key we use to insert to the map is the same as req.key.
                    resources: s.resources.insert(req.key, stamped_obj_with_new_rv),
                    resource_version_counter: s.resource_version_counter + 1,
                    ..s
                }, Ok(()))
            }
        } else {
            // The object can be immediately removed from the key-value store.
            (KubernetesAPIState {
                resources: s.resources.remove(req.key),
                resource_version_counter: s.resource_version_counter + 1,
                ..s
            }, Ok(()))
        }
    }
}

pub open spec fn handle_delete_request(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
    recommends
        msg.content.is_delete_request(),
{
    let req = msg.content.get_delete_request();
    let (s_prime, result) = Self::handle_delete_request_inner(req, s);
    (s_prime, Message::form_delete_resp_msg(msg, result))
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

pub open spec fn update_request_admission_check_helper(name: StringView, namespace: StringView, obj: DynamicObjectView, s: KubernetesAPIState) -> Option<APIError> {
    let key = ObjectRef {
        kind: obj.kind,
        namespace: namespace,
        name: name,
    };
    if obj.metadata.name.is_None() {
        // Update fails because the name of the object is not provided
        Some(APIError::BadRequest)
    } else if name != obj.metadata.name.get_Some_0() {
        // Update fails because the name of the provided object
        // does not match the name sent on the request
        Some(APIError::BadRequest)
    } else if obj.metadata.namespace.is_Some()
        && namespace != obj.metadata.namespace.get_Some_0() {
        // Update fails because the namespace of the provided object
        // does not match the namespace sent on the request
        Some(APIError::BadRequest)
    } else if !Self::unmarshallable_object(obj) {
        // Update fails because the provided object is not well formed
        // TODO: should the error be BadRequest?
        Some(APIError::BadRequest)
    } else if !s.resources.contains_key(key) {
        // Update fails because the object does not exist
        // TODO: check AllowCreateOnUpdate() to see whether to support create-on-update
        Some(APIError::ObjectNotFound)
    } else if obj.metadata.resource_version.is_None()
        && !Self::allow_unconditional_update(key.kind) {
        // Update fails because the object does not provide a rv and unconditional update is not supported
        Some(APIError::Invalid)
    } else if obj.metadata.resource_version.is_Some()
        && obj.metadata.resource_version != s.resources[key].metadata.resource_version {
        // Update fails because the object has a wrong rv
        Some(APIError::Conflict)
    } else if obj.metadata.uid.is_Some()
        && obj.metadata.uid != s.resources[key].metadata.uid {
        // Update fails because the object has a wrong uid
        // TODO: double check the Error type
        Some(APIError::InternalError)
    } else {
        None
    }
}

pub open spec fn update_request_admission_check(req: UpdateRequest, s: KubernetesAPIState) -> Option<APIError> {
    Self::update_request_admission_check_helper(req.name, req.namespace, req.obj, s)
}

pub open spec fn updated_object(req: UpdateRequest, old_obj: DynamicObjectView) -> DynamicObjectView {
    let updated_obj = DynamicObjectView {
        kind: req.obj.kind,
        metadata: ObjectMetaView {
            namespace: Some(req.namespace), // Overwrite namespace since it might not be provided
            resource_version: old_obj.metadata.resource_version, // Overwrite rv since it might not be provided
            uid: old_obj.metadata.uid, // Overwrite uid since it might not be provided
            deletion_timestamp: old_obj.metadata.deletion_timestamp, // Ignore any change to deletion_timestamp
            ..req.obj.metadata
        },
        spec: req.obj.spec,
        status: old_obj.status, // Ignore any change to status
    };
    updated_obj
}

pub open spec fn updated_object_validity_check(updated_obj: DynamicObjectView, old_obj: DynamicObjectView) -> Option<APIError> {
    if Self::metadata_validity_check(updated_obj).is_Some() {
        Self::metadata_validity_check(updated_obj)
    } else if Self::metadata_transition_validity_check(updated_obj, old_obj).is_Some() {
        Self::metadata_transition_validity_check(updated_obj, old_obj)
    } else if Self::object_validity_check(updated_obj).is_Some() {
        Self::object_validity_check(updated_obj)
    } else if Self::object_transition_validity_check(updated_obj, old_obj).is_Some() {
        Self::object_transition_validity_check(updated_obj, old_obj)
    } else {
        None
    }
}

#[verifier(inline)]
pub open spec fn handle_update_request_inner(req: UpdateRequest, s: KubernetesAPIState) -> (KubernetesAPIState, Result<DynamicObjectView, APIError>) {
    if Self::update_request_admission_check(req, s).is_Some() {
        // Update fails.
        (s, Err(Self::update_request_admission_check(req, s).get_Some_0()))
    } else {
        let old_obj = s.resources[req.key()];
        let updated_obj = Self::updated_object(req, old_obj);
        if updated_obj == old_obj {
            // Update is a noop because there is nothing to update
            // so the resource version counter does not increase here,
            // and the resource version of this object remains the same.
            (s, Ok(old_obj))
        } else {
            // Update changes something in the object (either in spec or metadata), so we set it a newer resource version,
            // which is the current rv counter.
            let updated_obj_with_new_rv = updated_obj.set_resource_version(s.resource_version_counter);
            if Self::updated_object_validity_check(updated_obj_with_new_rv, old_obj).is_Some() {
                // Update fails.
                (s, Err(Self::updated_object_validity_check(updated_obj_with_new_rv, old_obj).get_Some_0()))
            } else {
                // Update succeeds.
                if updated_obj_with_new_rv.metadata.deletion_timestamp.is_None()
                    || (updated_obj_with_new_rv.metadata.finalizers.is_Some()
                        && updated_obj_with_new_rv.metadata.finalizers.get_Some_0().len() > 0) {
                    // The regular update case, where the object has no deletion timestamp set
                    // or has at least one finalizer.
                    (KubernetesAPIState {
                        resources: s.resources.insert(req.key(), updated_obj_with_new_rv),
                        // The object just gets updated so it is not stable yet: built-in controller might update it
                        stable_resources: s.stable_resources.remove(req.key()),
                        resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                        ..s
                    }, Ok(updated_obj_with_new_rv))
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
                    }, Ok(updated_obj_with_new_rv))
                }
            }
        }
    }
}

pub open spec fn handle_update_request(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
    recommends
        msg.content.is_update_request(),
{
    let req = msg.content.get_update_request();
    let (s_prime, result) = Self::handle_update_request_inner(req, s);
    (s_prime, Message::form_update_resp_msg(msg, result))
}

pub open spec fn update_status_request_admission_check(req: UpdateStatusRequest, s: KubernetesAPIState) -> Option<APIError> {
    Self::update_request_admission_check_helper(req.name, req.namespace, req.obj, s)
}

pub open spec fn status_updated_object(req: UpdateStatusRequest, old_obj: DynamicObjectView) -> DynamicObjectView {
    let status_updated_object = DynamicObjectView {
        kind: req.obj.kind,
        metadata: old_obj.metadata, // Ignore any change to metadata
        spec: old_obj.spec, // Ignore any change to spec
        status: req.obj.status,
    };
    status_updated_object
}

#[verifier(inline)]
pub open spec fn handle_update_status_request_inner(req: UpdateStatusRequest, s: KubernetesAPIState) -> (KubernetesAPIState, Result<DynamicObjectView, APIError>) {
    if Self::update_status_request_admission_check(req, s).is_Some() {
        // UpdateStatus fails.
        (s, Err(Self::update_status_request_admission_check(req, s).get_Some_0()))
    } else {
        let old_obj = s.resources[req.key()];
        let updated_obj = Self::status_updated_object(req, old_obj);
        if updated_obj == old_obj {
            // UpdateStatus is a noop because there is nothing to update
            // so the resource version counter does not increase here,
            // and the resource version of this object remains the same.
            (s, Ok(old_obj))
        } else {
            // UpdateStatus changes something in the object (in status), so we set it a newer resource version,
            // which is the current rv counter.
            let updated_obj_with_new_rv = updated_obj.set_resource_version(s.resource_version_counter);
            if Self::updated_object_validity_check(updated_obj_with_new_rv, old_obj).is_Some() {
                // UpdateStatus fails.
                (s, Err(Self::updated_object_validity_check(updated_obj_with_new_rv, old_obj).get_Some_0()))
            } else {
                // UpdateStatus succeeds.
                (KubernetesAPIState {
                    resources: s.resources.insert(req.key(), updated_obj_with_new_rv),
                    resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                    ..s
                }, Ok(updated_obj_with_new_rv))
            }
        }
    }
}

pub open spec fn handle_update_status_request(msg: MsgType<E>, s: KubernetesAPIState) -> (KubernetesAPIState, MsgType<E>)
    recommends
        msg.content.is_update_status_request(),
{
    let req = msg.content.get_update_status_request();
    let (s_prime, result) = Self::handle_update_status_request_inner(req, s);
    (s_prime, Message::form_update_status_resp_msg(msg, result))
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
        APIRequest::UpdateStatusRequest(_) => Self::handle_update_status_request(msg, s),
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
            &&& s.resources == Map::<ObjectRef, DynamicObjectView>::empty()
            &&& s.stable_resources == Set::<ObjectRef>::empty()
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
