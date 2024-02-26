// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{api_server::types::*, cluster::Cluster, message::*};
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
// + Check kind-specific strategy like AllowCreateOnUpdate()
//
// + Support graceful deletion

#[verifier(inline)]
pub open spec fn unmarshallable_spec<K: CustomResourceView>(obj: DynamicObjectView) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal_spec(obj.spec).is_Ok(),
        Kind::DaemonSetKind => DaemonSetView::unmarshal_spec(obj.spec).is_Ok(),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal_spec(obj.spec).is_Ok(),
        Kind::PodKind => PodView::unmarshal_spec(obj.spec).is_Ok(),
        Kind::RoleBindingKind => RoleBindingView::unmarshal_spec(obj.spec).is_Ok(),
        Kind::RoleKind => RoleView::unmarshal_spec(obj.spec).is_Ok(),
        Kind::SecretKind => SecretView::unmarshal_spec(obj.spec).is_Ok(),
        Kind::ServiceKind => ServiceView::unmarshal_spec(obj.spec).is_Ok(),
        Kind::StatefulSetKind => StatefulSetView::unmarshal_spec(obj.spec).is_Ok(),
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal_spec(obj.spec).is_Ok(),
        Kind::CustomResourceKind => K::unmarshal_spec(obj.spec).is_Ok(),
    }
}

#[verifier(inline)]
pub open spec fn unmarshallable_status<K: CustomResourceView>(obj: DynamicObjectView) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal_status(obj.status).is_Ok(),
        Kind::DaemonSetKind => DaemonSetView::unmarshal_status(obj.status).is_Ok(),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal_status(obj.status).is_Ok(),
        Kind::PodKind => PodView::unmarshal_status(obj.status).is_Ok(),
        Kind::RoleBindingKind => RoleBindingView::unmarshal_status(obj.status).is_Ok(),
        Kind::RoleKind => RoleView::unmarshal_status(obj.status).is_Ok(),
        Kind::SecretKind => SecretView::unmarshal_status(obj.status).is_Ok(),
        Kind::ServiceKind => ServiceView::unmarshal_status(obj.status).is_Ok(),
        Kind::StatefulSetKind => StatefulSetView::unmarshal_status(obj.status).is_Ok(),
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal_status(obj.status).is_Ok(),
        Kind::CustomResourceKind => K::unmarshal_status(obj.status).is_Ok(),
    }
}

pub open spec fn unmarshallable_object<K: CustomResourceView>(obj: DynamicObjectView) -> bool {
    unmarshallable_spec::<K>(obj) && unmarshallable_status::<K>(obj)
}

pub open spec fn metadata_validity_check(obj: DynamicObjectView) -> Option<APIError> {
    if obj.metadata.owner_references.is_Some()
    && obj.metadata.owner_references.get_Some_0().len() > 1
    && obj.metadata.owner_references.get_Some_0().filter(|o: OwnerReferenceView| o.controller.is_Some() && o.controller.get_Some_0()).len() > 1 {
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

pub open spec fn valid_object<K: CustomResourceView>(obj: DynamicObjectView) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal(obj).get_Ok_0().state_validation(),
        Kind::DaemonSetKind => DaemonSetView::unmarshal(obj).get_Ok_0().state_validation(),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal(obj).get_Ok_0().state_validation(),
        Kind::PodKind => PodView::unmarshal(obj).get_Ok_0().state_validation(),
        Kind::RoleBindingKind => RoleBindingView::unmarshal(obj).get_Ok_0().state_validation(),
        Kind::RoleKind => RoleView::unmarshal(obj).get_Ok_0().state_validation(),
        Kind::SecretKind => SecretView::unmarshal(obj).get_Ok_0().state_validation(),
        Kind::ServiceKind => ServiceView::unmarshal(obj).get_Ok_0().state_validation(),
        Kind::StatefulSetKind => StatefulSetView::unmarshal(obj).get_Ok_0().state_validation(),
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal(obj).get_Ok_0().state_validation(),
        Kind::CustomResourceKind => K::unmarshal(obj).get_Ok_0().state_validation(),
    }
}

pub open spec fn object_validity_check<K: CustomResourceView>(obj: DynamicObjectView) -> Option<APIError> {
    if !valid_object::<K>(obj) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn valid_transition<K: CustomResourceView>(obj: DynamicObjectView, old_obj: DynamicObjectView) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal(obj).get_Ok_0().transition_validation(ConfigMapView::unmarshal(old_obj).get_Ok_0()),
        Kind::DaemonSetKind => DaemonSetView::unmarshal(obj).get_Ok_0().transition_validation(DaemonSetView::unmarshal(old_obj).get_Ok_0()),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal(obj).get_Ok_0().transition_validation(PersistentVolumeClaimView::unmarshal(old_obj).get_Ok_0()),
        Kind::PodKind => PodView::unmarshal(obj).get_Ok_0().transition_validation(PodView::unmarshal(old_obj).get_Ok_0()),
        Kind::RoleBindingKind => RoleBindingView::unmarshal(obj).get_Ok_0().transition_validation(RoleBindingView::unmarshal(old_obj).get_Ok_0()),
        Kind::RoleKind => RoleView::unmarshal(obj).get_Ok_0().transition_validation(RoleView::unmarshal(old_obj).get_Ok_0()),
        Kind::SecretKind => SecretView::unmarshal(obj).get_Ok_0().transition_validation(SecretView::unmarshal(old_obj).get_Ok_0()),
        Kind::ServiceKind => ServiceView::unmarshal(obj).get_Ok_0().transition_validation(ServiceView::unmarshal(old_obj).get_Ok_0()),
        Kind::StatefulSetKind => StatefulSetView::unmarshal(obj).get_Ok_0().transition_validation(StatefulSetView::unmarshal(old_obj).get_Ok_0()),
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal(obj).get_Ok_0().transition_validation(ServiceAccountView::unmarshal(old_obj).get_Ok_0()),
        Kind::CustomResourceKind => K::unmarshal(obj).get_Ok_0().transition_validation(K::unmarshal(old_obj).get_Ok_0()),
    }
}

pub open spec fn object_transition_validity_check<K: CustomResourceView>(obj: DynamicObjectView, old_obj: DynamicObjectView) -> Option<APIError> {
    if !valid_transition::<K>(obj, old_obj) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn marshalled_default_status<K: CustomResourceView>(kind: Kind) -> Value {
    match kind {
        Kind::ConfigMapKind => ConfigMapView::marshal_status(ConfigMapView::default().status()),
        Kind::DaemonSetKind => DaemonSetView::marshal_status(DaemonSetView::default().status()),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::marshal_status(PersistentVolumeClaimView::default().status()),
        Kind::PodKind => PodView::marshal_status(PodView::default().status()),
        Kind::RoleBindingKind => RoleBindingView::marshal_status(RoleBindingView::default().status()),
        Kind::RoleKind => RoleView::marshal_status(RoleView::default().status()),
        Kind::SecretKind => SecretView::marshal_status(SecretView::default().status()),
        Kind::ServiceKind => ServiceView::marshal_status(ServiceView::default().status()),
        Kind::StatefulSetKind => StatefulSetView::marshal_status(StatefulSetView::default().status()),
        Kind::ServiceAccountKind => ServiceAccountView::marshal_status(ServiceAccountView::default().status()),
        Kind::CustomResourceKind => K::marshal_status(K::default().status()),
    }
}

#[verifier(inline)]
pub open spec fn handle_get_request(req: GetRequest, s: ApiServerState) -> GetResponse {
    if !s.resources.contains_key(req.key) {
        // Get fails
        GetResponse{res: Err(APIError::ObjectNotFound)}
    } else {
        // Get succeeds
        GetResponse{res: Ok(s.resources[req.key])}
    }
}

#[verifier(inline)]
pub open spec fn handle_list_request(req: ListRequest, s: ApiServerState) -> ListResponse {
    // TODO: List should consider other fields
    let selector = |o: DynamicObjectView| {
        &&& o.object_ref().namespace == req.namespace
        &&& o.object_ref().kind == req.kind
    };
    ListResponse{res: Ok(map_to_seq(s.resources, selector))}
}

pub open spec fn create_request_admission_check<K: CustomResourceView>(req: CreateRequest, s: ApiServerState) -> Option<APIError> {
    if req.obj.metadata.name.is_None() {
        // Creation fails because the name of the provided object is not provided
        Some(APIError::Invalid)
    } else if req.obj.metadata.namespace.is_Some() && req.namespace != req.obj.metadata.namespace.get_Some_0() {
        // Creation fails because the namespace of the provided object does not match the namespace sent on the request
        Some(APIError::BadRequest)
    } else if !unmarshallable_object::<K>(req.obj) {
        // Creation fails because the provided object is not well formed
        Some(APIError::BadRequest) // TODO: should the error be BadRequest?
    } else if s.resources.contains_key(req.obj.set_namespace(req.namespace).object_ref()) {
        // Creation fails because the object already exists
        Some(APIError::ObjectAlreadyExists)
    } else {
        None
    }
}

pub open spec fn created_object_validity_check<K: CustomResourceView>(created_obj: DynamicObjectView) -> Option<APIError> {
    if metadata_validity_check(created_obj).is_Some() {
        metadata_validity_check(created_obj)
    } else if object_validity_check::<K>(created_obj).is_Some() {
        object_validity_check::<K>(created_obj)
    } else {
        None
    }
}

#[verifier(inline)]
pub open spec fn handle_create_request<K: CustomResourceView>(req: CreateRequest, s: ApiServerState) -> (ApiServerState, CreateResponse) {
    if create_request_admission_check::<K>(req, s).is_Some() {
        // Creation fails.
        (s, CreateResponse{res: Err(create_request_admission_check::<K>(req, s).get_Some_0())})
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
            status: marshalled_default_status::<K>(req.obj.kind), // Overwrite the status with the default one
        };
        if created_object_validity_check::<K>(created_obj).is_Some() {
            // Creation fails.
            (s, CreateResponse{res: Err(created_object_validity_check::<K>(created_obj).get_Some_0())})
        } else {
            // Creation succeeds.
            (ApiServerState {
                resources: s.resources.insert(created_obj.object_ref(), created_obj),
                // The object just gets created so it is not stable yet: built-in controller might update it
                stable_resources: s.stable_resources.remove(created_obj.object_ref()),
                uid_counter: s.uid_counter + 1,
                resource_version_counter: s.resource_version_counter + 1,
                ..s
            }, CreateResponse{res: Ok(created_obj)})
        }
    }
}

// Here we make a compromise when modeling the behavior of setting
// deletion timestamp to each object that is deemed to be deleted.
// The real Kubernetes' behavior uses the current timestamp as the
// deletion timestamp, but we only use an opaque string here.
// This is fine because the request handling logic we want to model
// only cares whether the object has a deletion timestamp or not.
// By using this closed deletion_timestamp() function, we make the
// modeling and proof much easier compared to modelling the real clock.
pub closed spec fn deletion_timestamp() -> StringView;

pub open spec fn handle_delete_request(req: DeleteRequest, s: ApiServerState) -> (ApiServerState, DeleteResponse) {
    if !s.resources.contains_key(req.key) {
        // Deletion fails.
        (s, DeleteResponse{res: Err(APIError::ObjectNotFound)})
    } else {
        // Deletion succeeds.
        let obj = s.resources[req.key];
        if obj.metadata.finalizers.is_Some() && obj.metadata.finalizers.get_Some_0().len() > 0 {
            // With the finalizer(s) in the object, we cannot immediately delete it from the key-value store.
            // Instead, we set the deletion timestamp of this object.
            // If the object already has a deletion timestamp, then skip.
            if obj.metadata.deletion_timestamp.is_Some() {
                (s, DeleteResponse{res: Ok(())})
            } else {
                let stamped_obj_with_new_rv = obj.set_deletion_timestamp(deletion_timestamp())
                                                    .set_resource_version(s.resource_version_counter);
                (ApiServerState {
                    // Here we use req.key, instead of stamped_obj.object_ref(), to insert to the map.
                    // This is intended because using stamped_obj.object_ref() will require us to use
                    // the invariant each_object_in_etcd_is_well_formed a lot more frequently:
                    // we need this invariant to convince Verus that the stamped_obj is well formed
                    // so the key we use to insert to the map is the same as req.key.
                    resources: s.resources.insert(req.key, stamped_obj_with_new_rv),
                    resource_version_counter: s.resource_version_counter + 1,
                    ..s
                }, DeleteResponse{res: Ok(())})
            }
        } else {
            // The object can be immediately removed from the key-value store.
            (ApiServerState {
                resources: s.resources.remove(req.key),
                resource_version_counter: s.resource_version_counter + 1,
                ..s
            }, DeleteResponse{res: Ok(())})
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

pub open spec fn update_request_admission_check_helper<K: CustomResourceView>(name: StringView, namespace: StringView, obj: DynamicObjectView, s: ApiServerState) -> Option<APIError> {
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
    } else if !unmarshallable_object::<K>(obj) {
        // Update fails because the provided object is not well formed
        // TODO: should the error be BadRequest?
        Some(APIError::BadRequest)
    } else if !s.resources.contains_key(key) {
        // Update fails because the object does not exist
        // TODO: check AllowCreateOnUpdate() to see whether to support create-on-update
        Some(APIError::ObjectNotFound)
    } else if obj.metadata.resource_version.is_None()
        && !allow_unconditional_update(key.kind) {
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

pub open spec fn update_request_admission_check<K: CustomResourceView>(req: UpdateRequest, s: ApiServerState) -> Option<APIError> {
    update_request_admission_check_helper::<K>(req.name, req.namespace, req.obj, s)
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

pub open spec fn updated_object_validity_check<K: CustomResourceView>(updated_obj: DynamicObjectView, old_obj: DynamicObjectView) -> Option<APIError> {
    if metadata_validity_check(updated_obj).is_Some() {
        metadata_validity_check(updated_obj)
    } else if metadata_transition_validity_check(updated_obj, old_obj).is_Some() {
        metadata_transition_validity_check(updated_obj, old_obj)
    } else if object_validity_check::<K>(updated_obj).is_Some() {
        object_validity_check::<K>(updated_obj)
    } else if object_transition_validity_check::<K>(updated_obj, old_obj).is_Some() {
        object_transition_validity_check::<K>(updated_obj, old_obj)
    } else {
        None
    }
}

#[verifier(inline)]
pub open spec fn handle_update_request<K: CustomResourceView>(req: UpdateRequest, s: ApiServerState) -> (ApiServerState, UpdateResponse) {
    if update_request_admission_check::<K>(req, s).is_Some() {
        // Update fails.
        (s, UpdateResponse{res: Err(update_request_admission_check::<K>(req, s).get_Some_0())})
    } else {
        let old_obj = s.resources[req.key()];
        let updated_obj = updated_object(req, old_obj);
        if updated_obj == old_obj {
            // Update is a noop because there is nothing to update
            // so the resource version counter does not increase here,
            // and the resource version of this object remains the same.
            (s, UpdateResponse{res: Ok(old_obj)})
        } else {
            // Update changes something in the object (either in spec or metadata), so we set it a newer resource version,
            // which is the current rv counter.
            let updated_obj_with_new_rv = updated_obj.set_resource_version(s.resource_version_counter);
            if updated_object_validity_check::<K>(updated_obj_with_new_rv, old_obj).is_Some() {
                // Update fails.
                (s, UpdateResponse{res: Err(updated_object_validity_check::<K>(updated_obj_with_new_rv, old_obj).get_Some_0())})
            } else {
                // Update succeeds.
                if updated_obj_with_new_rv.metadata.deletion_timestamp.is_None()
                    || (updated_obj_with_new_rv.metadata.finalizers.is_Some()
                        && updated_obj_with_new_rv.metadata.finalizers.get_Some_0().len() > 0)
                {
                    // The regular update case, where the object has no deletion timestamp set
                    // or has at least one finalizer.
                    (ApiServerState {
                        resources: s.resources.insert(req.key(), updated_obj_with_new_rv),
                        // The object just gets updated so it is not stable yet: built-in controller might update it
                        stable_resources: s.stable_resources.remove(req.key()),
                        resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                        ..s
                    }, UpdateResponse{res: Ok(updated_obj_with_new_rv)})
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
                    (ApiServerState {
                        resources: s.resources.remove(updated_obj_with_new_rv.object_ref()),
                        resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                        ..s
                    }, UpdateResponse{res: Ok(updated_obj_with_new_rv)})
                }
            }
        }
    }
}

pub open spec fn update_status_request_admission_check<K: CustomResourceView>(req: UpdateStatusRequest, s: ApiServerState) -> Option<APIError> {
    update_request_admission_check_helper::<K>(req.name, req.namespace, req.obj, s)
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
pub open spec fn handle_update_status_request<K: CustomResourceView>(req: UpdateStatusRequest, s: ApiServerState) -> (ApiServerState, UpdateStatusResponse) {
    if update_status_request_admission_check::<K>(req, s).is_Some() {
        // UpdateStatus fails.
        (s, UpdateStatusResponse{res: Err(update_status_request_admission_check::<K>(req, s).get_Some_0())})
    } else {
        let old_obj = s.resources[req.key()];
        let updated_obj = status_updated_object(req, old_obj);
        if updated_obj == old_obj {
            // UpdateStatus is a noop because there is nothing to update
            // so the resource version counter does not increase here,
            // and the resource version of this object remains the same.
            (s, UpdateStatusResponse{res: Ok(old_obj)})
        } else {
            // UpdateStatus changes something in the object (in status), so we set it a newer resource version,
            // which is the current rv counter.
            let updated_obj_with_new_rv = updated_obj.set_resource_version(s.resource_version_counter);
            if updated_object_validity_check::<K>(updated_obj_with_new_rv, old_obj).is_Some() {
                // UpdateStatus fails.
                (s, UpdateStatusResponse{res: Err(updated_object_validity_check::<K>(updated_obj_with_new_rv, old_obj).get_Some_0())})
            } else {
                // UpdateStatus succeeds.
                (ApiServerState {
                    resources: s.resources.insert(req.key(), updated_obj_with_new_rv),
                    resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                    ..s
                }, UpdateStatusResponse{res: Ok(updated_obj_with_new_rv)})
            }
        }
    }
}

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn handle_get_request_msg(msg: MsgType<E>, s: ApiServerState) -> (ApiServerState, MsgType<E>)
    recommends
        msg.content.is_get_request(),
{
    let req = msg.content.get_get_request();
    (s, Message::form_get_resp_msg(msg, handle_get_request(req, s)))
}

pub open spec fn handle_list_request_msg(msg: MsgType<E>, s: ApiServerState) -> (ApiServerState, MsgType<E>)
    recommends
        msg.content.is_list_request(),
{
    let req = msg.content.get_list_request();
    (s, Message::form_list_resp_msg(msg, handle_list_request(req, s)))
}

pub open spec fn handle_create_request_msg(msg: MsgType<E>, s: ApiServerState) -> (ApiServerState, MsgType<E>)
    recommends
        msg.content.is_create_request(),
{
    let req = msg.content.get_create_request();
    let (s_prime, resp) = handle_create_request::<K>(req, s);
    (s_prime, Message::form_create_resp_msg(msg, resp))
}

pub open spec fn handle_delete_request_msg(msg: MsgType<E>, s: ApiServerState) -> (ApiServerState, MsgType<E>)
    recommends
        msg.content.is_delete_request(),
{
    let req = msg.content.get_delete_request();
    let (s_prime, resp) = handle_delete_request(req, s);
    (s_prime, Message::form_delete_resp_msg(msg, resp))
}

pub open spec fn handle_update_request_msg(msg: MsgType<E>, s: ApiServerState) -> (ApiServerState, MsgType<E>)
    recommends
        msg.content.is_update_request(),
{
    let req = msg.content.get_update_request();
    let (s_prime, resp) = handle_update_request::<K>(req, s);
    (s_prime, Message::form_update_resp_msg(msg, resp))
}

pub open spec fn handle_update_status_request_msg(msg: MsgType<E>, s: ApiServerState) -> (ApiServerState, MsgType<E>)
    recommends
        msg.content.is_update_status_request(),
{
    let req = msg.content.get_update_status_request();
    let (s_prime, resp) = handle_update_status_request::<K>(req, s);
    (s_prime, Message::form_update_status_resp_msg(msg, resp))
}

// etcd is modeled as a centralized map that handles get/list/create/delete/update
pub open spec fn transition_by_etcd(msg: MsgType<E>, s: ApiServerState) -> (ApiServerState, MsgType<E>)
    recommends
        msg.content.is_APIRequest(),
{
    match msg.content.get_APIRequest_0() {
        APIRequest::GetRequest(_) => Self::handle_get_request_msg(msg, s),
        APIRequest::ListRequest(_) => Self::handle_list_request_msg(msg, s),
        APIRequest::CreateRequest(_) => Self::handle_create_request_msg(msg, s),
        APIRequest::DeleteRequest(_) => Self::handle_delete_request_msg(msg, s),
        APIRequest::UpdateRequest(_) => Self::handle_update_request_msg(msg, s),
        APIRequest::UpdateStatusRequest(_) => Self::handle_update_status_request_msg(msg, s),
    }
}

pub open spec fn handle_request() -> ApiServerAction<E::Input, E::Output> {
    Action {
        precondition: |input: ApiServerActionInput<E::Input, E::Output>, s: ApiServerState| {
            &&& input.recv.is_Some()
            &&& input.recv.get_Some_0().content.is_APIRequest()
            // This dst check is redundant since the compound state machine has checked it
            &&& input.recv.get_Some_0().dst == HostId::ApiServer
        },
        transition: |input: ApiServerActionInput<E::Input, E::Output>, s: ApiServerState| {
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
            (s_prime, ApiServerActionOutput {
                send: Multiset::singleton(etcd_resp)
            })
        },
    }
}

pub open spec fn kubernetes_api() -> ApiServerStateMachine<E::Input, E::Output> {
    StateMachine {
        init: |s: ApiServerState| {
            &&& s.resources == Map::<ObjectRef, DynamicObjectView>::empty()
            &&& s.stable_resources == Set::<ObjectRef>::empty()
        },
        actions: set![Self::handle_request()],
        step_to_action: |step: ApiServerStep| {
            match step {
                ApiServerStep::HandleRequest => Self::handle_request(),
            }
        },
        action_input: |step: ApiServerStep, input: ApiServerActionInput<E::Input, E::Output>| {
            input
        }
    }
}

}

}
