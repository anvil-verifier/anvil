// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::executable_model::{
    api_server_state::ApiServerState, common::*, object_map::ObjectMap,
    object_ref_set::ObjectRefSet,
};
use crate::kubernetes_api_objects::{error::*, exec::prelude::*, spec::prelude::*};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine as model, api_server::types as model_types,
};
use vstd::{multiset::*, prelude::*};

verus! {

// The ExecutableApiServerModel is an executable version of the spec-level ApiServerModel
// defined in crate::kubernetes_cluster::spec::api_server.
// The main purpose of creating this exec model is to validate the trusted ApiServerModel
// which our verification depends on.
// The validation is done in two steps: (1) we prove ExecutableApiServerModel conforms to the ApiServerModel,
// and (2) we run conformance tests by comparing the external behavior of ExecutableApiServerModel and the real
// Kubernetes implementation (in a kind cluster).
// The conformance tests can be found in crate::conformance_tests.
pub struct ExecutableApiServerModel<K> where K: View + CustomResource, K::V: CustomResourceView {
    k: K,
}

pub struct ExecutableApiServerState {
    pub resources: StoredState,
}

pub type SimpleExecutableApiServerModel = ExecutableApiServerModel<SimpleCR>;

impl <K> ExecutableApiServerModel<K> where K: View + CustomResource, K::V: CustomResourceView {

#[verifier(external_body)]
fn unmarshallable_object(obj: &DynamicObject) -> (b: bool)
    ensures b == model::unmarshallable_object::<K::V>(obj@),
{ true }

fn metadata_validity_check(obj: &DynamicObject) -> (ret: Option<APIError>)
    ensures ret == model::metadata_validity_check(obj@)
{
    if obj.metadata().owner_references().is_some()
    && obj.metadata().owner_references().unwrap().len() > 1
    && filter_controller_references(obj.metadata().owner_references().unwrap()).len() > 1 {
        Some(APIError::Invalid)
    } else {
        None
    }
}

fn metadata_transition_validity_check(obj: &DynamicObject, old_obj: &DynamicObject) -> (ret: Option<APIError>)
    ensures ret == model::metadata_transition_validity_check(obj@, old_obj@)
{
    if old_obj.metadata().has_deletion_timestamp()
    && obj.metadata().finalizers().is_some()
    && !obj.metadata().finalizers_as_set().subset_of(&old_obj.metadata().finalizers_as_set()) {
        Some(APIError::Forbidden)
    } else {
        None
    }
}

fn valid_object(obj: &DynamicObject) -> (ret: bool)
    requires model::unmarshallable_object::<K::V>(obj@)
    ensures ret == model::valid_object::<K::V>(obj@)
{
    match obj.kind() {
        Kind::ConfigMapKind => ConfigMap::unmarshal(obj.clone()).unwrap().state_validation(),
        Kind::DaemonSetKind => DaemonSet::unmarshal(obj.clone()).unwrap().state_validation(),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaim::unmarshal(obj.clone()).unwrap().state_validation(),
        Kind::PodKind => Pod::unmarshal(obj.clone()).unwrap().state_validation(),
        Kind::RoleBindingKind => RoleBinding::unmarshal(obj.clone()).unwrap().state_validation(),
        Kind::RoleKind => Role::unmarshal(obj.clone()).unwrap().state_validation(),
        Kind::SecretKind => Secret::unmarshal(obj.clone()).unwrap().state_validation(),
        Kind::ServiceKind => Service::unmarshal(obj.clone()).unwrap().state_validation(),
        Kind::StatefulSetKind => StatefulSet::unmarshal(obj.clone()).unwrap().state_validation(),
        Kind::ServiceAccountKind => ServiceAccount::unmarshal(obj.clone()).unwrap().state_validation(),
        Kind::CustomResourceKind => {
            proof {
                K::V::unmarshal_result_determined_by_unmarshal_spec_and_status();
                K::V::kind_is_custom_resource();
            }
            K::unmarshal(obj.clone()).unwrap().state_validation()
        },
    }
}

fn object_validity_check(obj: &DynamicObject) -> (ret: Option<APIError>)
    requires model::unmarshallable_object::<K::V>(obj@)
    ensures ret == model::object_validity_check::<K::V>(obj@)
{
    if !Self::valid_object(obj) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

fn valid_transition(obj: &DynamicObject, old_obj: &DynamicObject) -> (ret: bool)
    requires
        model::unmarshallable_object::<K::V>(obj@),
        model::unmarshallable_object::<K::V>(old_obj@),
        old_obj@.kind == obj@.kind,
        model::valid_object::<K::V>(obj@),
        model::valid_object::<K::V>(old_obj@),
    ensures ret == model::valid_transition::<K::V>(obj@, old_obj@)
{
    match obj.kind() {
        Kind::ConfigMapKind => ConfigMap::unmarshal(obj.clone()).unwrap().transition_validation(&ConfigMap::unmarshal(old_obj.clone()).unwrap()),
        Kind::DaemonSetKind => DaemonSet::unmarshal(obj.clone()).unwrap().transition_validation(&DaemonSet::unmarshal(old_obj.clone()).unwrap()),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaim::unmarshal(obj.clone()).unwrap().transition_validation(&PersistentVolumeClaim::unmarshal(old_obj.clone()).unwrap()),
        Kind::PodKind => Pod::unmarshal(obj.clone()).unwrap().transition_validation(&Pod::unmarshal(old_obj.clone()).unwrap()),
        Kind::RoleBindingKind => RoleBinding::unmarshal(obj.clone()).unwrap().transition_validation(&RoleBinding::unmarshal(old_obj.clone()).unwrap()),
        Kind::RoleKind => Role::unmarshal(obj.clone()).unwrap().transition_validation(&Role::unmarshal(old_obj.clone()).unwrap()),
        Kind::SecretKind => Secret::unmarshal(obj.clone()).unwrap().transition_validation(&Secret::unmarshal(old_obj.clone()).unwrap()),
        Kind::ServiceKind => Service::unmarshal(obj.clone()).unwrap().transition_validation(&Service::unmarshal(old_obj.clone()).unwrap()),
        Kind::StatefulSetKind => StatefulSet::unmarshal(obj.clone()).unwrap().transition_validation(&StatefulSet::unmarshal(old_obj.clone()).unwrap()),
        Kind::ServiceAccountKind => ServiceAccount::unmarshal(obj.clone()).unwrap().transition_validation(&ServiceAccount::unmarshal(old_obj.clone()).unwrap()),
        Kind::CustomResourceKind => {
            proof {
                K::V::unmarshal_result_determined_by_unmarshal_spec_and_status();
                K::V::kind_is_custom_resource();
            }
            K::unmarshal(obj.clone()).unwrap().transition_validation(&K::unmarshal(old_obj.clone()).unwrap())
        },
    }
}

fn object_transition_validity_check(obj: &DynamicObject, old_obj: &DynamicObject) -> (ret: Option<APIError>)
    requires
        model::unmarshallable_object::<K::V>(obj@),
        model::unmarshallable_object::<K::V>(old_obj@),
        old_obj@.kind == obj@.kind,
        model::valid_object::<K::V>(obj@),
        model::valid_object::<K::V>(old_obj@),
    ensures ret == model::object_transition_validity_check::<K::V>(obj@, old_obj@)
{
    if !Self::valid_transition(obj, old_obj) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub fn handle_get_request(req: &KubeGetRequest, s: &ApiServerState) -> (ret: KubeGetResponse)
    ensures ret@ == model::handle_get_request(req@, s@)
{
    let req_key = KubeObjectRef {
        kind: req.api_resource.kind(),
        name: req.name.clone(),
        namespace: req.namespace.clone(),
    };
    if !s.resources.contains_key(&req_key) {
        KubeGetResponse{res: Err(APIError::ObjectNotFound)}
    } else {
        KubeGetResponse{res: Ok(s.resources.get(&req_key).unwrap())}
    }
}

fn create_request_admission_check(req: &KubeCreateRequest, s: &ApiServerState) -> (ret: Option<APIError>)
    ensures ret == model::create_request_admission_check::<K::V>(req@, s@),
{
    if req.obj.metadata().name().is_none() {
        Some(APIError::Invalid)
    } else if req.obj.metadata().namespace().is_some() && !req.namespace.eq(&req.obj.metadata().namespace().unwrap()) {
        Some(APIError::BadRequest)
    } else if !Self::unmarshallable_object(&req.obj) {
        Some(APIError::BadRequest)
    } else if s.resources.contains_key(&KubeObjectRef {
        kind: req.obj.kind(),
        name: req.obj.metadata().name().unwrap(),
        namespace: req.namespace.clone(),
    }) {
        Some(APIError::ObjectAlreadyExists)
    } else {
        None
    }
}

fn created_object_validity_check(created_obj: &DynamicObject) -> (ret: Option<APIError>)
    requires model::unmarshallable_object::<K::V>(created_obj@)
    ensures ret == model::created_object_validity_check::<K::V>(created_obj@)
{
    if Self::metadata_validity_check(created_obj).is_some() {
        Self::metadata_validity_check(created_obj)
    } else if Self::object_validity_check(created_obj).is_some() {
        Self::object_validity_check(created_obj)
    } else {
        None
    }
}

pub fn handle_create_request(req: &KubeCreateRequest, s: &mut ApiServerState) -> (ret: KubeCreateResponse)
    requires
        // No integer overflow
        old(s).resource_version_counter < i64::MAX,
        old(s).uid_counter < i64::MAX,
    ensures (s@, ret@) == model::handle_create_request::<K::V>(req@, old(s)@)
{
    // TODO: use if-let?
    let request_check_error = Self::create_request_admission_check(req, s);
    if request_check_error.is_some() {
        KubeCreateResponse{res: Err(request_check_error.unwrap())}
    } else {
        let mut created_obj = req.obj.clone();
        created_obj.set_namespace(req.namespace.clone());
        created_obj.set_resource_version(s.resource_version_counter);
        created_obj.set_uid(s.uid_counter);
        created_obj.unset_deletion_timestamp();
        created_obj.set_default_status::<K::V>();
        let object_check_error = Self::created_object_validity_check(&created_obj);
        if object_check_error.is_some() {
            KubeCreateResponse{res: Err(object_check_error.unwrap())}
        } else {
            s.resources.insert(created_obj.object_ref(), created_obj.clone());
            s.stable_resources.remove(&created_obj.object_ref());
            s.uid_counter = s.uid_counter + 1;
            s.resource_version_counter = s.resource_version_counter + 1;
            KubeCreateResponse{res: Ok(created_obj)}
        }
    }
}

pub fn handle_delete_request(req: &KubeDeleteRequest, s: &mut ApiServerState) -> (ret: KubeDeleteResponse)
    requires old(s).resource_version_counter < i64::MAX // No integer overflow
    ensures (s@, ret@) == model::handle_delete_request(req@, old(s)@)
{
    let req_key = KubeObjectRef {
        kind: req.api_resource.kind(),
        name: req.name.clone(),
        namespace: req.namespace.clone(),
    };
    if !s.resources.contains_key(&req_key) {
        KubeDeleteResponse{res: Err(APIError::ObjectNotFound)}
    } else {
        let mut obj = s.resources.get(&req_key).unwrap();
        if obj.metadata().finalizers().is_some() && obj.metadata().finalizers().unwrap().len() > 0 {
            if obj.metadata().has_deletion_timestamp() {
                KubeDeleteResponse{res: Ok(())}
            } else {
                obj.set_current_deletion_timestamp();
                obj.set_resource_version(s.resource_version_counter);
                let stamped_obj_with_new_rv = obj; // This renaming is just to stay consistent with the model
                s.resources.insert(req_key, stamped_obj_with_new_rv);
                s.resource_version_counter = s.resource_version_counter + 1;
                KubeDeleteResponse{res: Ok(())}
            }
        } else {
            s.resources.remove(&req_key);
            s.resource_version_counter = s.resource_version_counter + 1;
            KubeDeleteResponse{res: Ok(())}
        }
    }
}

fn allow_unconditional_update(kind: &Kind) -> (ret: bool)
    ensures ret == model::allow_unconditional_update(*kind)
{
    match kind {
        Kind::CustomResourceKind => false,
        _ => true,
    }
}

fn update_request_admission_check_helper(name: &String, namespace: &String, obj: &DynamicObject, s: &ApiServerState) -> (ret: Option<APIError>)
    ensures ret == model::update_request_admission_check_helper::<K::V>(name@, namespace@, obj@, s@)
{
    let key = KubeObjectRef {
        kind: obj.kind(),
        namespace: namespace.clone(),
        name: name.clone(),
    };
    if obj.metadata().name().is_none() {
        Some(APIError::BadRequest)
    } else if !name.eq(&obj.metadata().name().unwrap()) {
        Some(APIError::BadRequest)
    } else if obj.metadata().namespace().is_some()
    && !namespace.eq(&obj.metadata().namespace().unwrap()) {
        Some(APIError::BadRequest)
    } else if !Self::unmarshallable_object(&obj) {
        Some(APIError::BadRequest)
    } else if !s.resources.contains_key(&key) {
        Some(APIError::ObjectNotFound)
    } else if !obj.metadata().has_some_resource_version()
    && !Self::allow_unconditional_update(&key.kind) {
        Some(APIError::Invalid)
    } else if obj.metadata().has_some_resource_version()
    && !obj.metadata().resource_version_eq(&s.resources.get(&key).unwrap().metadata()) {
        Some(APIError::Conflict)
    } else if obj.metadata().has_some_uid()
    && !obj.metadata().uid_eq(&s.resources.get(&key).unwrap().metadata()) {
        Some(APIError::InternalError)
    } else {
        None
    }
}

fn update_request_admission_check(req: &KubeUpdateRequest, s: &ApiServerState) -> (ret: Option<APIError>)
    ensures ret == model::update_request_admission_check::<K::V>(req@, s@)
{
    Self::update_request_admission_check_helper(&req.name, &req.namespace, &req.obj, s)
}

fn updated_object(req: &KubeUpdateRequest, old_obj: &DynamicObject) -> (ret: DynamicObject)
    ensures ret@ == model::updated_object(req@, old_obj@)
{
    let mut updated_obj = req.obj.clone();
    updated_obj.set_namespace(req.namespace.clone());
    updated_obj.set_resource_version_from(old_obj);
    updated_obj.set_uid_from(old_obj);
    updated_obj.set_deletion_timestamp_from(old_obj);
    updated_obj.set_status_from(old_obj);
    updated_obj
}

fn updated_object_validity_check(updated_obj: &DynamicObject, old_obj: &DynamicObject) -> (ret: Option<APIError>)
    requires
        model::unmarshallable_object::<K::V>(updated_obj@),
        model::unmarshallable_object::<K::V>(old_obj@),
        old_obj@.kind == updated_obj@.kind,
        model::valid_object::<K::V>(old_obj@),
    ensures ret == model::updated_object_validity_check::<K::V>(updated_obj@, old_obj@)
{
    if Self::metadata_validity_check(updated_obj).is_some() {
        Self::metadata_validity_check(updated_obj)
    } else if Self::metadata_transition_validity_check(updated_obj, old_obj).is_some() {
        Self::metadata_transition_validity_check(updated_obj, old_obj)
    } else if Self::object_validity_check(updated_obj).is_some() {
        Self::object_validity_check(updated_obj)
    } else if Self::object_transition_validity_check(updated_obj, old_obj).is_some() {
        Self::object_transition_validity_check(updated_obj, old_obj)
    } else {
        None
    }
}

pub fn handle_update_request(req: &KubeUpdateRequest, s: &mut ApiServerState) -> (ret: KubeUpdateResponse)
    requires
        // No integer overflow
        old(s).resource_version_counter < i64::MAX,
        // The old version is marshallable
        old(s)@.resources.contains_key(req@.key()) ==> model::unmarshallable_object::<K::V>(old(s)@.resources[req@.key()]),
        // The old version passes state validation
        old(s)@.resources.contains_key(req@.key()) ==> model::valid_object::<K::V>(old(s)@.resources[req@.key()]),
        // The old version has the right key (name, namespace, kind)
        old(s)@.resources.contains_key(req@.key()) ==> old(s)@.resources[req@.key()].object_ref() == req@.key(),
        // All the three preconditions above are proved by the invariant lemma_always_each_object_in_etcd_is_well_formed
    ensures (s@, ret@) == model::handle_update_request::<K::V>(req@, old(s)@)
{
    let request_check_error = Self::update_request_admission_check(req, s);
    if request_check_error.is_some() {
        KubeUpdateResponse{res: Err(request_check_error.unwrap())}
    } else {
        let req_key = KubeObjectRef {
            kind: req.obj.kind(),
            namespace: req.namespace.clone(),
            name: req.name.clone(),
        };
        let old_obj = s.resources.get(&req_key).unwrap();
        let mut updated_obj = Self::updated_object(&req, &old_obj);
        if updated_obj.eq(&old_obj) {
            KubeUpdateResponse{res: Ok(old_obj)}
        } else {
            updated_obj.set_resource_version(s.resource_version_counter);
            let updated_obj_with_new_rv = updated_obj; // This renaming is just to stay consistent with the model
            let object_check_error = Self::updated_object_validity_check(&updated_obj_with_new_rv, &old_obj);
            if object_check_error.is_some() {
                KubeUpdateResponse{res: Err(object_check_error.unwrap())}
            } else {
                if !updated_obj_with_new_rv.metadata().has_deletion_timestamp()
                    || (updated_obj_with_new_rv.metadata().finalizers().is_some()
                        && updated_obj_with_new_rv.metadata().finalizers().unwrap().len() > 0)
                {
                    s.stable_resources.remove(&req_key);
                    s.resources.insert(req_key, updated_obj_with_new_rv.clone());
                    s.resource_version_counter = s.resource_version_counter + 1;
                    KubeUpdateResponse{res: Ok(updated_obj_with_new_rv)}
                } else {
                    s.resources.remove(&updated_obj_with_new_rv.object_ref());
                    s.resource_version_counter = s.resource_version_counter + 1;
                    KubeUpdateResponse{res: Ok(updated_obj_with_new_rv)}
                }
            }
        }
    }
}

fn update_status_request_admission_check(req: &KubeUpdateStatusRequest, s: &ApiServerState) -> (ret: Option<APIError>)
    ensures ret == model::update_status_request_admission_check::<K::V>(req@, s@)
{
    Self::update_request_admission_check_helper(&req.name, &req.namespace, &req.obj, s)
}

fn status_updated_object(req: &KubeUpdateStatusRequest, old_obj: &DynamicObject) -> (ret: DynamicObject)
    ensures ret@ == model::status_updated_object(req@, old_obj@)
{
    let mut status_updated_object = req.obj.clone();
    status_updated_object.set_metadata_from(old_obj);
    status_updated_object.set_spec_from(old_obj);
    status_updated_object
}

pub fn handle_update_status_request(req: &KubeUpdateStatusRequest, s: &mut ApiServerState) -> (ret: KubeUpdateStatusResponse)
    requires
        // No integer overflow
        old(s).resource_version_counter < i64::MAX,
        // The old version is marshallable
        old(s)@.resources.contains_key(req@.key()) ==> model::unmarshallable_object::<K::V>(old(s)@.resources[req@.key()]),
        // The old version passes state validation
        old(s)@.resources.contains_key(req@.key()) ==> model::valid_object::<K::V>(old(s)@.resources[req@.key()]),
        // The old version has the right key (name, namespace, kind)
        old(s)@.resources.contains_key(req@.key()) ==> old(s)@.resources[req@.key()].object_ref() == req@.key(),
        // All the three preconditions above are proved by the invariant lemma_always_each_object_in_etcd_is_well_formed
    ensures (s@, ret@) == model::handle_update_status_request::<K::V>(req@, old(s)@)
{
    let request_check_error = Self::update_status_request_admission_check(req, s);
    if request_check_error.is_some() {
        KubeUpdateStatusResponse{res: Err(request_check_error.unwrap())}
    } else {
        let req_key = KubeObjectRef {
            kind: req.obj.kind(),
            namespace: req.namespace.clone(),
            name: req.name.clone(),
        };
        let old_obj = s.resources.get(&req_key).unwrap();
        let mut status_updated_obj = Self::status_updated_object(&req, &old_obj);
        if status_updated_obj.eq(&old_obj) {
            KubeUpdateStatusResponse{res: Ok(old_obj)}
        } else {
            status_updated_obj.set_resource_version(s.resource_version_counter);
            let status_updated_obj_with_new_rv = status_updated_obj; // This renaming is just to stay consistent with the model
            let object_check_error = Self::updated_object_validity_check(&status_updated_obj_with_new_rv, &old_obj);
            if object_check_error.is_some() {
                KubeUpdateStatusResponse{res: Err(object_check_error.unwrap())}
            } else {
                s.resources.insert(req_key, status_updated_obj_with_new_rv.clone());
                s.resource_version_counter = s.resource_version_counter + 1;
                KubeUpdateStatusResponse{res: Ok(status_updated_obj_with_new_rv)}
            }
        }
    }
}

}

}
