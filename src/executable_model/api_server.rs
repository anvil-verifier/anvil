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

struct ExecutableApiServerModel<K> where K: View + CustomResource, K::V: CustomResourceView {
    k: K,
}

pub struct ExecutableApiServerState {
    pub resources: StoredState,
}

impl <K> ExecutableApiServerModel<K> where K: View + CustomResource, K::V: CustomResourceView {

#[verifier(external_body)]
fn unmarshallable_object(obj: &DynamicObject) -> (b: bool)
    ensures b == model::unmarshallable_object::<K::V>(obj@),
{ true }

fn allow_unconditional_update(kind: &Kind) -> (b: bool)
    ensures b == model::allow_unconditional_update(*kind)
{
    match kind {
        Kind::CustomResourceKind => false,
        _ => true,
    }
}

#[verifier(external_body)]
fn controller_references(owner_references: &Vec<OwnerReference>) -> (ret: Vec<OwnerReference>)
    ensures ret@.map_values(|o: OwnerReference| o@) == owner_references@.map_values(|o: OwnerReference| o@).filter(|o: OwnerReferenceView| o.controller.is_Some() && o.controller.get_Some_0())
{
    // TODO: is there a way to prove postconditions involving filter?
    // TODO: clone the entire Vec instead of clone in map()
    owner_references.iter().map(|o: &OwnerReference| o.clone()).filter(|o: &OwnerReference| o.controller().is_some() && o.controller().unwrap()).collect()
}

fn metadata_validity_check(obj: &DynamicObject) -> (ret: Option<APIError>)
    ensures ret == model::metadata_validity_check(obj@)
{
    if obj.metadata().owner_references().is_some()
    && obj.metadata().owner_references().unwrap().len() > 1
    && Self::controller_references(&obj.metadata().owner_references().unwrap()).len() >= 2 {
        Some(APIError::Invalid)
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

fn handle_get_request(req: &KubeGetRequest, s: &ApiServerState) -> (ret: KubeGetResponse)
    ensures ret@ == model::handle_get_request(req@, s@)
{
    let object_ref = KubeObjectRef {
        kind: req.api_resource.kind(),
        name: req.name.clone(),
        namespace: req.namespace.clone(),
    };
    if !s.resources.contains_key(&object_ref) {
        KubeGetResponse{res: Err(APIError::ObjectNotFound)}
    } else {
        KubeGetResponse{res: Ok(s.resources.get(&object_ref).unwrap())}
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

fn handle_create_request(req: &KubeCreateRequest, s: ApiServerState) -> (ret: (ApiServerState, KubeCreateResponse))
    requires
        s.resource_version_counter < i64::MAX,
        s.uid_counter < i64::MAX,
    ensures (ret.0@, ret.1@) == model::handle_create_request::<K::V>(req@, s@)
{
    // TODO: use if-let?
    let request_check_error = Self::create_request_admission_check(req, &s);
    if request_check_error.is_some() {
        let resp = KubeCreateResponse{res: Err(request_check_error.unwrap())};
        (s, resp)
    } else {
        let mut created_obj = req.obj.clone();
        created_obj.set_namespace(req.namespace.clone());
        created_obj.set_resource_version(s.resource_version_counter);
        created_obj.set_uid(s.uid_counter);
        created_obj.unset_deletion_timestamp();
        created_obj.set_default_status::<K::V>();
        let object_check_error = Self::created_object_validity_check(&created_obj);
        if object_check_error.is_some() {
            let resp = KubeCreateResponse{res: Err(object_check_error.unwrap())};
            (s, resp)
        } else {
            let mut s_prime = s;
            s_prime.resources.insert(created_obj.object_ref(), created_obj.clone());
            s_prime.stable_resources.remove(&created_obj.object_ref());
            s_prime.uid_counter = s_prime.uid_counter + 1;
            s_prime.resource_version_counter = s_prime.resource_version_counter + 1;
            let resp = KubeCreateResponse{res: Ok(created_obj)};
            (s_prime, resp)
        }
    }
}

fn update_request_admission_check_helper(name: &String, namespace: &String, obj: &DynamicObject, s: &ApiServerState) -> (ret: Option<APIError>)
    ensures ret == model::update_request_admission_check_helper::<K::V>(name@, namespace@, obj@, s@),
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

}

}
