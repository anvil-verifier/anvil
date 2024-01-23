// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::executable_model::{
    api_server_state::ApiServerState, common::*, object_map::ObjectMap,
    object_ref_set::ObjectRefSet,
};
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::controller::types::ControllerState;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine as model, api_server::types as model_types,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{multiset::*, prelude::*};

verus! {

struct ExecutableApiServerModel<K> where K: View, K::V: ResourceView {
    k: K,
}

pub struct ExecutableApiServerState {
    pub resources: StoredState,
}

impl <K> ExecutableApiServerModel<K> where K: View, K::V: ResourceView {

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

#[verifier(external_body)]
fn valid_object(obj: &DynamicObject) -> (ret: bool)
    ensures ret == model::valid_object::<K::V>(obj@)
{
    unimplemented!();
}

fn object_validity_check(obj: &DynamicObject) -> (ret: Option<APIError>)
    ensures ret == model::object_validity_check::<K::V>(obj@)
{
    if !Self::valid_object(obj) {
        Some(APIError::Invalid)
    } else {
        None
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

// #[verifier(external_body)]
// fn handle_create_request(req: KubeCreateRequest, s: ApiServerState) -> (ret: (ApiServerState, Result<DynamicObject, APIError>))
//     ensures (ret.0@, ret.1@) == model::handle_create_request::<K::V>(req@, s@)
// {
//     unimplemented!();
// }

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
    } else if obj.metadata().resource_version().is_none()
    && !Self::allow_unconditional_update(&key.kind) {
        Some(APIError::Invalid)
    } else if obj.metadata().resource_version().is_some()
    && !obj.metadata().resource_version_eq(&s.resources.get(&key).unwrap().metadata()) {
        Some(APIError::Conflict)
    } else if obj.metadata().uid().is_some()
    && !obj.metadata().uid_eq(&s.resources.get(&key).unwrap().metadata()) {
        Some(APIError::InternalError)
    } else {
        None
    }
}

}

}
