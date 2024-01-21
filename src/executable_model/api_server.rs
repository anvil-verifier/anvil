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
use crate::kubernetes_cluster::spec::controller::common::ControllerState;
use crate::kubernetes_cluster::spec::{
    kubernetes_api::common as model_types, kubernetes_api::state_machine as model,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{multiset::*, prelude::*};

verus! {

struct ExecutableAPIServerModel<K> where K: View, K::V: ResourceView {
    k: K,
}

pub struct ExecutableAPIServerState {
    pub resources: StoredState,
}

impl <K> ExecutableAPIServerModel<K> where K: View, K::V: ResourceView {

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

fn update_request_admission_check_helper(name: String, namespace: String, obj: DynamicObject, s: ApiServerState) -> (ret: Option<APIError>)
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
