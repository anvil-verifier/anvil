// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::controller::common::ControllerState;
use crate::kubernetes_cluster::spec::{
    cluster::Cluster, kubernetes_api::common::*, kubernetes_api::state_machine::*, message::*,
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
fn controller_references(owner_references: &Vec<OwnerReference>) -> (ret: Vec<OwnerReference>)
    ensures ret@.map_values(|o: OwnerReference| o@) == owner_references@.map_values(|o: OwnerReference| o@).filter(|o: OwnerReferenceView| o.controller.is_Some() && o.controller.get_Some_0())
{
    // TODO: is there a way to prove postconditions involving filter?
    // TODO: clone the entire Vec instead of clone in map()
    owner_references.iter().map(|o: &OwnerReference| o.clone()).filter(|o: &OwnerReference| o.controller().is_some() && o.controller().unwrap()).collect()
}

fn metadata_validity_check(obj: &DynamicObject) -> (err_opt: Option<APIError>)
    ensures err_opt == metadata_validity_check(obj@)
{
    if obj.metadata().owner_references().is_some()
    && obj.metadata().owner_references().unwrap().len() > 1
    && Self::controller_references(&obj.metadata().owner_references().unwrap()).len() >= 2 {
        Some(APIError::Invalid)
    } else {
        None
    }
}

// fn update_request_admission_check_helper(name: String, namespace: String, obj: DynamicObject, )

// pub open spec fn update_request_admission_check_helper<K: ResourceView>(name: StringView, namespace: StringView, obj: DynamicObjectView, s: KubernetesAPIState) -> Option<APIError> {
//     let key = ObjectRef {
//         kind: obj.kind,
//         namespace: namespace,
//         name: name,
//     };
//     if obj.metadata.name.is_None() {
//         // Update fails because the name of the object is not provided
//         Some(APIError::BadRequest)
//     } else if name != obj.metadata.name.get_Some_0() {
//         // Update fails because the name of the provided object
//         // does not match the name sent on the request
//         Some(APIError::BadRequest)
//     } else if obj.metadata.namespace.is_Some()
//         && namespace != obj.metadata.namespace.get_Some_0() {
//         // Update fails because the namespace of the provided object
//         // does not match the namespace sent on the request
//         Some(APIError::BadRequest)
//     } else if !unmarshallable_object::<K>(obj) {
//         // Update fails because the provided object is not well formed
//         // TODO: should the error be BadRequest?
//         Some(APIError::BadRequest)
//     } else if !s.resources.contains_key(key) {
//         // Update fails because the object does not exist
//         // TODO: check AllowCreateOnUpdate() to see whether to support create-on-update
//         Some(APIError::ObjectNotFound)
//     } else if obj.metadata.resource_version.is_None()
//         && !allow_unconditional_update(key.kind) {
//         // Update fails because the object does not provide a rv and unconditional update is not supported
//         Some(APIError::Invalid)
//     } else if obj.metadata.resource_version.is_Some()
//         && obj.metadata.resource_version != s.resources[key].metadata.resource_version {
//         // Update fails because the object has a wrong rv
//         Some(APIError::Conflict)
//     } else if obj.metadata.uid.is_Some()
//         && obj.metadata.uid != s.resources[key].metadata.uid {
//         // Update fails because the object has a wrong uid
//         // TODO: double check the Error type
//         Some(APIError::InternalError)
//     } else {
//         None
//     }
// }

}

}
