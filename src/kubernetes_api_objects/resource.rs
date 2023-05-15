// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

use k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta as K8SObjectMeta;
use kube::api::DynamicObject as K8SDynamicObject;

verus! {


pub trait ResourceView: Sized {
    // TODO: make metadata() a trait method
    open spec fn object_ref(self) -> ObjectRef;
    open spec fn to_dynamic_object(self) -> DynamicObjectView;
    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Self;
    proof fn integrity_check()
        ensures forall |o: Self| o == Self::from_dynamic_object(#[trigger] o.to_dynamic_object());
}

}
