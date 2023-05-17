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

/// This trait defines the methods that each ghost type of Kubernetes resource object should implement
pub trait ResourceView: Sized {
    // TODO: make metadata() a trait method
    // TODO: implement this trait for all k8s resource types

    /// Get the kind of the object
    open spec fn kind(self) -> Kind;

    /// Get the reference of the object,
    /// which consists of kind, name and namespace
    open spec fn object_ref(self) -> ObjectRef;

    /// Convert the object to a dynamic object
    open spec fn to_dynamic_object(self) -> DynamicObjectView;

    /// Convert back from a dynamic object
    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Self;

    /// Check if the data integrity is preserved after converting to and back from dynamic object
    proof fn integrity_check()
        ensures forall |o: Self| o == Self::from_dynamic_object(#[trigger] o.to_dynamic_object());
}

}
