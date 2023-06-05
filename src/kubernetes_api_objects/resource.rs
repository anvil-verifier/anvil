// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

use deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta as K8SObjectMeta;
use deps_hack::kube::api::DynamicObject as K8SDynamicObject;

verus! {

/// This trait defines the methods that each wrapper of Kubernetes resource object should implement
pub trait ResourceWrapper<T>: Sized {
    fn from_kube(inner: T) -> Self;

    fn into_kube(self) -> T;
}

/// This trait defines the methods that each ghost type of Kubernetes resource object should implement
pub trait ResourceView: Sized {
    /// Get the metadata of the object

    open spec fn metadata(self) -> ObjectMetaView;

    /// Get the kind of the object

    open spec fn kind(self) -> Kind;

    /// Get the reference of the object,
    /// which consists of kind, name and namespace

    // TODO: object_ref can be implemented here if default implementation is supported by Verus
    open spec fn object_ref(self) -> ObjectRef;

    /// Convert the object to a dynamic object

    open spec fn to_dynamic_object(self) -> DynamicObjectView;

    /// Convert back from a dynamic object

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<Self, ParseDynamicObjectError>;

    /// Check if the data integrity is preserved after converting to and back from dynamic object

    proof fn to_dynamic_preserves_integrity()
        ensures
            forall |o: Self| Self::from_dynamic_object(#[trigger] o.to_dynamic_object()).is_Ok()
                            && o == Self::from_dynamic_object(o.to_dynamic_object()).get_Ok_0();
}

}
