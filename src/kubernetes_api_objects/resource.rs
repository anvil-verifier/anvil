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
    type Spec;

    /// Get the metadata of the object

    open spec fn metadata(self) -> ObjectMetaView;

    /// Get the kind of the object

    open spec fn kind() -> Kind;

    /// Get the reference of the object,
    /// which consists of kind, name and namespace

    // TODO: object_ref can be implemented here if default implementation is supported by Verus
    open spec fn object_ref(self) -> ObjectRef;

    proof fn object_ref_is_well_formed()
        ensures
            forall |o: Self|
                #[trigger] o.object_ref() == (ObjectRef {
                    kind: Self::kind(),
                    name: o.metadata().name.get_Some_0(),
                    namespace: o.metadata().namespace.get_Some_0(),
                });

    /// Get the spec of the object

    open spec fn spec(self) -> Self::Spec;

    /// Convert the object to a dynamic object

    open spec fn to_dynamic_object(self) -> DynamicObjectView;

    /// Convert back from a dynamic object

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<Self, ParseDynamicObjectError>;

    /// Check if the data integrity is preserved after converting to and back from dynamic object

    proof fn to_dynamic_preserves_integrity()
        ensures
            forall |o: Self| Self::from_dynamic_object(#[trigger] o.to_dynamic_object()).is_Ok()
                            && o == Self::from_dynamic_object(o.to_dynamic_object()).get_Ok_0();

    proof fn from_dynamic_preserves_metadata()
        ensures
            forall |d: DynamicObjectView|
                #[trigger] Self::from_dynamic_object(d).is_Ok()
                    ==> d.metadata == Self::from_dynamic_object(d).get_Ok_0().metadata();

    proof fn from_dynamic_preserves_kind()
        ensures
            forall |d: DynamicObjectView|
                #[trigger] Self::from_dynamic_object(d).is_Ok()
                    ==> d.kind == Self::kind();

    closed spec fn marshal_spec(s: Self::Spec) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, ParseDynamicObjectError>;

    proof fn spec_integrity_is_preserved_by_marshal()
        ensures
            forall |s: Self::Spec|
                Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)).is_Ok()
                && s == Self::unmarshal_spec(Self::marshal_spec(s)).get_Ok_0();
    
    proof fn from_dynamic_object_result_determined_by_unmarshal()
        ensures
            forall |obj: DynamicObjectView|
                obj.kind == Self::kind() ==> Self::unmarshal_spec(obj.spec).is_Ok() == #[trigger] Self::from_dynamic_object(obj).is_Ok();

    /// This method specifies the validation rule that only checks the new object.
    open spec fn rule(obj: Self) -> bool;

    /// This method specifies the validation rule that checks the relations between the new and old object.
    open spec fn transition_rule(new_obj: Self, old_obj: Self) -> bool;

}

}
