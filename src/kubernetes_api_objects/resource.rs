// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    common::*, dynamic::*, error::ParseDynamicObjectError, marshal::*, object_meta::*,
};
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

    spec fn metadata(self) -> ObjectMetaView;

    /// Get the kind of the object

    spec fn kind() -> Kind;

    /// Get the reference of the object,
    /// which consists of kind, name and namespace

    // TODO: object_ref can be implemented here if default implementation is supported by Verus
    spec fn object_ref(self) -> ObjectRef;

    proof fn object_ref_is_well_formed()
        ensures
            forall |o: Self|
                #[trigger] o.object_ref() == (ObjectRef {
                    kind: Self::kind(),
                    name: o.metadata().name.get_Some_0(),
                    namespace: o.metadata().namespace.get_Some_0(),
                });

    /// Get the spec of the object

    spec fn spec(self) -> Self::Spec;

    /// Convert the object to a dynamic object

    spec fn marshal(self) -> DynamicObjectView;

    /// Convert back from a dynamic object

    spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, ParseDynamicObjectError>;

    /// Check if the data integrity is preserved after converting to and back from dynamic object

    proof fn marshal_preserves_integrity()
        ensures
            forall |o: Self| Self::unmarshal(#[trigger] o.marshal()).is_Ok()
                            && o == Self::unmarshal(o.marshal()).get_Ok_0();

    proof fn marshal_preserves_metadata()
        ensures
            forall |d: DynamicObjectView|
                #[trigger] Self::unmarshal(d).is_Ok()
                    ==> d.metadata == Self::unmarshal(d).get_Ok_0().metadata();

    proof fn marshal_preserves_kind()
        ensures
            forall |d: DynamicObjectView|
                #[trigger] Self::unmarshal(d).is_Ok()
                    ==> d.kind == Self::kind();

    spec fn marshal_spec(s: Self::Spec) -> Value;

    spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, ParseDynamicObjectError>;

    proof fn marshal_spec_preserves_integrity()
        ensures
            forall |s: Self::Spec|
                Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)).is_Ok()
                && s == Self::unmarshal_spec(Self::marshal_spec(s)).get_Ok_0();

    proof fn unmarshal_result_determined_by_unmarshal_spec()
        ensures
            forall |obj: DynamicObjectView|
                obj.kind == Self::kind() ==> Self::unmarshal_spec(obj.spec).is_Ok() == #[trigger] Self::unmarshal(obj).is_Ok();

    /// This method specifies the validation rule that only checks the new object.
    spec fn state_validation(self) -> bool;

    /// This method specifies the validation rule that checks the relations between the new and old object.
    spec fn transition_validation(self, old_obj: Self) -> bool;

}

}
