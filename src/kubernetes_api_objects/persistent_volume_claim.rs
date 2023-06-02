// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_api_objects::resource_requirements::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::vec::*;

verus! {

/// PersistentVolumeClaim is a type of API object representing a request for storage (typically used by a Pod).
/// PersistentVolumeClaim objects are often defined in StatefulSet objects as the Volumes mounted to the Pods.
///
/// This definition is a wrapper of PersistentVolumeClaim defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/persistent_volume_claim.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/storage/persistent-volumes/.

#[verifier(external_body)]
pub struct PersistentVolumeClaim {
    inner: deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim,
}

impl PersistentVolumeClaim {
    pub spec fn view(&self) -> PersistentVolumeClaimView;

    #[verifier(external_body)]
    pub fn default() -> (pvc: PersistentVolumeClaim)
        ensures
            pvc@ == PersistentVolumeClaimView::default(),
    {
        PersistentVolumeClaim {
            inner: deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<PersistentVolumeClaimSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures
            self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: PersistentVolumeClaimSpec)
        ensures
            self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = std::option::Option::Some(spec.into_kube());
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::CustomResourceKind,
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim>(&()))
    }

    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (pvc: PersistentVolumeClaim)
        ensures
            pvc@ == PersistentVolumeClaimView::from_dynamic_object(obj@),
    {
        PersistentVolumeClaim { inner: obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim>().unwrap() }
    }
}

impl ResourceWrapper<deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim> for PersistentVolumeClaim {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim) -> PersistentVolumeClaim {
        PersistentVolumeClaim {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim {
        self.inner
    }
}

#[verifier(external_body)]
pub struct PersistentVolumeClaimSpec {
    inner: deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec,
}

impl PersistentVolumeClaimSpec {
    pub spec fn view(&self) -> PersistentVolumeClaimSpecView;

    #[verifier(external_body)]
    pub fn default() -> (pvc_spec: PersistentVolumeClaimSpec)
        ensures
            pvc_spec@ == PersistentVolumeClaimSpecView::default(),
    {
        PersistentVolumeClaimSpec {
            inner: deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_access_modes(&mut self, access_modes: Vec<String>)
        ensures
            self@ == old(self)@.set_access_modes(access_modes@.map_values(|mode: String| mode@)),
    {
        self.inner.access_modes = std::option::Option::Some(
            access_modes.vec.into_iter().map(|mode: String| mode.into_rust_string()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_resources(&mut self, resources: ResourceRequirements)
        ensures
            self@ == old(self)@,
    {
        self.inner.resources = std::option::Option::Some(resources.into_kube())
    }
}

impl ResourceWrapper<deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec> for PersistentVolumeClaimSpec {
    #[verifier(external)]
    fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec) -> PersistentVolumeClaimSpec {
        PersistentVolumeClaimSpec {
            inner: inner
        }
    }

    #[verifier(external)]
    fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec {
        self.inner
    }
}

/// PersistentVolumeClaimView is the ghost type of PersistentVolumeClaim.
/// It is supposed to be used in spec and proof code.

pub struct PersistentVolumeClaimView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PersistentVolumeClaimSpecView>,
}

impl PersistentVolumeClaimView {
    pub open spec fn default() -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            metadata: ObjectMetaView::default(),
            spec: Option::None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: PersistentVolumeClaimSpecView) -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            spec: Option::Some(spec),
            ..self
        }
    }

    pub open spec fn metadata_field() -> nat {0}

    pub open spec fn spec_field() -> nat {1}
}

impl ResourceView for PersistentVolumeClaimView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind(self) -> Kind {
        Kind::PersistentVolumeClaimKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: self.kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: self.kind(),
            metadata: self.metadata,
            data: Value::Object(Map::empty()
                                    .insert(Self::spec_field(), if self.spec.is_None() {Value::Null} else {
                                        self.spec.get_Some_0().marshal()
                                    })),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            metadata: obj.metadata,
            spec: if obj.data.get_Object_0()[Self::spec_field()].is_Null() {Option::None} else {
                Option::Some(PersistentVolumeClaimSpecView::unmarshal(obj.data.get_Object_0()[Self::spec_field()]))
            },
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        assert forall |o: Self| o == Self::from_dynamic_object(#[trigger] o.to_dynamic_object()) by {
            if o.spec.is_Some() && o.spec.get_Some_0().access_modes.is_Some() {
                assert_seqs_equal!(
                    o.spec.get_Some_0().access_modes.get_Some_0(),
                    Self::from_dynamic_object(o.to_dynamic_object()).spec.get_Some_0().access_modes.get_Some_0()
                );
            }
        }
    }
}

impl Marshalable for PersistentVolumeClaimView {
    open spec fn marshal(self) -> Value {
        Value::Object(Map::empty()
                        .insert(Self::metadata_field(), self.metadata.marshal())
                        .insert(Self::spec_field(), if self.spec.is_None() { Value::Null } else {
                            self.spec.get_Some_0().marshal()
                        }))
    }

    open spec fn unmarshal(value: Value) -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            metadata: ObjectMetaView::unmarshal(value.get_Object_0()[Self::metadata_field()]),
            spec: if value.get_Object_0()[Self::spec_field()].is_Null() { Option::None } else {
                Option::Some(PersistentVolumeClaimSpecView::unmarshal(value.get_Object_0()[Self::spec_field()]))
            },
        }
    }

    proof fn marshal_preserves_integrity() {
        PersistentVolumeClaimSpecView::marshal_preserves_integrity();
    }
}

pub struct PersistentVolumeClaimSpecView {
    pub access_modes: Option<Seq<StringView>>,
}

impl PersistentVolumeClaimSpecView {
    pub open spec fn default() -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            access_modes: Option::None,
        }
    }

    pub open spec fn set_access_modes(self, access_modes: Seq<StringView>) -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            access_modes: Option::Some(access_modes),
            ..self
        }
    }

    pub open spec fn access_modes_field() -> nat {0}
}

impl Marshalable for PersistentVolumeClaimSpecView {
    open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::access_modes_field(), if self.access_modes.is_None() { Value::Null } else {
                    Value::Array(self.access_modes.get_Some_0().map_values(|mode: StringView| Value::String(mode)))
                })
        )
    }

    open spec fn unmarshal(value: Value) -> Self {
        PersistentVolumeClaimSpecView {
            access_modes: if value.get_Object_0()[Self::access_modes_field()].is_Null() { Option::None } else {
                Option::Some(value.get_Object_0()[Self::access_modes_field()].get_Array_0().map_values(|v: Value| v.get_String_0()))
            },
        }
    }

    proof fn marshal_preserves_integrity() {
        assert forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()) by {
            if o.access_modes.is_Some() {
                assert_seqs_equal!(o.access_modes.get_Some_0(), Self::unmarshal(o.marshal()).access_modes.get_Some_0());
            }
        }
    }
}

}
