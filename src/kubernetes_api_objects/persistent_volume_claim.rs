// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

#[verifier(external_body)]
pub struct PersistentVolumeClaim {
    inner: k8s_openapi::api::core::v1::PersistentVolumeClaim,
}

impl PersistentVolumeClaim {
    pub spec fn view(&self) -> PersistentVolumeClaimView;

    #[verifier(external_body)]
    pub fn default() -> (pvc: PersistentVolumeClaim)
        ensures
            pvc@ == PersistentVolumeClaimView::default(),
    {
        PersistentVolumeClaim {
            inner: k8s_openapi::api::core::v1::PersistentVolumeClaim::default(),
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
}

#[verifier(external_body)]
pub struct PersistentVolumeClaimSpec {
    inner: k8s_openapi::api::core::v1::PersistentVolumeClaimSpec,
}

impl PersistentVolumeClaimSpec {
    pub spec fn view(&self) -> PersistentVolumeClaimSpecView;

    #[verifier(external_body)]
    pub fn default() -> (pvc_spec: PersistentVolumeClaimSpec)
        ensures
            pvc_spec@ == PersistentVolumeClaimSpecView::default(),
    {
        PersistentVolumeClaimSpec {
            inner: k8s_openapi::api::core::v1::PersistentVolumeClaimSpec::default(),
        }
    }
}

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

    pub open spec fn spec_field() -> nat {0}
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

    proof fn integrity_check() {
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

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::access_modes_field(), if self.access_modes.is_None() {Value::Null} else {
                    Value::Array(self.access_modes.get_Some_0().map_values(|mode: StringView| Value::String(mode)))
                })
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        PersistentVolumeClaimSpecView {
            access_modes: if value.get_Object_0()[Self::access_modes_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::access_modes_field()].get_Array_0().map_values(|v: Value| v.get_String_0()))
            },
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal())
    {
        assert forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()) by {
            if o.access_modes.is_Some() {
                assert_seqs_equal!(o.access_modes.get_Some_0(), Self::unmarshal(o.marshal()).access_modes.get_Some_0());
            }
        }
    }

    pub open spec fn access_modes_field() -> nat {0}
}

}
