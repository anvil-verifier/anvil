// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError, marshal::*,
    object_meta::*, resource::*, resource_requirements::*,
};
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;

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
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<PersistentVolumeClaimSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        match &self.inner.spec {
            Some(s) => Some(PersistentVolumeClaimSpec::from_kube(s.clone())),
            None => None,
        }
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
        self.inner.spec = Some(spec.into_kube());
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == PersistentVolumeClaimView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim>(&()))
    }

    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<PersistentVolumeClaim, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == PersistentVolumeClaimView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == PersistentVolumeClaimView::unmarshal(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim>();
        if parse_result.is_ok() {
            let res = PersistentVolumeClaim { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
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
        self.inner.access_modes = Some(
            access_modes.into_iter().map(|mode: String| mode.into_rust_string()).collect()
        );
    }

    #[verifier(external_body)]
    pub fn set_resources(&mut self, resources: ResourceRequirements)
        ensures
            self@ == old(self)@.set_resources(resources@),
    {
        self.inner.resources = Some(resources.into_kube());
    }

    #[verifier(external_body)]
    pub fn overwrite_storage_class_name(&mut self, storage_class_name: Option<String>)
        ensures
            storage_class_name.is_None() ==> self@ == old(self)@.overwrite_storage_class_name(None),
            storage_class_name.is_Some() ==> self@ == old(self)@.overwrite_storage_class_name(Some(storage_class_name.get_Some_0()@)),
    {
        match storage_class_name {
            Some(n) => {
                self.inner.storage_class_name = Some(n.into_rust_string());
            },
            None => {
                self.inner.storage_class_name = None;
            }
        }
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
            spec: None,
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
            spec: Some(spec),
            ..self
        }
    }
}

impl ResourceView for PersistentVolumeClaimView {
    type Spec = Option<PersistentVolumeClaimSpecView>;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::PersistentVolumeClaimKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> Option<PersistentVolumeClaimSpecView> {
        self.spec
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: PersistentVolumeClaimView::marshal_spec(self.spec),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<PersistentVolumeClaimView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !PersistentVolumeClaimView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(PersistentVolumeClaimView {
                metadata: obj.metadata,
                spec: PersistentVolumeClaimView::unmarshal_spec(obj.spec).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        PersistentVolumeClaimView::marshal_spec_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: Option<PersistentVolumeClaimSpecView>) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<Option<PersistentVolumeClaimSpecView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec() {}

    open spec fn state_validation(self) -> bool {
        &&& self.spec.is_Some()
    }

    open spec fn transition_validation(self, old_obj: PersistentVolumeClaimView) -> bool {
        true
    }
}

pub struct PersistentVolumeClaimSpecView {
    pub storage_class_name: Option<StringView>,
    pub access_modes: Option<Seq<StringView>>,
    pub resources: Option<ResourceRequirementsView>,
}

impl PersistentVolumeClaimSpecView {
    pub open spec fn default() -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            storage_class_name: None,
            access_modes: None,
            resources: None,
        }
    }

    pub open spec fn set_access_modes(self, access_modes: Seq<StringView>) -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            access_modes: Some(access_modes),
            ..self
        }
    }

    pub open spec fn set_resources(self, resources: ResourceRequirementsView) -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            resources: Some(resources),
            ..self
        }
    }

    pub open spec fn overwrite_storage_class_name(self, storage_class_name: Option<StringView>) -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            storage_class_name: storage_class_name,
            ..self
        }
    }
}

impl Marshalable for PersistentVolumeClaimSpecView {
    closed spec fn marshal(self) -> Value;

    closed spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}


}
