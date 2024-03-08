// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*, resource_requirements::*,
};
use crate::kubernetes_api_objects::spec::{persistent_volume_claim::*, resource::*};
use crate::vstd_ext::string_view::*;
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
    pub fn eq(&self, other: &Self) -> (b: bool)
        ensures b == (self.view() == other.view())
    {
        self.inner == other.inner
    }

    #[verifier(external_body)]
    pub fn default() -> (pvc: PersistentVolumeClaim)
        ensures pvc@ == PersistentVolumeClaimView::default(),
    {
        PersistentVolumeClaim {
            inner: deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
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
        ensures self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == PersistentVolumeClaimView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim>(&()))
    }

    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
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

#[verifier(external)]
impl ResourceWrapper<deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim> for PersistentVolumeClaim {
    fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim) -> PersistentVolumeClaim { PersistentVolumeClaim { inner: inner } }

    fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim { self.inner }
}

#[verifier(external_body)]
pub struct PersistentVolumeClaimSpec {
    inner: deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec,
}

impl PersistentVolumeClaimSpec {
    pub spec fn view(&self) -> PersistentVolumeClaimSpecView;

    #[verifier(external_body)]
    pub fn default() -> (pvc_spec: PersistentVolumeClaimSpec)
        ensures pvc_spec@ == PersistentVolumeClaimSpecView::default(),
    {
        PersistentVolumeClaimSpec {
            inner: deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (pvc_spec: PersistentVolumeClaimSpec)
        ensures pvc_spec@ == self@,
    {
        PersistentVolumeClaimSpec { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_access_modes(&mut self, access_modes: Vec<String>)
        ensures self@ == old(self)@.set_access_modes(access_modes@.map_values(|mode: String| mode@)),
    {
        self.inner.access_modes = Some(access_modes.into_iter().map(|mode: String| mode.into_rust_string()).collect());
    }

    #[verifier(external_body)]
    pub fn set_resources(&mut self, resources: ResourceRequirements)
        ensures self@ == old(self)@.set_resources(resources@),
    {
        self.inner.resources = Some(resources.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_storage_class_name(&mut self, storage_class_name: String)
        ensures self@ == old(self)@.set_storage_class_name(storage_class_name@),
    {
        self.inner.storage_class_name = Some(storage_class_name.into_rust_string());
    }
}

#[verifier(external)]
impl ResourceWrapper<deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec> for PersistentVolumeClaimSpec {
    fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec) -> PersistentVolumeClaimSpec {
        PersistentVolumeClaimSpec { inner: inner }
    }

    fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec { self.inner }
}

}
