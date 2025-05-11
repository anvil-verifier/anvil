// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*, volume_resource_requirements::*,
};
use crate::kubernetes_api_objects::spec::{persistent_volume_claim::*, resource::*};
use vstd::prelude::*;

// PersistentVolumeClaim is a type of API object representing a request for storage (typically used by a Pod).
// PersistentVolumeClaim objects are often defined in StatefulSet objects as the Volumes mounted to the Pods.
//
// This definition is a wrapper of PersistentVolumeClaim defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/persistent_volume_claim.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/concepts/storage/persistent-volumes/.

implement_wrapper_type!(
    PersistentVolumeClaim,
    deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim,
    PersistentVolumeClaimView
);

verus! {

impl PersistentVolumeClaim {
    #[verifier(external_body)]
    pub fn eq(&self, other: &Self) -> (b: bool)
        ensures b == (self.view() == other.view())
    {
        self.inner == other.inner
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
    pub fn set_spec(&mut self, spec: PersistentVolumeClaimSpec)
        ensures self@ == old(self)@.with_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
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
        ensures self@ == old(self)@.with_access_modes(access_modes@.map_values(|mode: String| mode@)),
    {
        self.inner.access_modes = Some(access_modes);
    }

    #[verifier(external_body)]
    pub fn set_resources(&mut self, resources: VolumeResourceRequirements)
        ensures self@ == old(self)@.with_resources(resources@),
    {
        self.inner.resources = Some(resources.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_storage_class_name(&mut self, storage_class_name: String)
        ensures self@ == old(self)@.with_storage_class_name(storage_class_name@),
    {
        self.inner.storage_class_name = Some(storage_class_name);
    }
}


}

implement_resource_wrapper_trait!(
    PersistentVolumeClaim,
    deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaim
);

implement_resource_wrapper_trait!(
    PersistentVolumeClaimSpec,
    deps_hack::k8s_openapi::api::core::v1::PersistentVolumeClaimSpec
);
