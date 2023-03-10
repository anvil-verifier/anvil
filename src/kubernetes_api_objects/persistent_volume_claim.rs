// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::object_meta::*;
use crate::pervasive::prelude::*;

use k8s_openapi::api::core::v1::PersistentVolumeClaim as K8SPersistentVolumeClaim;
use k8s_openapi::api::core::v1::PersistentVolumeClaimSpec as K8SPersistentVolumeClaimSpec;
use k8s_openapi::api::core::v1::PersistentVolumeClaimStatus as K8SPersistentVolumeClaimStatus;

verus! {

#[verifier(external_body)]
pub struct PersistentVolumeClaim {
    inner: K8SPersistentVolumeClaim,
}

pub struct PersistentVolumeClaimView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PersistentVolumeClaimSpecView>,
    pub status: Option<PersistentVolumeClaimStatusView>,
}

impl PersistentVolumeClaim {
    pub spec fn view(&self) -> PersistentVolumeClaimView;

    #[verifier(external_body)]
    pub fn default() -> (pod: PersistentVolumeClaim)
        ensures
            pod@.is_default(),
    {
        PersistentVolumeClaim {
            inner: K8SPersistentVolumeClaim::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        todo!()
    }

    // is it OK to name it spec?
    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<PersistentVolumeClaimSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn status(&self) -> (status: Option<PersistentVolumeClaimStatus>)
        ensures
            self@.status.is_Some() == status.is_Some(),
            status.is_Some() ==> status.get_Some_0()@ == self@.status.get_Some_0(),
    {
        todo!()
    }
}

impl PersistentVolumeClaimView {
    pub open spec fn is_default(self) -> bool {
        &&& self.metadata.is_default()
        &&& self.spec.is_None()
        &&& self.status.is_None()
    }
}

#[verifier(external_body)]
pub struct PersistentVolumeClaimSpec {
    inner: K8SPersistentVolumeClaimSpec,
}

pub struct PersistentVolumeClaimSpecView {
    // A lot more fields to specify...
}

impl PersistentVolumeClaimSpec {
    pub spec fn view(&self) -> PersistentVolumeClaimSpecView;

    #[verifier(external_body)]
    pub fn default() -> (pod_spec: PersistentVolumeClaimSpec)
        ensures
            pod_spec@.is_default(),
    {
        PersistentVolumeClaimSpec {
            inner: K8SPersistentVolumeClaimSpec::default(),
        }
    }
}

impl PersistentVolumeClaimSpecView {
    pub open spec fn is_default(self) -> bool {
       true
       // The condition depends on how default() is implemented
    }
}

#[verifier(external_body)]
pub struct PersistentVolumeClaimStatus {
    inner: K8SPersistentVolumeClaimStatus,
}

pub struct PersistentVolumeClaimStatusView {
    // A lot more fields to specify...
}

impl PersistentVolumeClaimStatus {
    pub spec fn view(&self) -> PersistentVolumeClaimStatusView;

    #[verifier(external_body)]
    pub fn default() -> (pod_status: PersistentVolumeClaimStatus)
        ensures
            pod_status@.is_default(),
    {
        PersistentVolumeClaimStatus {
            inner: K8SPersistentVolumeClaimStatus::default(),
        }
    }
}

impl PersistentVolumeClaimStatusView {
    pub open spec fn is_default(self) -> bool {
       true
       // The condition depends on how default() is implemented
    }
}

}
