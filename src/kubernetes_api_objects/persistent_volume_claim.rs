// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use vstd::prelude::*;

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
    // pub spec: Option<PersistentVolumeClaimSpecView>,
    // pub status: Option<PersistentVolumeClaimStatusView>,
}

impl PersistentVolumeClaim {
    pub spec fn view(&self) -> PersistentVolumeClaimView;

    #[verifier(external_body)]
    pub fn default() -> (pvc: PersistentVolumeClaim)
        ensures
            pvc@ == PersistentVolumeClaimView::default(),
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

    // #[verifier(external_body)]
    // pub fn spec(&self) -> (spec: Option<PersistentVolumeClaimSpec>)
    //     ensures
    //         self@.spec.is_Some() == spec.is_Some(),
    //         spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    // {
    //     todo!()
    // }

    // #[verifier(external_body)]
    // pub fn status(&self) -> (status: Option<PersistentVolumeClaimStatus>)
    //     ensures
    //         self@.status.is_Some() == status.is_Some(),
    //         status.is_Some() ==> status.get_Some_0()@ == self@.status.get_Some_0(),
    // {
    //     todo!()
    // }
}

impl PersistentVolumeClaimView {
    pub open spec fn default() -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            metadata: ObjectMetaView::default(),
            // spec: Option::None,
            // status: Option::None,
        }
    }
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
            data: Value::Object(Map::empty()),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            metadata: obj.metadata,
        }
    }

    proof fn integrity_check() {}
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
    pub fn default() -> (pvc_spec: PersistentVolumeClaimSpec)
        ensures
            pvc_spec@ == PersistentVolumeClaimSpecView::default(),
    {
        PersistentVolumeClaimSpec {
            inner: K8SPersistentVolumeClaimSpec::default(),
        }
    }
}

impl PersistentVolumeClaimSpecView {
    pub open spec fn default() -> PersistentVolumeClaimSpecView {
       PersistentVolumeClaimSpecView {}
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
    pub fn default() -> (pvc_status: PersistentVolumeClaimStatus)
        ensures
            pvc_status@ == PersistentVolumeClaimStatusView::default(),
    {
        PersistentVolumeClaimStatus {
            inner: K8SPersistentVolumeClaimStatus::default(),
        }
    }
}

impl PersistentVolumeClaimStatusView {
    pub open spec fn default() -> PersistentVolumeClaimStatusView {
       PersistentVolumeClaimStatusView {}
    }
}

}
