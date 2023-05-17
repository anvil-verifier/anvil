// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use vstd::prelude::*;

use k8s_openapi::api::core::v1::Pod as K8SPod;
use k8s_openapi::api::core::v1::PodSpec as K8SPodSpec;
use k8s_openapi::api::core::v1::PodStatus as K8SPodStatus;

verus! {

#[verifier(external_body)]
pub struct Pod {
    inner: K8SPod,
}

pub struct PodView {
    pub metadata: ObjectMetaView,
    // pub spec: Option<PodSpecView>,
    // pub status: Option<PodStatusView>,
}

impl Pod {
    pub spec fn view(&self) -> PodView;

    #[verifier(external_body)]
    pub fn default() -> (pod: Pod)
        ensures
            pod@ == PodView::default(),
    {
        Pod {
            inner: K8SPod::default(),
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
    // pub fn spec(&self) -> (spec: Option<PodSpec>)
    //     ensures
    //         self@.spec.is_Some() == spec.is_Some(),
    //         spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    // {
    //     todo!()
    // }

    // #[verifier(external_body)]
    // pub fn status(&self) -> (status: Option<PodStatus>)
    //     ensures
    //         self@.status.is_Some() == status.is_Some(),
    //         status.is_Some() ==> status.get_Some_0()@ == self@.status.get_Some_0(),
    // {
    //     todo!()
    // }
}

impl PodView {
    pub open spec fn default() -> PodView {
        PodView {
            metadata: ObjectMetaView::default(),
            // spec: Option::None,
            // status: Option::None,
        }
    }
}

impl ResourceView for PodView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind(self) -> Kind {
        Kind::PodKind
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

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> PodView {
        PodView {
            metadata: obj.metadata,
        }
    }

    proof fn integrity_check() {}
}

#[verifier(external_body)]
pub struct PodSpec {
    inner: K8SPodSpec,
}

pub struct PodSpecView {
    // A lot more fields to specify...
}

impl PodSpec {
    pub spec fn view(&self) -> PodSpecView;

    #[verifier(external_body)]
    pub fn default() -> (pod_spec: PodSpec)
        ensures
            pod_spec@ == PodSpecView::default(),
    {
        PodSpec {
            inner: K8SPodSpec::default(),
        }
    }
}

impl PodSpecView {
    pub open spec fn default() -> PodSpecView {
        PodSpecView {}
    }
}

#[verifier(external_body)]
pub struct PodStatus {
    inner: K8SPodStatus,
}

pub struct PodStatusView {
    // A lot more fields to specify...
}

impl PodStatus {
    pub spec fn view(&self) -> PodStatusView;

    #[verifier(external_body)]
    pub fn default() -> (pod_status: PodStatus)
        ensures
            pod_status@ == PodStatusView::default(),
    {
        PodStatus {
            inner: K8SPodStatus::default(),
        }
    }
}

impl PodStatusView {
    pub open spec fn default() -> PodStatusView {
       PodStatusView {}
    }
}

}
