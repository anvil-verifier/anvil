// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::config_map::ConfigMapView;
use crate::kubernetes_api_objects::custom_resource::CustomResourceView;
use crate::kubernetes_api_objects::object_meta::ObjectMetaView;
use crate::kubernetes_api_objects::persistent_volume_claim::PersistentVolumeClaimView;
use crate::kubernetes_api_objects::pod::PodView;
use crate::kubernetes_api_objects::service::ServiceView;
use crate::kubernetes_api_objects::stateful_set::StatefulSetView;

verus! {

#[is_variant]
pub enum KubernetesObject {
    ConfigMap(ConfigMapView),
    CustomResource(CustomResourceView),
    PersistentVolumeClaim(PersistentVolumeClaimView),
    Pod(PodView),
    StatefulSet(StatefulSetView),
    Service(ServiceView),
}

impl KubernetesObject {
    pub open spec fn kind(self) -> Kind {
        match self {
            KubernetesObject::ConfigMap(obj) => obj.kind(),
            KubernetesObject::CustomResource(obj) => obj.kind(),
            KubernetesObject::PersistentVolumeClaim(obj) => obj.kind(),
            KubernetesObject::Pod(obj) => obj.kind(),
            KubernetesObject::StatefulSet(obj) => obj.kind(),
            KubernetesObject::Service(obj) => obj.kind(),
        }
    }

    pub open spec fn metadata(self) -> ObjectMetaView {
        match self {
            KubernetesObject::ConfigMap(obj) => obj.metadata,
            KubernetesObject::CustomResource(obj) => obj.metadata,
            KubernetesObject::PersistentVolumeClaim(obj) => obj.metadata,
            KubernetesObject::Pod(obj) => obj.metadata,
            KubernetesObject::StatefulSet(obj) => obj.metadata,
            KubernetesObject::Service(obj) => obj.metadata,
        }
    }

    pub open spec fn object_ref(self) -> ObjectRef
        recommends
            self.metadata().name.is_Some(),
            self.metadata().namespace.is_Some(),
    {
        ObjectRef {
            kind: self.kind(),
            name: self.metadata().name.get_Some_0(),
            namespace: self.metadata().namespace.get_Some_0(),
        }
    }
}

}
