// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::config_map::{ConfigMap, ConfigMapView};
use crate::kubernetes_api_objects::custom_resource::{CustomResource, CustomResourceView};
use crate::kubernetes_api_objects::object_meta::ObjectMetaView;
use crate::kubernetes_api_objects::persistent_volume_claim::{
    PersistentVolumeClaim, PersistentVolumeClaimView,
};
use crate::kubernetes_api_objects::pod::{Pod, PodView};
use crate::kubernetes_api_objects::service::{Service, ServiceView};
use crate::kubernetes_api_objects::stateful_set::{StatefulSet, StatefulSetView};

verus! {

#[is_variant]
pub enum KubeObject {
    ConfigMap(ConfigMap),
    CustomResource(CustomResource),
    PersistentVolumeClaim(PersistentVolumeClaim),
    Pod(Pod),
    StatefulSet(StatefulSet),
    Service(Service),
}

impl KubeObject {
    pub open spec fn to_view(&self) -> KubernetesObject {
        match self {
            KubeObject::ConfigMap(o) => KubernetesObject::ConfigMap(o@),
            KubeObject::CustomResource(o) => KubernetesObject::CustomResource(o@),
            KubeObject::PersistentVolumeClaim(o) => KubernetesObject::PersistentVolumeClaim(o@),
            KubeObject::Pod(o) => KubernetesObject::Pod(o@),
            KubeObject::StatefulSet(o) => KubernetesObject::StatefulSet(o@),
            KubeObject::Service(o) => KubernetesObject::Service(o@),
        }
    }
}

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
