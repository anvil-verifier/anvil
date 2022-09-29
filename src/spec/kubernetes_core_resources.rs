#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use crate::custom_controller_var::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

// TODO: we should strictly follow the object layout in
// https://github.com/kubernetes/kubernetes/blob/release-1.25/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/types.go

pub trait KubernetesResource {
    open spec fn get_kind(&self) -> StringL;
    open spec fn get_object_meta(&self) -> ObjectMetaL;
    open spec fn get_key(&self) -> ObjectKey;
}

#[derive(PartialEq, Eq)]
pub struct ObjectMetaL {
    pub name: StringL,
    pub namespace: StringL,
    // TODO: use OwnerReferences instead of owner_key
    pub owner_key: ObjectKey,
}

#[derive(PartialEq, Eq)]
pub struct PodL {
    pub metadata: ObjectMetaL,
}

impl KubernetesResource for PodL {
    open spec fn get_kind(&self) -> StringL {
        StringL::Pod
    }

    open spec fn get_object_meta(&self) -> ObjectMetaL {
        self.metadata
    }

    open spec fn get_key(&self) -> ObjectKey {
        ObjectKey{
            object_type: self.get_kind(),
            namespace: self.get_object_meta().namespace,
            name: self.get_object_meta().name,
        }
    }
}

impl PodL {
    pub open spec fn key(&self) -> ObjectKey {
        ObjectKey{
            object_type: StringL::Pod,
            namespace: self.metadata.namespace,
            name: self.metadata.name,
        }
    }
}

#[derive(PartialEq, Eq)]
pub struct ConfigMapL {
    pub metadata: ObjectMetaL,
}

impl KubernetesResource for ConfigMapL {
    open spec fn get_kind(&self) -> StringL {
        StringL::ConfigMap
    }

    open spec fn get_object_meta(&self) -> ObjectMetaL {
        self.metadata
    }

    open spec fn get_key(&self) -> ObjectKey {
        ObjectKey{
            object_type: self.get_kind(),
            namespace: self.get_object_meta().namespace,
            name: self.get_object_meta().name,
        }
    }
}

impl ConfigMapL {
    pub open spec fn key(&self) -> ObjectKey {
        ObjectKey{
            object_type: StringL::ConfigMap,
            namespace: self.metadata.namespace,
            name: self.metadata.name,
        }
    }
}

#[derive(PartialEq, Eq)]
#[is_variant]
pub enum KubernetesObject {
    Pod(PodL),
    ConfigMap(ConfigMapL),
    CustomResourceObject(CustomResourceObject),
}

impl KubernetesObject {
    pub open spec fn key(&self) -> ObjectKey {
        match *self {
            KubernetesObject::Pod(p) => p.key(),
            KubernetesObject::ConfigMap(cm) => cm.key(),
            KubernetesObject::CustomResourceObject(cro) => cro.key(),
        }
    }
}

}
