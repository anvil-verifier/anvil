use crate::kubernetes_api_objects::exec::{api_resource::ApiResource, dynamic::DynamicObject};
use crate::kubernetes_api_objects::spec::{
    common::{Kind, ObjectRef},
    dynamic::{DynamicObjectView, StoredState},
    resource::ResourceView,
};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine as model, api_server::types as model_types,
};
use vstd::prelude::*;
use vstd::string::*;

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct ExternalObjectRef {
    pub kind: Kind,
    pub name: std::string::String,
    pub namespace: std::string::String,
}

impl KubeObjectRef {
    pub fn into_external_object_ref(self) -> ExternalObjectRef {
        ExternalObjectRef {
            kind: self.kind.clone(),
            name: self.name.into_rust_string(),
            namespace: self.namespace.into_rust_string(),
        }
    }

    pub fn from_external_object_ref(key: ExternalObjectRef) -> KubeObjectRef {
        KubeObjectRef {
            kind: key.kind.clone(),
            name: String::from_rust_string(key.name),
            namespace: String::from_rust_string(key.namespace),
        }
    }
}

verus! {

pub struct KubeObjectRef {
    pub kind: Kind,
    pub name: String,
    pub namespace: String,
}

impl View for KubeObjectRef {
    type V = ObjectRef;
    open spec fn view(&self) -> ObjectRef {
        ObjectRef {
            kind: self.kind,
            name: self.name@,
            namespace: self.namespace@,
        }
    }
}

impl std::clone::Clone for KubeObjectRef {
    fn clone(&self) -> (result: Self)
        ensures result == self
    {
        KubeObjectRef {
            kind: self.kind.clone(),
            name: self.name.clone(),
            namespace: self.namespace.clone(),
        }
    }
}

impl ApiResource {
    #[verifier(external_body)]
    pub fn kind(&self) -> (kind: Kind)
        ensures kind == self@.kind,
    {
        match self.as_kube_ref().kind.as_str() {
            "ConfigMap" => Kind::ConfigMapKind,
            "DaemonSet" => Kind::DaemonSetKind,
            "PersistentVolumeClaim" => Kind::PersistentVolumeClaimKind,
            "Pod" => Kind::PodKind,
            "Role" => Kind::RoleKind,
            "RoleBinding" => Kind::RoleBindingKind,
            "StatefulSet" => Kind::StatefulSetKind,
            "Service" => Kind::ServiceKind,
            "ServiceAccount" => Kind::ServiceAccountKind,
            "Secret" => Kind::SecretKind,
            _ => panic!(), // We assume the DynamicObject won't be a custom object
        }
    }
}

impl DynamicObject {
    #[verifier(external_body)]
    pub fn kind(&self) -> (kind: Kind)
        ensures kind == self@.kind,
    {
        if self.as_kube_ref().types.is_none() {
            panic!();
        }
        match self.as_kube_ref().types.as_ref().unwrap().kind.as_str() {
            "ConfigMap" => Kind::ConfigMapKind,
            "DaemonSet" => Kind::DaemonSetKind,
            "PersistentVolumeClaim" => Kind::PersistentVolumeClaimKind,
            "Pod" => Kind::PodKind,
            "Role" => Kind::RoleKind,
            "RoleBinding" => Kind::RoleBindingKind,
            "StatefulSet" => Kind::StatefulSetKind,
            "Service" => Kind::ServiceKind,
            "ServiceAccount" => Kind::ServiceAccountKind,
            "Secret" => Kind::SecretKind,
            _ => panic!(), // We assume the DynamicObject won't be a custom object
        }
    }

    #[verifier(external_body)]
    pub fn object_ref(&self) -> (object_ref: KubeObjectRef)
        requires
            self@.metadata.name.is_Some(),
            self@.metadata.namespace.is_Some(),
        ensures object_ref@ == self@.object_ref(),
    {
        KubeObjectRef {
            kind: self.kind(),
            name: self.metadata().name().unwrap(),
            namespace: self.metadata().namespace().unwrap(),
        }
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures self@ == old(self)@.set_namespace(namespace@),
    {
        self.as_kube_mut_ref().metadata.namespace = Some(namespace.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_resource_version(&mut self, resource_version: i64)
        ensures self@ == old(self)@.set_resource_version(resource_version as int),
    {
        self.as_kube_mut_ref().metadata.resource_version = Some(resource_version.to_string());
    }

    #[verifier(external_body)]
    pub fn set_uid(&mut self, uid: i64)
        ensures self@ == old(self)@.set_uid(uid as int),
    {
        self.as_kube_mut_ref().metadata.uid = Some(uid.to_string());
    }

    #[verifier(external_body)]
    pub fn unset_deletion_timestamp(&mut self)
        ensures self@ == old(self)@.unset_deletion_timestamp(),
    {
        self.as_kube_mut_ref().metadata.deletion_timestamp = None;
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, other: &DynamicObject)
        ensures self@ == old(self)@.set_spec(other@.spec)
    {
        self.as_kube_mut_ref().data = other.as_kube_ref().data.clone()
    }

    #[verifier(external_body)]
    pub fn set_status(&mut self, other: &DynamicObject)
        ensures self@ == old(self)@.set_status(other@.status)
    {}

    #[verifier(external_body)]
    pub fn set_default_status<K: ResourceView>(&mut self)
        ensures self@ == old(self)@.set_status(model::marshalled_default_status::<K>(self@.kind))
    {}
}

}
