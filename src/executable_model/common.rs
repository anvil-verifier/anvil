use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::kubernetes_api_objects::spec::{
    common::{Kind, ObjectRef},
    dynamic::{DynamicObjectView, StoredState},
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
    pub fn into_object_map_key(self) -> ExternalObjectRef {
        ExternalObjectRef {
            kind: self.kind.clone(),
            name: self.name.into_rust_string(),
            namespace: self.namespace.into_rust_string(),
        }
    }

    pub fn from_object_map_key(key: ExternalObjectRef) -> KubeObjectRef {
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

}
