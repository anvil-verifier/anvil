use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::kubernetes_api_objects::spec::{
    common::{Kind, ObjectRef},
    dynamic::{DynamicObjectView, StoredState},
};
use vstd::prelude::*;
use vstd::string::*;

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct ObjectMapKey {
    pub kind: Kind,
    pub name: std::string::String,
    pub namespace: std::string::String,
}

impl KubeObjectRef {
    pub fn to_object_map_key(self) -> ObjectMapKey {
        ObjectMapKey {
            kind: self.kind.clone(),
            name: self.name.into_rust_string(),
            namespace: self.namespace.into_rust_string(),
        }
    }

    pub fn from_object_map_key(key: ObjectMapKey) -> KubeObjectRef {
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

#[verifier(external_body)]
pub struct ObjectMap {
    inner: std::collections::BTreeMap<ObjectMapKey, DynamicObject>,
}

impl ObjectMap {
    pub spec fn view(&self) -> StoredState;

    #[verifier(external_body)]
    pub fn new() -> (m: Self)
        ensures m@ == StoredState::empty(),
    {
        ObjectMap { inner: std::collections::BTreeMap::new() }
    }

    pub fn empty() -> (m: Self)
        ensures m@ == StoredState::empty(),
    {
        ObjectMap::new()
    }

    #[verifier(external_body)]
    pub fn len(&self) -> (len: usize)
        ensures len == self@.len(),
    {
        self.inner.len()
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (m: Self)
        ensures m@ == self@,
    {
        ObjectMap { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn insert(&mut self, key: KubeObjectRef, value: DynamicObject) -> (old_v: Option<DynamicObject>)
        ensures
            self@ == old(self)@.insert(key@, value@),
            old(self)@.contains_key(key@) == old_v.is_Some(),
            old_v.is_Some() ==> old_v.get_Some_0()@ == old(self)@[key@],
    {
        match self.inner.insert(key.to_object_map_key(), value) {
            Some(old_v) => Some(old_v.clone()),
            None => None,
        }
    }

    #[verifier(external)]
    pub fn from_rust_map(inner: std::collections::BTreeMap<ObjectMapKey, DynamicObject>) -> ObjectMap { ObjectMap { inner: inner } }

    #[verifier(external)]
    pub fn into_rust_map(self) -> std::collections::BTreeMap<ObjectMapKey, DynamicObject> { self.inner }
}

}
