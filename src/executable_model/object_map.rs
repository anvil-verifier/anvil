use crate::executable_model::common::*;
use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::kubernetes_api_objects::spec::{
    common::{Kind, ObjectRef},
    dynamic::{DynamicObjectView, StoredState},
};
use vstd::prelude::*;
use vstd::string::*;

verus! {

// This is the exec version of the map used in crate::kubernetes_cluster::spec::api_server::types::ApiServerState
// for storing the cluster state (i.e., the k8s objects).
#[verifier(external_body)]
pub struct ObjectMap {
    inner: std::collections::BTreeMap<ExternalObjectRef, DynamicObject>,
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
        match self.inner.insert(key.into_external_object_ref(), value) {
            Some(old_v) => Some(old_v.clone()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn remove(&mut self, key: &KubeObjectRef) -> (old_v: Option<DynamicObject>)
        ensures
            self@ == old(self)@.remove(key@),
            old(self)@.contains_key(key@) == old_v.is_Some(),
            old_v.is_Some() ==> old_v.get_Some_0()@ == old(self)@[key@],
    {
        self.inner.remove(&key.clone().into_external_object_ref())
    }

    #[verifier(external_body)]
    pub fn get(&self, key: &KubeObjectRef) -> (v: Option<DynamicObject>)
        ensures
            self@.contains_key(key@) == v.is_Some(),
            v.is_Some() ==> v.get_Some_0()@ == self@[key@],
    {
        // I abuse clone() coz performance does not matter here
        match self.inner.get(&key.clone().into_external_object_ref()) {
            Some(v) => Some(v.clone()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn contains_key(&self, key: &KubeObjectRef) -> (b: bool)
        ensures self@.contains_key(key@) == b
    {
        self.inner.contains_key(&key.clone().into_external_object_ref())
    }

    #[verifier(external)]
    pub fn from_rust_map(inner: std::collections::BTreeMap<ExternalObjectRef, DynamicObject>) -> ObjectMap { ObjectMap { inner: inner } }

    #[verifier(external)]
    pub fn into_rust_map(self) -> std::collections::BTreeMap<ExternalObjectRef, DynamicObject> { self.inner }
}

}
