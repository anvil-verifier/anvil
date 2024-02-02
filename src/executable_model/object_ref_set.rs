use crate::executable_model::common::*;
use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::kubernetes_api_objects::spec::common::{Kind, ObjectRef};
use vstd::prelude::*;
use vstd::string::*;

verus! {

// This is the exec version of the set used in crate::kubernetes_cluster::spec::api_server::types::ApiServerState
// for storing the key of the stable objects.
#[verifier(external_body)]
pub struct ObjectRefSet {
    inner: std::collections::BTreeSet<ExternalObjectRef>,
}

impl ObjectRefSet {
    pub spec fn view(&self) -> Set::<ObjectRef>;

    #[verifier(external_body)]
    pub fn new() -> (m: Self)
        ensures m@ == Set::<ObjectRef>::empty(),
    {
        ObjectRefSet { inner: std::collections::BTreeSet::new() }
    }

    pub fn empty() -> (m: Self)
        ensures m@ == Set::<ObjectRef>::empty(),
    {
        ObjectRefSet::new()
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
        ObjectRefSet { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn remove(&mut self, key: &KubeObjectRef) -> (b: bool)
        ensures
            self@ == old(self)@.remove(key@),
            b == old(self)@.contains(key@),
    {
        self.inner.remove(&key.clone().into_external_object_ref())
    }

    #[verifier(external)]
    pub fn from_rust_set(inner: std::collections::BTreeSet<ExternalObjectRef>) -> ObjectRefSet { ObjectRefSet { inner: inner } }

    #[verifier(external)]
    pub fn into_rust_set(self) -> std::collections::BTreeSet<ExternalObjectRef> { self.inner }
}

}
