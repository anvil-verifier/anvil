use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::string::*;

verus! {

// This is the exec version of the set used in crate::kubernetes_cluster::spec::api_server::types::ApiServerState
// for storing the key of the stable objects.
#[verifier(external_body)]
pub struct StringSet {
    inner: std::collections::BTreeSet<std::string::String>,
}

impl StringSet {
    pub spec fn view(&self) -> Set::<StringView>;

    #[verifier(external_body)]
    pub fn new() -> (m: Self)
        ensures m@ == Set::<StringView>::empty(),
    {
        StringSet { inner: std::collections::BTreeSet::new() }
    }

    pub fn empty() -> (m: Self)
        ensures m@ == Set::<StringView>::empty(),
    {
        StringSet::new()
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (m: Self)
        ensures m@ == self@,
    {
        StringSet { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn subset_of(&self, other: &Self) -> (ret: bool)
        ensures ret == self@.subset_of(other@)
    {
        self.as_rust_set_ref().is_subset(other.as_rust_set_ref())
    }

    #[verifier(external)]
    pub fn from_rust_set(inner: std::collections::BTreeSet<std::string::String>) -> StringSet { StringSet { inner: inner } }

    #[verifier(external)]
    pub fn into_rust_set(self) -> std::collections::BTreeSet<std::string::String> { self.inner }

    #[verifier(external)]
    pub fn as_rust_set_ref(&self) -> &std::collections::BTreeSet<std::string::String> { &self.inner }
}

}
