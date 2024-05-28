use vstd::prelude::*;
use vstd::string::*;

verus! {

#[verifier(external_body)]
pub struct StringMap {
    inner: std::collections::BTreeMap<std::string::String, std::string::String>,
}

impl StringMap {
    pub spec fn view(&self) -> Map<Seq<char>, Seq<char>>;

    #[verifier(external_body)]
    pub fn new() -> (m: Self)
        ensures m@ == Map::<Seq<char>, Seq<char>>::empty(),
    {
        StringMap { inner: std::collections::BTreeMap::new() }
    }

    pub fn empty() -> (m: Self)
        ensures m@ == Map::<Seq<char>, Seq<char>>::empty(),
    {
        StringMap::new()
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
        StringMap { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn insert(&mut self, key: String, value: String) -> (old_v: Option<String>)
        ensures
            self@ == old(self)@.insert(key@, value@),
            old(self)@.contains_key(key@) == old_v.is_Some(),
            old_v.is_Some() ==> old_v.get_Some_0()@ == old(self)@[key@],
    {
        match self.inner.insert(key.into_rust_string(), value.into_rust_string()) {
            Some(old_v) => Some(String::from_rust_string(old_v)),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn get_uncloned<'a>(&'a self, key: &String) -> (v: Option<StrSlice<'a>>)
        ensures
            self@.contains_key(key@) == v.is_Some(),
            v.is_Some() ==> v.get_Some_0()@ == self@[key@],
    {
        match self.inner.get(key.as_rust_string_ref()) {
            Some(v) => Some(v),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn get(&self, key: &String) -> (v: Option<String>)
        ensures
            self@.contains_key(key@) == v.is_Some(),
            v.is_Some() ==> v.get_Some_0()@ == self@[key@],
    {
        match self.inner.get(key.as_rust_string_ref()) {
            Some(v) => Some(String::from_rust_string(v.to_string())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn extend(&mut self, m2: StringMap)
        ensures self@ == old(self)@.union_prefer_right(m2@),
    {
        self.inner.extend(m2.into_rust_map())
    }

    #[verifier(external_body)]
    pub fn keys(&self) -> (keys: Vec<String>)
        ensures keys@.map_values(|k: String| k@) == self@.dom().to_seq(),
    {
        self.inner.keys().cloned().map(|key| String::from_rust_string(key)).collect()
    }

    #[verifier(external)]
    pub fn from_rust_map(inner: std::collections::BTreeMap<std::string::String, std::string::String>) -> StringMap { StringMap { inner: inner } }

    #[verifier(external)]
    pub fn into_rust_map(self) -> std::collections::BTreeMap<std::string::String, std::string::String> { self.inner }
}

}
