use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct StringMap {
    inner: std::collections::BTreeMap<std::string::String, std::string::String>,
}

impl View for StringMap {
    type V = Map<Seq<char>, Seq<char>>;

    uninterp spec fn view(&self) -> Map<Seq<char>, Seq<char>>;
}

impl DeepView for StringMap {
    type V = Map<Seq<char>, Seq<char>>;

    open spec fn deep_view(&self) -> Map<Seq<char>, Seq<char>> {
        self@
    }
}

impl StringMap {
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
    pub fn contains_key(&self, key: &str) -> (res: bool)
        ensures res == self@.contains_key(key@),
    {
        self.inner.contains_key(key)
    }

    #[verifier(external_body)]
    pub fn insert(&mut self, key: String, value: String) -> (old_v: Option<String>)
        ensures
            self@ == old(self)@.insert(key@, value@),
            old(self)@.contains_key(key@) == old_v is Some,
            old_v is Some ==> old_v->0@ == old(self)@[key@],
    {
        self.inner.insert(key, value)
    }

    #[verifier(external_body)]
    pub fn remove(&mut self, key: &String) -> (old_v: Option<String>)
        ensures
            self@ == old(self)@.remove(key@),
            old(self)@.contains_key(key@) == old_v is Some,
            old_v is Some ==> old_v->0@ == old(self)@[key@],
    {
        self.inner.remove(key)
    }

    #[verifier(external_body)]
    pub fn get_uncloned(&self, key: &String) -> (v: Option<&String>)
        ensures
            self@.contains_key(key@) == v is Some,
            v is Some ==> v->0@ == self@[key@],
    {
        self.inner.get(key)
    }

    #[verifier(external_body)]
    pub fn get(&self, key: &String) -> (v: Option<String>)
        ensures
            self@.contains_key(key@) == v is Some,
            v is Some ==> v->0@ == self@[key@],
    {
        match self.inner.get(key) {
            Some(v) => Some(v.to_string()),
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
        self.inner.keys().cloned().collect()
    }

    #[verifier(external)]
    pub fn from_rust_map(inner: std::collections::BTreeMap<std::string::String, std::string::String>) -> StringMap { StringMap { inner: inner } }

    #[verifier(external)]
    pub fn into_rust_map(self) -> std::collections::BTreeMap<std::string::String, std::string::String> { self.inner }
}

}
