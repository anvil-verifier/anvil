// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;

#[allow(unused_imports)]
#[macro_use]
use crate::pervasive::{*, option::Option, map::*};
#[allow(unused_imports)]
use crate::common::ObjectKey;

#[verifier(external_body)]
pub struct Dict<#[verifier(maybe_negative)] K, #[verifier(strictly_positive)] V>
{
    pub dict: std::collections::HashMap<K, V>,
}

impl<K: std::cmp::Eq + std::hash::Hash, V> Dict<K, V> {
    fndecl!(pub fn view(&self) -> Map<K, V>);

    #[verifier(external_body)]
    pub fn new() -> Self {
        ensures(|d: Self| equal(d.view(), Map::empty()));

        Dict { dict: std::collections::HashMap::new() }
    }

    pub fn empty() -> Self {
        ensures(|d: Self| equal(d.view(), Map::empty()));

        Dict::new()
    }

    #[verifier(external_body)]
    pub fn insert(&mut self, key: K, value: V) -> crate::pervasive::option::Option<V> {
        ensures(|r: crate::pervasive::option::Option<V>| [
            equal(r, if old(self).view().dom().contains(key) {
                crate::pervasive::option::Option::Some(old(self).view().index(key))
            } else {
                crate::pervasive::option::Option::None
            }),
            equal(self.view(), old(self).view().insert(key, value)),
        ]);

        match self.dict.insert(key, value) {
            Some(v) => crate::pervasive::option::Option::Some(v),
            None => crate::pervasive::option::Option::None,
        }
    }

    #[verifier(external_body)]
    pub fn remove(&mut self, key: &K) -> crate::pervasive::option::Option<V> {
        ensures(|r: crate::pervasive::option::Option<V>| [
            equal(r, if old(self).view().dom().contains(*key) {
                crate::pervasive::option::Option::Some(old(self).view().index(*key))
            } else {
                crate::pervasive::option::Option::None
            }),
            equal(self.view(), old(self).view().remove(*key)),
        ]);

        match self.dict.remove(key) {
            Some(v) => crate::pervasive::option::Option::Some(v),
            None => crate::pervasive::option::Option::None,
        }
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn contains(&self, key: &K) -> bool {
        ensures(|r: bool| r == self.view().dom().contains(*key));

        match self.dict.get(key) {
            Some(v) => true,
            None => false,
        }
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn index(&self, key: &K) -> &V {
        requires(self.view().dom().contains(*key));
        ensures(|r: &V| equal(*r, self.view().index(*key)));

        match self.dict.get(key) {
            Some(v) => &v,
            None => panic!("Never reach here"),
        }
    }

    // TODO: len() cannot pass Verus due to some type incompatibility issue; need to revisit later
    // #[verifier(external_body)]
    // #[verifier(autoview)]
    // pub fn len(&self) -> usize {
    //     ensures(|l: usize| l == self.view().dom().len());

    //     self.dict.len()
    // }
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_dict_ext_equal<V>(m1: Dict<ObjectKey, V>, m2: Dict<ObjectKey, V>) {
    ensures(equal(m1, m2) == equal(m1.view(), m2.view()));
}

