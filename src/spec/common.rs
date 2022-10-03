// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#![allow(unused_imports)]
use crate::pervasive::option::*;
use builtin::*;
use builtin_macros::*;

verus! {

impl std::cmp::PartialEq for Option<StringL> {
    #[verifier(external)]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Option::Some(a), Option::Some(b)) => a == b,
            (Option::None, Option::None) => true,
            _ => false,
        }
    }
}

impl std::cmp::Eq for Option<StringL> {}

#[derive(Structural, Copy, PartialEq, Eq)]
pub enum StringL {
    ConfigMap1,
    ConfigMap2,
    Default,
    DefaultConfigMap1,
    ConfigMap,
    ConfigMapGenerator,
    MyConfigMapGenerator,
    Pod,
    MyPod,
}

impl Clone for StringL {
    #[verifier(external)]
    fn clone(&self) -> StringL {
        *self
    }
}

impl std::hash::Hash for StringL {
    #[verifier(external)]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            StringL::ConfigMap1 => 1.hash(state),
            StringL::ConfigMap2 => 2.hash(state),
            StringL::Default => 3.hash(state),
            StringL::DefaultConfigMap1 => 4.hash(state),
            StringL::ConfigMap => 5.hash(state),
            StringL::ConfigMapGenerator => 6.hash(state),
            StringL::MyConfigMapGenerator => 7.hash(state),
            StringL::Pod => 8.hash(state),
            StringL::MyPod => 9.hash(state),
        }
    }
}

#[derive(Structural, Copy, PartialEq, Eq)]
pub struct ObjectKey {
    pub object_type: StringL,
    pub namespace: StringL,
    pub name: StringL,
}

impl Clone for ObjectKey {
    #[verifier(external)]
    fn clone(&self) -> ObjectKey {
        *self
    }
}

impl std::hash::Hash for ObjectKey {
    #[verifier(external)]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.object_type.hash(state);
        self.namespace.hash(state);
        self.name.hash(state);
    }
}

}
