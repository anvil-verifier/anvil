// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#![allow(unused_imports)]
use crate::apis::*;
use crate::common::*;
use crate::kubernetes_core_resources::*;
use builtin::*;
use builtin_macros::*;

verus! {

#[derive(Structural, PartialEq, Eq)]
pub enum CustomReconcileStep {
    CheckIfCMGExists,
    CheckIfCMExists,
    CreateCM1,
    CreateCM2,
}

#[derive(PartialEq, Eq)]
pub struct ConfigMapGeneratorL {
    pub metadata: ObjectMetaL,
}

impl ConfigMapGeneratorL {
    pub open spec fn key(&self) -> ObjectKey {
        ObjectKey{
            object_type: StringL::ConfigMapGenerator,
            namespace: self.metadata.namespace,
            name: self.metadata.name,
        }
    }
}

#[derive(PartialEq, Eq)]
pub enum CustomResourceObject {
    ConfigMapGenerator(ConfigMapGeneratorL),
}

impl CustomResourceObject {
    pub open spec fn key(&self) -> ObjectKey {
        match *self {
            CustomResourceObject::ConfigMapGenerator(cmg) => cmg.key(),
        }
    }
}

}
