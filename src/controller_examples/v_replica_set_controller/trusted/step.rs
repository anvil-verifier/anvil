// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum VReplicaSetReconcileStep {
    Init,
    AfterListPods,
    AfterCreatePod(usize),
    AfterDeletePod(usize),
    Done,
    Error,
}

impl std::marker::Copy for VReplicaSetReconcileStep {}

impl std::clone::Clone for VReplicaSetReconcileStep {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

}
