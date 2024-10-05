// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum VDeploymentReconcileStep {
    Init,
    More,
    Done,
    Error,
}

impl std::marker::Copy for VDeploymentReconcileStep {}

impl std::clone::Clone for VDeploymentReconcileStep {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

}
