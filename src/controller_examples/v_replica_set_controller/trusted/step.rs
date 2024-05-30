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

impl View for VReplicaSetReconcileStep {
    type V = VReplicaSetReconcileStepView;

    open spec fn view(&self) -> VReplicaSetReconcileStepView {
        match self {
            VReplicaSetReconcileStep::Init => VReplicaSetReconcileStepView::Init,
            VReplicaSetReconcileStep::AfterListPods => VReplicaSetReconcileStepView::AfterListPods,
            VReplicaSetReconcileStep::AfterCreatePod(i) => VReplicaSetReconcileStepView::AfterCreatePod(*i as nat),
            VReplicaSetReconcileStep::AfterDeletePod(i) => VReplicaSetReconcileStepView::AfterDeletePod(*i as nat),
            VReplicaSetReconcileStep::Done => VReplicaSetReconcileStepView::Done,
            VReplicaSetReconcileStep::Error => VReplicaSetReconcileStepView::Error,
        }
    }
}

#[is_variant]
pub enum VReplicaSetReconcileStepView {
    Init,
    AfterListPods,
    AfterCreatePod(nat),
    AfterDeletePod(nat),
    Done,
    Error,
}


}
