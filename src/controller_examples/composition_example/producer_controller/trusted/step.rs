// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum ProducerReconcileStep {
    Init,
    Done,
    Error,
}

impl std::marker::Copy for ProducerReconcileStep {}

impl std::clone::Clone for ProducerReconcileStep {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

impl View for ProducerReconcileStep {
    type V = ProducerReconcileStepView;

    open spec fn view(&self) -> ProducerReconcileStepView {
        match self {
            ProducerReconcileStep::Init => ProducerReconcileStepView::Init,
            ProducerReconcileStep::Done => ProducerReconcileStepView::Done,
            ProducerReconcileStep::Error => ProducerReconcileStepView::Error,
        }
    }
}

#[is_variant]
pub enum ProducerReconcileStepView {
    Init,
    Done,
    Error,
}


}
