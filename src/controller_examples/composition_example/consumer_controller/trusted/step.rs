// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum ConsumerReconcileStep {
    Init,
    AfterGetProducer,
    AfterCreateProducer,
    AfterGetPod,
    AfterUpdatePod,
    Done,
    Error,
}

impl std::marker::Copy for ConsumerReconcileStep {}

impl std::clone::Clone for ConsumerReconcileStep {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

impl View for ConsumerReconcileStep {
    type V = ConsumerReconcileStepView;

    open spec fn view(&self) -> ConsumerReconcileStepView {
        match self {
            ConsumerReconcileStep::Init => ConsumerReconcileStepView::Init,
            ConsumerReconcileStep::AfterGetProducer => ConsumerReconcileStepView::AfterGetProducer,
            ConsumerReconcileStep::AfterCreateProducer => ConsumerReconcileStepView::AfterCreateProducer,
            ConsumerReconcileStep::AfterGetPod => ConsumerReconcileStepView::AfterGetPod,
            ConsumerReconcileStep::AfterUpdatePod => ConsumerReconcileStepView::AfterUpdatePod,
            ConsumerReconcileStep::Done => ConsumerReconcileStepView::Done,
            ConsumerReconcileStep::Error => ConsumerReconcileStepView::Error,
        }
    }
}

#[is_variant]
pub enum ConsumerReconcileStepView {
    Init,
    AfterGetProducer,
    AfterCreateProducer,
    AfterGetPod,
    AfterUpdatePod,
    Done,
    Error,
}


}
