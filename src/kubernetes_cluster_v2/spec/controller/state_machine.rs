// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster_v2::spec::{
    controller::controller_runtime::*, controller::types::*, message::*,
};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub open spec fn controller(reconcile: Reconcile, cr_kind: Kind) -> ControllerStateMachine {
    StateMachine {
        init: |s: ControllerState| {
            &&& s.ongoing_reconciles == Map::<ObjectRef, OngoingReconcile>::empty()
            &&& s.scheduled_reconciles == Map::<ObjectRef, DynamicObjectView>::empty()
            &&& s.reconcile == reconcile
            &&& s.cr_kind == cr_kind
        },
        actions: set![
            run_scheduled_reconcile(),
            continue_reconcile(),
            end_reconcile()
        ],
        step_to_action: |step: ControllerStep| {
            match step {
                ControllerStep::RunScheduledReconcile => run_scheduled_reconcile(),
                ControllerStep::ContinueReconcile => continue_reconcile(),
                ControllerStep::EndReconcile => end_reconcile(),
            }
        },
        action_input: |step: ControllerStep, input: ControllerActionInput| {
            input
        }
    }
}

}
