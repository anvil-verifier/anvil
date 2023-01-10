// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::kubernetes_cluster::spec::{
    common::*, controller::common::*, controller::controller_runtime::*,
    controller::simple_controller::*,
};
use crate::pervasive::{map::*, option::*, seq::*, set::*, string::*};
use crate::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn controller() -> ControllerStateMachine {
    StateMachine {
        init: |s: ControllerState| {
            s === ControllerState {
                ongoing_reconciles: Map::empty(),
                scheduled_reconciles: Set::empty(),
            }
        },
        actions: set![trigger_reconcile(), run_scheduled_reconcile(), continue_reconcile(), end_reconcile()],
        step_to_action: |step: ControllerStep| {
            match step {
                ControllerStep::TriggerReconcile => trigger_reconcile(),
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
