// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{
    common::*, controller::common::*, controller::controller_runtime::*, reconciler::*,
};
use crate::pervasive::{map::*, option::*, seq::*, set::*, string::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn controller<T>(reconciler: Reconciler<T>) -> ControllerStateMachine<T> {
    StateMachine {
        init: |s: ControllerState<T>| {
            s == ControllerState::<T> {
                req_id: 0,
                ongoing_reconciles: Map::empty(),
                scheduled_reconciles: Set::empty(),
            }
        },
        actions: set![trigger_reconcile(reconciler), run_scheduled_reconcile(reconciler), continue_reconcile(reconciler), end_reconcile(reconciler)],
        step_to_action: |step: ControllerStep| {
            match step {
                ControllerStep::TriggerReconcile => trigger_reconcile(reconciler),
                ControllerStep::RunScheduledReconcile => run_scheduled_reconcile(reconciler),
                ControllerStep::ContinueReconcile => continue_reconcile(reconciler),
                ControllerStep::EndReconcile => end_reconcile(reconciler),
            }
        },
        action_input: |step: ControllerStep, input: ControllerActionInput| {
            input
        }
    }
}

}
