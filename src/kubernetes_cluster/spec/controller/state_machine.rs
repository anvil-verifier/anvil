// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, dynamic::*};
use crate::kubernetes_cluster::spec::{
    channel::*, controller::common::*, controller::controller_runtime::*, message::*,
};
use crate::reconciler::spec::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;
use vstd::{map::*, option::*, seq::*, set::*, string::*};

verus! {

pub open spec fn controller<K: ResourceView, T>(reconciler: Reconciler<K, T>) -> ControllerStateMachine<T> {
    StateMachine {
        init: |s: ControllerState<T>| {
            s == init_controller_state::<T>()
        },
        actions: set![
            run_scheduled_reconcile(reconciler),
            continue_reconcile(reconciler),
            end_reconcile(reconciler)
        ],
        step_to_action: |step: ControllerStep| {
            match step {
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
