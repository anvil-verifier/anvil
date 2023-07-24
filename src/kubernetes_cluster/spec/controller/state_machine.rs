// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    controller::common::*, controller::controller_runtime::*, message::*,
};
use crate::reconciler::spec::reconciler::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub open spec fn controller<K: ResourceView, R: Reconciler<K>>() -> ControllerStateMachine<K, R> {
    StateMachine {
        init: |s: ControllerState<K, R>| {
            s == init_controller_state::<K, R>()
        },
        actions: set![
            run_scheduled_reconcile::<K, R>(),
            continue_reconcile::<K, R>(),
            end_reconcile::<K, R>()
        ],
        step_to_action: |step: ControllerStep| {
            match step {
                ControllerStep::RunScheduledReconcile => run_scheduled_reconcile::<K, R>(),
                ControllerStep::ContinueReconcile => continue_reconcile::<K, R>(),
                ControllerStep::EndReconcile => end_reconcile::<K, R>(),
            }
        },
        action_input: |step: ControllerStep, input: ControllerActionInput| {
            input
        }
    }
}

}
