// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, resource::*};
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

pub open spec fn controller<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>() -> ControllerStateMachine<K, T> {
    StateMachine {
        init: |s: ControllerState<K, T>| {
            s == init_controller_state::<K, T>()
        },
        actions: set![
            run_scheduled_reconcile::<K, T, ReconcilerType>(),
            continue_reconcile::<K, T, ReconcilerType>(),
            end_reconcile::<K, T, ReconcilerType>()
        ],
        step_to_action: |step: ControllerStep| {
            match step {
                ControllerStep::RunScheduledReconcile => run_scheduled_reconcile::<K, T, ReconcilerType>(),
                ControllerStep::ContinueReconcile => continue_reconcile::<K, T, ReconcilerType>(),
                ControllerStep::EndReconcile => end_reconcile::<K, T, ReconcilerType>(),
            }
        },
        action_input: |step: ControllerStep, input: ControllerActionInput| {
            input
        }
    }
}

}
