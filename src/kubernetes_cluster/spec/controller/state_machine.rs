// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{common::*, resource::*};
use crate::kubernetes_cluster::Cluster;
use crate::kubernetes_cluster::spec::{
    controller::common::*, controller::controller_runtime::*, message::*,
};
use crate::reconciler::spec::reconciler::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn controller() -> ControllerStateMachine<K, E, R> {
    StateMachine {
        init: |s: ControllerState<K, E, R>| {
            s == init_controller_state::<K, E, R>()
        },
        actions: set![
            run_scheduled_reconcile::<K, E, R>(),
            continue_reconcile::<K, E, R>(),
            end_reconcile::<K, E, R>()
        ],
        step_to_action: |step: ControllerStep| {
            match step {
                ControllerStep::RunScheduledReconcile => run_scheduled_reconcile::<K, E, R>(),
                ControllerStep::ContinueReconcile => continue_reconcile::<K, E, R>(),
                ControllerStep::EndReconcile => end_reconcile::<K, E, R>(),
            }
        },
        action_input: |step: ControllerStep, input: ControllerActionInput<E>| {
            input
        }
    }
}

}

}
