// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{common::*, resource::*};
use crate::kubernetes_cluster::spec::{
    cluster::Cluster, controller::common::*, controller::controller_runtime::*, external_api::*,
    message::*,
};
use crate::reconciler::spec::reconciler::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn form_external_input(input: E::Input, id: nat) -> ExternalComm<E::Input, E::Output> {
    ExternalComm::Input(input, id)
}

pub open spec fn init_controller_state() -> ControllerState<K, E, R> {
    ControllerState {
        ongoing_reconciles: Map::empty(),
        scheduled_reconciles: Map::empty(),
    }
}

pub open spec fn controller() -> ControllerStateMachine<K, E, R> {
    StateMachine {
        init: |s: ControllerState<K, E, R>| {
            s == Self::init_controller_state()
        },
        actions: set![
            Self::run_scheduled_reconcile(),
            Self::continue_reconcile(),
            Self::end_reconcile()
        ],
        step_to_action: |step: ControllerStep| {
            match step {
                ControllerStep::RunScheduledReconcile => Self::run_scheduled_reconcile(),
                ControllerStep::ContinueReconcile => Self::continue_reconcile(),
                ControllerStep::EndReconcile => Self::end_reconcile(),
            }
        },
        action_input: |step: ControllerStep, input: ControllerActionInput<E>| {
            input
        }
    }
}

}

}
