// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::types::ApiServerState,
    builtin_controllers::{
        garbage_collector::*, stabilizer::*, stateful_set_controller::*, types::*,
    },
    cluster::Cluster,
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: CustomResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn builtin_controllers() -> BuiltinControllersStateMachine<E::Input, E::Output> {
    StateMachine {
        init: |s: ApiServerState| {
            true
        },
        actions: set![
            Self::run_garbage_collector(),
            Self::run_stateful_set_controller(),
            Self::run_daemon_set_controller(),
            Self::run_stabilizer()
        ],
        step_to_action: |step: BuiltinControllersStep| {
            match step {
                BuiltinControllersStep::RunGarbageCollector => Self::run_garbage_collector(),
                BuiltinControllersStep::RunStatefulSetController => Self::run_stateful_set_controller(),
                BuiltinControllersStep::RunDaemonSetController => Self::run_daemon_set_controller(),
                BuiltinControllersStep::RunStabilizer => Self::run_stabilizer(),
            }
        },
        action_input: |step: BuiltinControllersStep, input: BuiltinControllersActionInput| {
            input
        }
    }
}

}

}
