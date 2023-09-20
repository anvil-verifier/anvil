// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::prelude::*;
use crate::kubernetes_cluster::spec::{
    builtin_controllers::{garbage_collector::*, types::*},
    cluster::Cluster,
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn builtin_controllers() -> BuiltinControllersStateMachine<E::Input, E::Output> {
    StateMachine {
        init: |s: BuiltinControllersState| {
            true
        },
        actions: set![Self::run_garbage_collector()],
        step_to_action: |step: BuiltinControllersStep| {
            match step {
                BuiltinControllersStep::RunGarbageCollector => Self::run_garbage_collector(),
            }
        },
        action_input: |step: BuiltinControllersStep, input: BuiltinControllersActionInput| {
            input
        }
    }
}

}

}
