// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, error::*, object_meta::*,
    persistent_volume_claim::*, pod::*, resource::*, role::*, role_binding::*, secret::*,
    service::*, service_account::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::*, cluster::Cluster, message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn garbage_collector_precondition(input: BuiltinControllersActionInput, s: BuiltinControllersState) -> bool {
    input.resources.dom().contains(input.key)
}

pub open spec fn garbage_collector_transition(
    input: BuiltinControllersActionInput, s: BuiltinControllersState
) -> (BuiltinControllersState, BuiltinControllersActionOutput) {
    (s, (Multiset::empty(), input.rest_id_allocator))
}

pub open spec fn reconcile() -> BuiltinControllersAction {
    Action {
        precondition: |input: BuiltinControllersActionInput, s: BuiltinControllersState| {
            match input.choice {
                BuiltinControllerChoice::GarbageCollector => Self::garbage_collector_precondition(input, s)
            }
        },
        transition: |input: BuiltinControllersActionInput, s: BuiltinControllersState| {
            match input.choice {
                BuiltinControllerChoice::GarbageCollector => Self::garbage_collector_transition(input, s)
            }
        },
    }
}

pub open spec fn builtin_controllers() -> BuiltinControllersStateMachine {
    StateMachine {
        init: |s: BuiltinControllersState| {
            true
        },
        actions: set![Self::reconcile()],
        step_to_action: |step: BuiltinControllersStep| {
            match step {
                BuiltinControllersStep::Reconcile => Self::reconcile(),
            }
        },
        action_input: |step: BuiltinControllersStep, input: BuiltinControllersActionInput| {
            input
        }
    }
}

}

}
