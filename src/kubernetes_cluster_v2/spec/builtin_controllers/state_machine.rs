// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster_v2::spec::{
    api_server::types::ApiServerState,
    builtin_controllers::{garbage_collector::*, types::*},
    message::*,
};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use vstd::{multiset::*, prelude::*};

verus! {


pub open spec fn builtin_controllers() -> BuiltinControllersStateMachine {
    StateMachine {
        init: |s: ApiServerState| {
            true
        },
        actions: set![
            run_garbage_collector(),
        ],
        step_to_action: |step: BuiltinControllersStep| {
            match step {
                BuiltinControllersStep::RunGarbageCollector => run_garbage_collector(),
            }
        },
        action_input: |step: BuiltinControllersStep, input: BuiltinControllersActionInput| {
            input
        }
    }
}

}
