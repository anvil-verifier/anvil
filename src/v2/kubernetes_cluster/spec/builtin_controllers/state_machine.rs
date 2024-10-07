use crate::kubernetes_cluster::spec::builtin_controllers::{garbage_collector::*, types::*};
use crate::state_machine::state_machine::*;
use vstd::prelude::*;

verus! {

pub open spec fn builtin_controllers() -> BuiltinControllersStateMachine {
    StateMachine {
        init: |s: ()| {
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
