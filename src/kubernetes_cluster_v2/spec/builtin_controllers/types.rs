// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster_v2::spec::{api_server::types::ApiServerState, message::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use vstd::{multiset::*, prelude::*};

verus! {

#[is_variant]
pub enum BuiltinControllersStep {
    RunGarbageCollector,
}

#[is_variant]
pub enum BuiltinControllerChoice {
    GarbageCollector,
}

pub struct BuiltinControllersActionInput {
    pub choice: BuiltinControllerChoice,
    pub key: ObjectRef,
    pub rest_id_allocator: RestIdAllocator,
}

pub struct BuiltinControllersActionOutput {
    pub send: Multiset<Message>,
    pub rest_id_allocator: RestIdAllocator,
}

pub type BuiltinControllersStateMachine = StateMachine<ApiServerState,
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionOutput,
                                            BuiltinControllersStep>;

pub type BuiltinControllersAction = Action<ApiServerState,
                                        BuiltinControllersActionInput,
                                        BuiltinControllersActionOutput>;

}
