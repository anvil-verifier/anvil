// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{api_server::types::APIServerState, message::*};
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
    pub rpc_id_allocator: RPCIdAllocator,
    pub resources: StoredState,
}

pub struct BuiltinControllersActionOutput {
    pub send: Multiset<Message>,
    pub rpc_id_allocator: RPCIdAllocator,
}

pub type BuiltinControllersStateMachine = StateMachine<(),
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionOutput,
                                            BuiltinControllersStep>;

pub type BuiltinControllersAction = Action<(),
                                        BuiltinControllersActionInput,
                                        BuiltinControllersActionOutput>;

}
