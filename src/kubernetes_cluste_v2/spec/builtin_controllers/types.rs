// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{api_method::*, common::*, dynamic::*};
use crate::kubernetes_cluster::spec::api_server::types::ApiServerState;
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub type StoredState = Map<ObjectRef, DynamicObjectView>;

#[is_variant]
pub enum BuiltinControllersStep {
    RunGarbageCollector,
    RunStatefulSetController,
    RunDaemonSetController,
    RunStabilizer,
}

#[is_variant]
pub enum BuiltinControllerChoice {
    GarbageCollector,
    StatefulSetController{ready_replicas: int},
    DaemonSetController{number_ready: int},
    Stabilizer,
}

pub struct BuiltinControllersActionInput {
    pub choice: BuiltinControllerChoice,
    pub key: ObjectRef,
    pub rest_id_allocator: RestIdAllocator,
}

pub struct BuiltinControllersActionOutput<I, O> {
    pub send: Multiset<Message<I, O>>,
    pub rest_id_allocator: RestIdAllocator,
}

pub type BuiltinControllersStateMachine<I, O> = StateMachine<ApiServerState,
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionOutput<I, O>,
                                            BuiltinControllersStep>;

pub type BuiltinControllersAction<I, O> = Action<ApiServerState,
                                        BuiltinControllersActionInput,
                                        BuiltinControllersActionOutput<I, O>>;

}
