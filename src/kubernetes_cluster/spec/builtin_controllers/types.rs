// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, dynamic::*};
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub type StoredState = Map<ObjectRef, DynamicObjectView>;

pub struct BuiltinControllersState {}

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
    pub resources: StoredState,
    pub rest_id_allocator: RestIdAllocator,
}

pub struct BuiltinControllersActionOutput<I, O> {
    pub send: Multiset<Message<I, O>>,
    pub rest_id_allocator: RestIdAllocator,
}

pub type BuiltinControllersStateMachine<I, O> = StateMachine<BuiltinControllersState,
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionOutput<I, O>,
                                            BuiltinControllersStep>;

pub type BuiltinControllersAction<I, O> = Action<BuiltinControllersState,
                                        BuiltinControllersActionInput,
                                        BuiltinControllersActionOutput<I, O>>;

}
