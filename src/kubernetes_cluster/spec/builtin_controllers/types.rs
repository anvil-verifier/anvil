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

pub enum BuiltinControllersStep {
    Reconcile,
}

pub enum BuiltinControllerChoice {
    GarbageCollector,
}

pub struct BuiltinControllersActionInput {
    pub choice: BuiltinControllerChoice,
    pub key: ObjectRef,
    pub resources: StoredState,
    pub rest_id_allocator: RestIdAllocator,
}

pub type BuiltinControllersActionOutput = (Multiset<Message>, RestIdAllocator);

pub type BuiltinControllersStateMachine = StateMachine<BuiltinControllersState,
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionOutput,
                                            BuiltinControllersStep>;

pub type BuiltinControllersAction = Action<BuiltinControllersState,
                                        BuiltinControllersActionInput,
                                        BuiltinControllersActionOutput>;

}
