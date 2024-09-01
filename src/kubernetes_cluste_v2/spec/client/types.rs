// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{dynamic::*, resource::*};
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct ClientState {}

pub enum Step {
    CreateCustomResource(DynamicObjectView),
    UpdateCustomResource(DynamicObjectView),
    DeleteCustomResource(DynamicObjectView),
}

pub struct ClientActionInput {
    pub obj: DynamicObjectView,
    pub rest_id_allocator: RestIdAllocator,
}

pub struct ClientActionOutput<I, O> {
    pub send: Multiset<Message<I, O>>,
    pub rest_id_allocator: RestIdAllocator,
}

pub type ClientStateMachine<I, O> = StateMachine<ClientState, RestIdAllocator, ClientActionInput, ClientActionOutput<I, O>, Step>;

pub type ClientAction<I, O> = Action<ClientState, ClientActionInput, ClientActionOutput<I, O>>;

}
