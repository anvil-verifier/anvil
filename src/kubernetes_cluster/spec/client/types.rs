// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::resource::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct ClientState {}

pub enum Step<K> {
    CreateCustomResource(K),
    UpdateCustomResource(K),
    DeleteCustomResource(K),
}

pub struct ClientActionInput<K> {
    pub cr: K,
    pub rest_id_allocator: RestIdAllocator,
}

pub type ClientActionOutput<I, O> = (Multiset<Message<I, O>>, RestIdAllocator);

pub type ClientStateMachine<K, I, O> = StateMachine<ClientState, RestIdAllocator, ClientActionInput<K>, ClientActionOutput<I, O>, Step<K>>;

pub type ClientAction<K, I, O> = Action<ClientState, ClientActionInput<K>, ClientActionOutput<I, O>>;

}
