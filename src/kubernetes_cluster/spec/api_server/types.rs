// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{api_method::*, common::*, dynamic::*};
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;

use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct APIServerState {
    pub resources: StoredState,
    pub uid_counter: Uid,
    pub resource_version_counter: ResourceVersion,
    pub stable_resources: Set<ObjectRef>,
}

pub enum APIServerStep {
    HandleRequest,
}

pub struct APIServerActionInput<I, O> {
    pub recv: Option<Message<I, O>>,
}

pub struct APIServerActionOutput<I, O> {
    pub send: Multiset<Message<I, O>>
}

pub type APIServerStateMachine<I, O> = StateMachine<APIServerState, APIServerActionInput<I, O>, APIServerActionInput<I, O>, APIServerActionOutput<I, O>, APIServerStep>;

pub type APIServerAction<I, O> = Action<APIServerState, APIServerActionInput<I, O>, APIServerActionOutput<I, O>>;

}
