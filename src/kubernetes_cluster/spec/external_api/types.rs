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

pub struct ExternalAPIState<E: ExternalAPI> {
    pub state: E::State,
}

pub enum ExternalAPIStep {
    HandleExternalRequest,
}

pub struct ExternalAPIActionInput<E: ExternalAPI> {
    pub recv: Option<MsgType<E>>,
    pub resources: StoredState,
}

pub struct ExternalAPIActionOutput<E: ExternalAPI> {
    pub send: Multiset<MsgType<E>>,
}

pub type ExternalAPIStateMachine<E> = StateMachine<ExternalAPIState<E>, ExternalAPIActionInput<E>, ExternalAPIActionInput<E>, ExternalAPIActionOutput<E>, ExternalAPIStep>;

pub type ExternalAPIAction<E> = Action<ExternalAPIState<E>, ExternalAPIActionInput<E>, ExternalAPIActionOutput<E>>;

}
