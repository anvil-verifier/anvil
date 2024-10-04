// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;

use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub type ExternalLocalState = Value;

pub struct ExternalState {
    pub state: ExternalLocalState,
}

pub struct ExternalModel {
    pub init: spec_fn() -> ExternalLocalState,
    pub transition: spec_fn(ExternalRequest, ExternalLocalState, StoredState) -> (ExternalLocalState, ExternalResponse),
}

pub enum ExternalStep {
    HandleExternalRequest,
}

pub struct ExternalActionInput {
    pub recv: Option<Message>,
    pub resources: StoredState,
}

pub struct ExternalActionOutput {
    pub send: Multiset<Message>,
}

pub type ExternalStateMachine = StateMachine<ExternalState, ExternalActionInput, ExternalActionInput, ExternalActionOutput, ExternalStep>;

pub type ExternalAction = Action<ExternalState, ExternalActionInput, ExternalActionOutput>;

}
