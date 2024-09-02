// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{api_method::*, common::*, dynamic::*};
use crate::kubernetes_cluster_v2::spec::{message::*, opaque::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;

use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub type ExternalLocalState = Opaque;

pub struct ExternalAPIState {
    pub state: ExternalLocalState,
    pub transition: spec_fn(ExternalMessageContent, ExternalLocalState, StoredState) -> (ExternalLocalState, ExternalMessageContent),
}

pub enum ExternalAPIStep {
    HandleExternalRequest,
}

pub struct ExternalAPIActionInput {
    pub recv: Option<Message>,
    pub resources: StoredState,
}

pub struct ExternalAPIActionOutput {
    pub send: Multiset<Message>,
}

pub type ExternalAPIStateMachine = StateMachine<ExternalAPIState, ExternalAPIActionInput, ExternalAPIActionInput, ExternalAPIActionOutput, ExternalAPIStep>;

pub type ExternalAPIAction = Action<ExternalAPIState, ExternalAPIActionInput, ExternalAPIActionOutput>;

}
