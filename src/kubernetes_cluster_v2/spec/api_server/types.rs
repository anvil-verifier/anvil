// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{api_method::*, common::*, dynamic::*, marshal::*};
use crate::kubernetes_cluster_v2::spec::message::*;
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

pub struct InstalledTypes {
    pub unmarshallable_spec: spec_fn(DynamicObjectView) -> bool,
    pub unmarshallable_status: spec_fn(DynamicObjectView) -> bool,
    pub valid_object: spec_fn(DynamicObjectView) -> bool,
    pub valid_transition: spec_fn(DynamicObjectView, DynamicObjectView) -> bool,
    pub marshalled_default_status: spec_fn(Kind) -> Value,
}

pub enum APIServerStep {
    HandleRequest,
}

pub struct APIServerActionInput {
    pub recv: Option<Message>,
}

pub struct APIServerActionOutput {
    pub send: Multiset<Message>
}

pub type APIServerStateMachine = StateMachine<APIServerState, APIServerActionInput, APIServerActionInput, APIServerActionOutput, APIServerStep>;

pub type APIServerAction = Action<APIServerState, APIServerActionInput, APIServerActionOutput>;

}
