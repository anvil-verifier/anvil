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

pub struct ApiServerState {
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

pub enum ApiServerStep {
    HandleRequest,
}

pub struct ApiServerActionInput {
    pub recv: Option<Message>,
}

pub struct ApiServerActionOutput {
    pub send: Multiset<Message>
}

pub type ApiServerStateMachine = StateMachine<ApiServerState, ApiServerActionInput, ApiServerActionInput, ApiServerActionOutput, ApiServerStep>;

pub type ApiServerAction = Action<ApiServerState, ApiServerActionInput, ApiServerActionOutput>;

}
