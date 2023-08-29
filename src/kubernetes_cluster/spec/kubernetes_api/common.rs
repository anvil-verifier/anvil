// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{api_method::*, common::*, dynamic::*};
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;

use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct KubernetesAPIState {
    pub resources: StoredState,
    pub uid_counter: Uid,
    pub resource_version_counter: ResourceVersion,
}

pub enum KubernetesAPIStep {
    HandleRequest,
}

pub struct KubernetesAPIActionInput<I, O> {
    pub recv: Option<Message<I, O>>,
}

pub struct KubernetesAPIActionOutput<I, O> {
    pub send: Multiset<Message<I, O>>
}

pub type KubernetesAPIStateMachine<I, O> = StateMachine<KubernetesAPIState, KubernetesAPIActionInput<I, O>, KubernetesAPIActionInput<I, O>, KubernetesAPIActionOutput<I, O>, KubernetesAPIStep>;

pub type KubernetesAPIAction<I, O> = Action<KubernetesAPIState, KubernetesAPIActionInput<I, O>, KubernetesAPIActionOutput<I, O>>;

}
