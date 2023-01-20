// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::kubernetes_cluster::spec::common::*;
use crate::pervasive::{map::*, option::*, result::*, seq::*, set::*, string::*};
use crate::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct KubernetesAPIState {
    pub resources: Map<ResourceKey, ResourceObj>,
}

pub enum KubernetesAPIStep {
    HandleRequest,
}

pub type KubernetesAPIActionInput = Option<Message>;

pub type KubernetesAPIStateMachine = StateMachine<KubernetesAPIState, KubernetesAPIActionInput, KubernetesAPIActionInput, Set<Message>, KubernetesAPIStep>;

pub type KubernetesAPIAction = Action<KubernetesAPIState, KubernetesAPIActionInput, Set<Message>>;

pub type KubernetesAPIActionResult = ActionResult<KubernetesAPIState, Set<Message>>;

}
