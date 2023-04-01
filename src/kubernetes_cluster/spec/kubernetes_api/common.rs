// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, object::*};
use crate::kubernetes_cluster::spec::{channel::*, message::*};
use crate::pervasive::{map::*, multiset::*, option::*, result::*, seq::*, string::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub type EtcdState = Map<ObjectRef, KubernetesObject>;

pub struct KubernetesAPIState {
    pub chan_manager: ChannelManager,
    pub resources: EtcdState,
}

pub enum KubernetesAPIStep {
    HandleRequest,
}

pub type KubernetesAPIActionInput = Option<Message>;

pub type KubernetesAPIStateMachine = StateMachine<KubernetesAPIState, KubernetesAPIActionInput, KubernetesAPIActionInput, Multiset<Message>, KubernetesAPIStep>;

pub type KubernetesAPIAction = Action<KubernetesAPIState, KubernetesAPIActionInput, Multiset<Message>>;

pub type KubernetesAPIActionResult = ActionResult<KubernetesAPIState, Multiset<Message>>;

}
