// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, dynamic::*};
use crate::kubernetes_cluster::spec::{channel::*, message::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;
use vstd::{map::*, multiset::*, option::*, result::*, seq::*, string::*};

verus! {

pub type EtcdState = Map<ObjectRef, DynamicObjectView>;

pub struct KubernetesAPIState {
    pub resource_version_counter: nat,
    pub resources: EtcdState,
}

pub enum KubernetesAPIStep {
    HandleRequest,
}

pub struct KubernetesAPIActionInput {
    pub recv: Option<Message>,
    pub chan_manager: ChannelManager,
}

pub type KubernetesAPIActionOutput = (Multiset<Message>, ChannelManager);

pub type KubernetesAPIStateMachine = StateMachine<KubernetesAPIState, KubernetesAPIActionInput, KubernetesAPIActionInput, KubernetesAPIActionOutput, KubernetesAPIStep>;

pub type KubernetesAPIAction = Action<KubernetesAPIState, KubernetesAPIActionInput, KubernetesAPIActionOutput>;

}
