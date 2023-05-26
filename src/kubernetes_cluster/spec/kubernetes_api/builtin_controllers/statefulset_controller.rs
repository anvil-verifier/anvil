// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{channel::*, kubernetes_api::common::*, message::*};
use builtin::*;
use builtin_macros::*;
use vstd::{map::*, multiset::*, option::*, result::*, seq::*};

verus! {

// TODO: complete the statefulset controller spec
pub open spec fn transition_by_statefulset_controller(event: WatchEvent, s: KubernetesAPIState, chan_manager: ChannelManager) -> (ChannelManager, Multiset<Message>) {
    let src = HostId::KubernetesAPI;
    let dst = HostId::KubernetesAPI;

    (chan_manager, Multiset::empty())
}

}
