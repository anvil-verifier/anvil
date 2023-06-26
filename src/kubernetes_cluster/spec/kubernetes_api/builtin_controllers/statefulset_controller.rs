// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{kubernetes_api::common::*, message::*};
use builtin::*;
use builtin_macros::*;
use vstd::{multiset::*, prelude::*};

verus! {

// TODO: complete the statefulset controller spec
pub open spec fn transition_by_statefulset_controller(event: WatchEvent, s: KubernetesAPIState, rest_id_allocator: RestIdAllocator) -> (RestIdAllocator, Multiset<Message>) {
    let src = HostId::KubernetesAPI;
    let dst = HostId::KubernetesAPI;

    (rest_id_allocator, Multiset::empty())
}

}
