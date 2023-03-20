// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, object::*};
use crate::kubernetes_cluster::spec::{common::*, distributed_system::*, reconciler::Reconciler};
use crate::pervasive::seq::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn added_event_msg_to_controller(res: KubernetesObject) -> Message {
    form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg_content(res))
}

}
