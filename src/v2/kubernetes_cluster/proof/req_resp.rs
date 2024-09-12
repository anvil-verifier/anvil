// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::v2::kubernetes_cluster::spec::{
    api_server::state_machine::transition_by_etcd, cluster_state_machine::*, message::*,
};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn object_in_ok_get_response_has_smaller_rv_than_etcd() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            s.in_flight().contains(msg)
            && #[trigger] is_ok_get_response_msg()(msg)
            ==> msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.is_Some()
                && msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() < s.api_server.resource_version_counter
    }
}

}

}
