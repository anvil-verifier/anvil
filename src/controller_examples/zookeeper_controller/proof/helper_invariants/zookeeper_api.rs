// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, error::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use crate::zookeeper_controller::{
    common::*,
    proof::{predicate::*, resource::*},
    spec::{reconciler::*, types::*, zookeeper_api::*},
};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub open spec fn stateful_set_has_at_least_one_replica(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = get_request(SubResource::StatefulSet, zookeeper).key;
        s.resources().contains_key(key) ==> {
            &&& StatefulSetView::unmarshal(s.resources()[key]).is_Ok()
            &&& StatefulSetView::unmarshal(s.resources()[key]).get_Ok_0().spec.is_Some()
            &&& StatefulSetView::unmarshal(s.resources()[key]).get_Ok_0().spec.get_Some_0().replicas.is_Some()
            &&& StatefulSetView::unmarshal(s.resources()[key]).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() > 0
        }
    }
}

pub open spec fn every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = zookeeper.object_ref();
        forall |msg: ZKMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& zk_set_data_request_msg(zookeeper)(msg)
        } ==> {
            &&& at_zk_step(key, ZookeeperReconcileStep::AfterUpdateZKNode)(s)
            &&& ZKCluster::pending_k8s_api_req_msg_is(s, key, msg)
        }
    }
}

}
