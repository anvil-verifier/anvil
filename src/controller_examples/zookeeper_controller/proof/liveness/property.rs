// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::zookeeper_controller::{
    common::*,
    proof::{predicate::*, resource::*},
    spec::{reconciler::*, types::*},
};
use vstd::prelude::*;

verus! {

pub open spec fn liveness(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(lift_state(desired_state_is(zookeeper))).leads_to(always(lift_state(current_state_matches(zookeeper))))
}

pub open spec fn current_state_matches(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        forall |sub_resource: SubResource|
            #[trigger] resource_state_matches(sub_resource, zookeeper, s.resources())
    }
}

}
