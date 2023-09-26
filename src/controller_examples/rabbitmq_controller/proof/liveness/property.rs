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
use crate::rabbitmq_controller::{
    common::*,
    proof::resource::*,
    spec::{reconciler::*, types::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub type RMQCluster = Cluster<RabbitmqClusterView, EmptyAPI, RabbitmqReconciler>;

spec fn liveness(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    always(lift_state(RMQCluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(current_state_matches(rabbitmq))))
}

pub open spec fn current_state_matches(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |sub_resource: SubResource| 
            #[trigger] resource_state_matches(sub_resource, rabbitmq, s.resources())
    }
}

}
