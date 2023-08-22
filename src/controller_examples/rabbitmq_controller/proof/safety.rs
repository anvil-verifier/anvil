// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::common::*,
    spec::{rabbitmqcluster::*, reconciler::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

spec fn stateful_set_not_scaled_down(rabbitmq: RabbitmqClusterView) -> ActionPred<RMQCluster> {
    |s: RMQCluster, s_prime: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        &&& s.resource_key_exists(sts_key)
        &&& s_prime.resource_key_exists(sts_key)
        ==> StatefulSetView::from_dynamic_object(s_prime.resource_obj_of(sts_key)).get_Ok_0().spec.get_Some_0().replicas.get_Some_0()
            >= StatefulSetView::from_dynamic_object(s.resource_obj_of(sts_key)).get_Ok_0().spec.get_Some_0().replicas.get_Some_0()
    }
}

#[verifier(external_body)]
proof fn stateful_set_never_scaled_down_for_all()
    ensures
        forall |rabbitmq: RabbitmqClusterView|
            cluster_spec().entails(lift_action(#[trigger] stateful_set_not_scaled_down(rabbitmq))),
{}

}
