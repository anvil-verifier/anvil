// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vstatefulset_controller::trusted::spec_types::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::rabbitmq_controller::model::reconciler::RabbitmqMaker;
use crate::rabbitmq_controller::trusted::{maker::*, spec_types::*, step::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::int_to_string_view;
use vstd::prelude::*;

verus! {

pub open spec fn safety_theorem(cluster: Cluster) -> bool {
    cluster_spec_without_wf(cluster).entails(tla_forall(|rabbitmq: RabbitmqClusterView| safety(rabbitmq)))
}

pub open spec fn cluster_spec_without_wf(cluster: Cluster) -> TempPred<ClusterState> {
    lift_state(cluster.init()).and(always(lift_action(cluster.next())))
}

pub open spec fn safety(rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(lift_action(stateful_set_not_scaled_down(rabbitmq)))
}

// To prove the safety property about stateful set, we need to first specify what the property is.
//
// Previously, we planned to use Message to describe the possible update/deletion/creation actions, and also specify the
// relevant properties. However, it is better not to include Message in the description the high-level safety property
// because Message is just a tool and a detail of the system. For update action, one way to circumvent using Message is
// to talk about the previous and current state: an object being updated means that it exists in both states but changes
// in current state.
pub open spec fn stateful_set_not_scaled_down(rabbitmq: RabbitmqClusterView) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        let sts_key = RabbitmqMaker::make_stateful_set_key(rabbitmq);
        s.resources().contains_key(sts_key)
        && s_prime.resources().contains_key(sts_key)
        ==> replicas_of_stateful_set(s_prime.resources()[sts_key]) >= replicas_of_stateful_set(s.resources()[sts_key])
    }
}

pub open spec fn replicas_of_stateful_set(obj: DynamicObjectView) -> int
    recommends obj.kind is CustomResourceKind,
{
    VStatefulSetView::unmarshal(obj)->Ok_0.spec.replicas->0
}

}
