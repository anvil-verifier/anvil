// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::EmptyAPI;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::v_replica_set_controller::{
    model::reconciler::*,
    proof::predicate::*,
    trusted::{spec_types::*, step::*},
};
use vstd::prelude::*;

verus! {

pub proof fn reconcile_eventually_terminates(spec: TempPred<VRSCluster>, vrs: VReplicaSetView)
    requires
        // spec.entails(always(lift_action(VRSCluster::next()))),
        // spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        // spec.entails(tla_forall(|i| VRSCluster::external_api_next().weak_fairness(i))),
        // spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        // spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        // spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        // spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        // spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        // spec.entails(always(lift_state(VRSCluster::no_pending_req_msg_at_reconcile_state(vrs.object_ref(), |s: VReplicaSetReconcileState| s.reconcile_step == VReplicaSetReconcileStep::Init)))),
    ensures spec.entails(true_pred().leads_to(lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref())))),
{
    assume(false);
}

}
