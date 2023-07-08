// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    controller::controller_runtime::{continue_reconcile, end_reconcile, run_scheduled_reconcile},
    message::*,
};
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::{rabbitmqcluster::*, reconciler::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub type ClusterState = State<RabbitmqClusterView, RabbitmqReconcileState>;

pub open spec fn cluster_spec() -> TempPred<ClusterState> {
    sm_spec::<RabbitmqClusterView, RabbitmqReconcileState, RabbitmqReconciler>()
}

pub open spec fn rabbitmq_reconcile_state(step: RabbitmqReconcileStep) -> RabbitmqReconcileState {
    RabbitmqReconcileState {
        reconcile_step: step
    }
}

pub open spec fn at_rabbitmq_step(key: ObjectRef, step: RabbitmqReconcileStep) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: ClusterState| {
        &&& s.reconcile_state_contains(key)
        &&& s.reconcile_state_of(key).local_state.reconcile_step == step
    }
}

pub open spec fn at_rabbitmq_step_with_zk(zk: RabbitmqClusterView, step: RabbitmqReconcileStep) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.reconcile_state_contains(zk.object_ref())
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.object_ref() == zk.object_ref()
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.spec == zk.spec
        &&& s.reconcile_state_of(zk.object_ref()).local_state.reconcile_step == step
    }
}

}
