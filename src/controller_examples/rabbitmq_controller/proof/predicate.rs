// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::proof::controller_runtime::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::{reconciler::*, resource::*, types::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub type RMQStep = Step<RMQMessage>;

pub type RMQCluster = Cluster<RabbitmqClusterView, EmptyAPI, RabbitmqReconciler>;

pub type RMQMessage = Message<EmptyTypeView, EmptyTypeView>;

pub open spec fn cluster_spec() -> TempPred<RMQCluster> {
    RMQCluster::sm_spec()
}

pub open spec fn at_rabbitmq_step(key: ObjectRef, step: RabbitmqReconcileStep) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: RMQCluster| {
        &&& s.ongoing_reconciles().contains_key(key)
        &&& s.ongoing_reconciles()[key].local_state.reconcile_step == step
    }
}

pub open spec fn at_step_closure(step: RabbitmqReconcileStep) -> FnSpec(RabbitmqReconcileState) -> bool {
    |s: RabbitmqReconcileState| s.reconcile_step == step
}

}