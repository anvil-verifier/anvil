// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::{
    proof::{
        cluster::*,
        controller_runtime_liveness::{
            lemma_pre_leads_to_post_by_controller,
            lemma_pre_leads_to_post_by_schedule_controller_reconcile,
        },
        controller_runtime_safety,
        kubernetes_api_liveness::{
            lemma_pre_leads_to_post_by_kubernetes_api, no_req_before_rest_id_is_in_flight,
        },
        kubernetes_api_safety,
    },
    spec::{
        cluster::*,
        controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::controller,
        kubernetes_api::state_machine::{
            handle_create_request, handle_get_request, handle_request, update_is_noop,
        },
        message::*,
    },
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::zookeeper_controller::{
    proof::{common::*, safety},
    spec::{reconciler::*, zookeepercluster::*},
};
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub proof fn reconcile_eventually_terminates(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
    ensures
        spec.entails(
            true_pred().leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{}

}
