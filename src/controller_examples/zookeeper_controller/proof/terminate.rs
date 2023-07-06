// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, error::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::{
    proof::{
        cluster::*,
        controller_runtime::*,
        controller_runtime_liveness::*,
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
        kubernetes_api::state_machine::{handle_request, transition_by_etcd, update_is_noop},
        message::*,
    },
};
use crate::reconciler::spec::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::zookeeper_controller::{
    common::ZookeeperReconcileStep,
    proof::{common::*, safety::*},
    spec::{reconciler::*, zookeepercluster::*},
};
use vstd::prelude::*;

verus! {

pub proof fn reconcile_eventually_terminates(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(no_pending_req_at_reconcile_init_state::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterUpdateStatefulSet))))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateStatefulSet))))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateHeadlessService))))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateClientService))))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateAdminServerService))))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateConfigMap))))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterGetStatefulSet))))),
    ensures
        spec.entails(
            true_pred().leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    let reconcile_idle = |s: ClusterState| { !s.reconcile_state_contains(zk.object_ref()) };
    lemma_reconcile_error_leads_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk.object_ref());
    lemma_reconcile_done_leads_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk.object_ref());
    temp_pred_equality(
        lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::Done))),
        lift_state(reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref()))
    );
    temp_pred_equality(
        lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::Error))),
        lift_state(reconciler_reconcile_error::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref()))
    );
    lemma_from_some_state_to_one_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk, zookeeper_reconcile_state(ZookeeperReconcileStep::AfterUpdateStatefulSet), zookeeper_reconcile_state(ZookeeperReconcileStep::Done));
    lemma_from_some_state_to_one_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk, zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateStatefulSet), zookeeper_reconcile_state(ZookeeperReconcileStep::Done));

    lemma_from_some_state_to_three_next_states_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, zk,
        zookeeper_reconcile_state(ZookeeperReconcileStep::AfterGetStatefulSet),
        zookeeper_reconcile_state(ZookeeperReconcileStep::AfterUpdateStatefulSet),
        zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateStatefulSet),
        zookeeper_reconcile_state(ZookeeperReconcileStep::Error)
    );

    lemma_from_some_state_to_one_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk, zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateConfigMap), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterGetStatefulSet));
    lemma_from_some_state_to_one_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk, zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateAdminServerService), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateConfigMap));
    lemma_from_some_state_to_one_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk, zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateClientService), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateAdminServerService));
    lemma_from_some_state_to_one_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk, zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateHeadlessService), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateClientService));
    lemma_from_init_state_to_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk, zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateHeadlessService));
    valid_implies_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));
    temp_pred_equality(
        true_pred(),
        lift_state(reconcile_idle)
        .or(lift_state(reconciler_reconcile_error::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())))
        .or(lift_state(at_reconcile_state(zk.object_ref(), ZookeeperReconciler::reconcile_init_state())))
        .or(lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateHeadlessService))))
        .or(lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateClientService))))
        .or(lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateAdminServerService))))
        .or(lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateConfigMap))))
        .or(lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterGetStatefulSet))))
        .or(lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateStatefulSet))))
        .or(lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterUpdateStatefulSet))))
        .or(lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::Done))))
    );
    or_leads_to_combine_n!(
        spec,
        lift_state(reconcile_idle),
        lift_state(reconciler_reconcile_error::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())),
        lift_state(at_reconcile_state(zk.object_ref(), ZookeeperReconciler::reconcile_init_state())),
        lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateHeadlessService))),
        lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateClientService))),
        lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateAdminServerService))),
        lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateConfigMap))),
        lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterGetStatefulSet))),
        lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateStatefulSet))),
        lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterUpdateStatefulSet))),
        lift_state(at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::Done)));
        lift_state(reconcile_idle)
    );
}

}
