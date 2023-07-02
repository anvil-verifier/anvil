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
        controller_runtime_liveness::{
            lemma_pre_leads_to_post_by_controller,
            lemma_pre_leads_to_post_by_schedule_controller_reconcile,
            lemma_reconcile_done_leads_to_reconcile_idle,
            lemma_reconcile_error_leads_to_reconcile_idle,
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
        kubernetes_api::state_machine::{handle_request, transition_by_etcd, update_is_noop},
        message::*,
    },
};
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
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(
            true_pred().leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    let reconcile_idle = |s: ClusterState| { !s.reconcile_state_contains(zk.object_ref()) };
    lemma_from_init_step_to_reconcile_idle(spec, zk);
    lemma_from_after_create_headless_service_step_to_reconcile_idle(spec, zk);
    lemma_from_after_create_client_service_step_to_reconcile_idle(spec, zk);
    lemma_from_after_create_admin_server_service_step_to_reconcile_idle(spec, zk);
    lemma_from_after_create_config_map_step_to_reconcile_idle(spec, zk);
    lemma_from_after_get_stateful_set_step_to_reconcile_idle(spec, zk);
    lemma_from_after_create_stateful_set_step_to_reconcile_idle(spec, zk);
    lemma_from_after_update_stateful_set_step_to_reconcile_idle(spec, zk);
    lemma_reconcile_error_leads_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk.object_ref());
    lemma_reconcile_done_leads_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk.object_ref());
    valid_implies_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));
    temp_pred_equality(
        true_pred(),
        lift_state(reconcile_idle)
        .or(lift_state(reconciler_reconcile_error::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())))
        .or(lift_state(reconciler_reconcile_init::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())))
        .or(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))
        .or(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))
        .or(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))
        .or(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))
        .or(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))
        .or(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))
        .or(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))
        .or(lift_state(reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())))
    );
    or_leads_to_combine_n!(
        spec,
        lift_state(reconcile_idle),
        lift_state(reconciler_reconcile_error::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())),
        lift_state(reconciler_reconcile_init::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)),
        lift_state(reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref()));
        lift_state(reconcile_idle)
    );
}

pub proof fn lemma_from_after_update_stateful_set_step_to_reconcile_idle(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(
            lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet))
                .leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    let at_after_update_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight = |s: ClusterState| {
        at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)(s)
        && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        && is_controller_request(s.pending_req_of(zk.object_ref()))
        && (s.message_in_flight(s.pending_req_of(zk.object_ref()))
        || exists |resp_msg: Message| {
            #[trigger] s.message_in_flight(resp_msg)
            && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        })
    };
    temp_pred_equality::<ClusterState>(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)), lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)).implies(lift_state(at_after_update_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight)));
    implies_to_leads_to::<ClusterState>(spec, lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)), lift_state(at_after_update_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight));

    let req_in_flight = at_after_update_stateful_set_step_and_pending_req_in_flight(zk.object_ref());
    let resp_in_flight = at_after_update_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
    // To show after_update_sts_step ~> done_step
    // Use or_leads_to_combine after discussing the two cases:
    // 1. resp_in_flight ~> done_step
    // 2. req_in_flight ~> resp_in_flight ~> done_step
    let done_step = reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
    lemma_from_at_after_update_stateful_set_step_and_resp_matches_pending_req_in_flight_to_done_step(spec, zk);
    lemma_from_at_after_update_stateful_set_step_and_pending_req_in_flight_to_done_step(spec, zk);
    or_leads_to_combine(spec, req_in_flight, resp_in_flight, done_step);
    temp_pred_equality::<ClusterState>(
        lift_state(req_in_flight).or(lift_state(resp_in_flight)),
        lift_state(at_after_update_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight)
    );

    lemma_reconcile_done_leads_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk.object_ref());
    leads_to_trans_n!(
        spec,
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)),
        lift_state(at_after_update_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight),
        lift_state(done_step),
        lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref()))
    );
}

pub proof fn lemma_from_after_create_stateful_set_step_to_reconcile_idle(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(
            lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet))
                .leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    let at_after_create_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight = |s: ClusterState| {
        at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)(s)
        && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        && is_controller_request(s.pending_req_of(zk.object_ref()))
        && (s.message_in_flight(s.pending_req_of(zk.object_ref()))
        || exists |resp_msg: Message| {
            #[trigger] s.message_in_flight(resp_msg)
            && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        })
    };
    temp_pred_equality::<ClusterState>(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)), lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)).implies(lift_state(at_after_create_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight)));
    implies_to_leads_to::<ClusterState>(spec, lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)), lift_state(at_after_create_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight));

    let req_in_flight = at_after_create_stateful_set_step_and_pending_req_in_flight(zk.object_ref());
    let resp_in_flight = at_after_create_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
    // To show after_update_sts_step ~> done_step
    // Use or_leads_to_combine after discussing the two cases:
    // 1. resp_in_flight ~> done_step
    // 2. req_in_flight ~> resp_in_flight ~> done_step
    let done_step = reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
    lemma_from_at_after_create_stateful_set_step_and_resp_matches_pending_req_in_flight_to_done_step(spec, zk);
    lemma_from_at_after_create_stateful_set_step_and_pending_req_in_flight_to_done_step(spec, zk);
    or_leads_to_combine(spec, req_in_flight, resp_in_flight, done_step);
    temp_pred_equality::<ClusterState>(
        lift_state(req_in_flight).or(lift_state(resp_in_flight)),
        lift_state(at_after_create_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight)
    );

    lemma_reconcile_done_leads_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk.object_ref());
    leads_to_trans_n!(
        spec,
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)),
        lift_state(at_after_create_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight),
        lift_state(done_step),
        lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref()))
    );
}

pub proof fn lemma_from_after_get_stateful_set_step_to_reconcile_idle(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(
            lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet))
                .leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    let at_after_get_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight = |s: ClusterState| {
        at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)(s)
        && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        && is_controller_request(s.pending_req_of(zk.object_ref()))
        && (s.message_in_flight(s.pending_req_of(zk.object_ref()))
        || exists |resp_msg: Message| {
            #[trigger] s.message_in_flight(resp_msg)
            && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        })
    };
    temp_pred_equality::<ClusterState>(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)), lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)).implies(lift_state(at_after_get_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight)));
    implies_to_leads_to::<ClusterState>(spec, lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)), lift_state(at_after_get_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight));

    let req_in_flight = at_after_get_stateful_set_step_and_pending_req_in_flight(zk.object_ref());
    let resp_in_flight = at_after_get_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref());

    let done_step = reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
    lemma_from_at_after_get_stateful_set_step_and_resp_matches_pending_req_in_flight_to_reconcile_idle(spec, zk);
    lemma_from_at_after_get_stateful_set_step_and_pending_req_in_flight_to_reconcile_idle(spec, zk);
    or_leads_to_combine(spec, req_in_flight, resp_in_flight, |s: ClusterState| !s.reconcile_state_contains(zk.object_ref()));
    temp_pred_equality(lift_state(req_in_flight).or(lift_state(resp_in_flight)), lift_state(at_after_get_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight));

    leads_to_trans_n!(
        spec,
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)),
        lift_state(at_after_get_stateful_set_step_and_pending_req_in_flight_or_resp_in_flight),
        lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref()))
    );
}

pub proof fn lemma_from_after_create_config_map_step_to_reconcile_idle(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(
            lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap))
                .leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    let at_after_create_config_map_step_and_pending_req_in_flight_or_resp_in_flight = |s: ClusterState| {
        at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)(s)
        && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        && is_controller_request(s.pending_req_of(zk.object_ref()))
        && (s.message_in_flight(s.pending_req_of(zk.object_ref()))
        || exists |resp_msg: Message| {
            #[trigger] s.message_in_flight(resp_msg)
            && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        })
    };
    temp_pred_equality::<ClusterState>(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)), lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)).implies(lift_state(at_after_create_config_map_step_and_pending_req_in_flight_or_resp_in_flight)));
    implies_to_leads_to::<ClusterState>(spec, lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)), lift_state(at_after_create_config_map_step_and_pending_req_in_flight_or_resp_in_flight));

    let req_in_flight = at_after_create_config_map_step_and_pending_req_in_flight(zk.object_ref());
    let resp_in_flight = at_after_create_config_map_step_and_resp_matches_pending_req_in_flight(zk.object_ref());

    let done_step = reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
    lemma_from_at_after_create_config_map_step_and_resp_matches_pending_req_in_flight_to_after_get_stateful_set_step(spec, zk);
    lemma_from_at_after_create_config_map_step_and_pending_req_in_flight_to_after_get_stateful_set_step(spec, zk);
    or_leads_to_combine(spec, req_in_flight, resp_in_flight, at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet));
    temp_pred_equality::<ClusterState>(
        lift_state(req_in_flight).or(lift_state(resp_in_flight)),
        lift_state(at_after_create_config_map_step_and_pending_req_in_flight_or_resp_in_flight)
    );

    lemma_from_after_get_stateful_set_step_to_reconcile_idle(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)),
        lift_state(at_after_create_config_map_step_and_pending_req_in_flight_or_resp_in_flight),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)),
        lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref()))
    );
}

pub proof fn lemma_from_after_create_admin_server_service_step_to_reconcile_idle(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(
            lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService))
                .leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    let at_after_create_admin_server_service_step_and_pending_req_in_flight_or_resp_in_flight = |s: ClusterState| {
        at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)(s)
        && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        && is_controller_request(s.pending_req_of(zk.object_ref()))
        && (s.message_in_flight(s.pending_req_of(zk.object_ref()))
        || exists |resp_msg: Message| {
            #[trigger] s.message_in_flight(resp_msg)
            && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        })
    };
    temp_pred_equality::<ClusterState>(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)), lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)).implies(lift_state(at_after_create_admin_server_service_step_and_pending_req_in_flight_or_resp_in_flight)));
    implies_to_leads_to::<ClusterState>(spec, lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)), lift_state(at_after_create_admin_server_service_step_and_pending_req_in_flight_or_resp_in_flight));

    let req_in_flight = at_after_create_admin_server_service_step_and_pending_req_in_flight(zk.object_ref());
    let resp_in_flight = at_after_create_admin_server_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref());

    let done_step = reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
    lemma_from_at_after_create_admin_server_service_step_and_resp_matches_pending_req_in_flight_to_after_create_config_map_step(spec, zk);
    lemma_from_at_after_create_admin_server_service_step_and_pending_req_in_flight_to_after_create_config_map_step(spec, zk);
    or_leads_to_combine(spec, req_in_flight, resp_in_flight, at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap));
    temp_pred_equality::<ClusterState>(
        lift_state(req_in_flight).or(lift_state(resp_in_flight)),
        lift_state(at_after_create_admin_server_service_step_and_pending_req_in_flight_or_resp_in_flight)
    );

    lemma_from_after_create_config_map_step_to_reconcile_idle(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)),
        lift_state(at_after_create_admin_server_service_step_and_pending_req_in_flight_or_resp_in_flight),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)),
        lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref()))
    );
}

pub proof fn lemma_from_after_create_client_service_step_to_reconcile_idle(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(
            lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService))
                .leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    let at_after_create_client_service_step_and_pending_req_in_flight_or_resp_in_flight = |s: ClusterState| {
        at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)(s)
        && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        && is_controller_request(s.pending_req_of(zk.object_ref()))
        && (s.message_in_flight(s.pending_req_of(zk.object_ref()))
        || exists |resp_msg: Message| {
            #[trigger] s.message_in_flight(resp_msg)
            && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        })
    };
    temp_pred_equality::<ClusterState>(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)), lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)).implies(lift_state(at_after_create_client_service_step_and_pending_req_in_flight_or_resp_in_flight)));
    implies_to_leads_to::<ClusterState>(spec, lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)), lift_state(at_after_create_client_service_step_and_pending_req_in_flight_or_resp_in_flight));

    let req_in_flight = at_after_create_client_service_step_and_pending_req_in_flight(zk.object_ref());
    let resp_in_flight = at_after_create_client_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
    // To show after_update_sts_step ~> done_step
    // Use or_leads_to_combine after discussing the two cases:
    // 1. resp_in_flight ~> done_step
    // 2. req_in_flight ~> resp_in_flight ~> done_step
    let done_step = reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
    lemma_from_at_after_create_client_service_step_and_resp_matches_pending_req_in_flight_to_after_create_admin_server_service_step(spec, zk);
    lemma_from_at_after_create_client_service_step_and_pending_req_in_flight_to_after_create_admin_server_service_step(spec, zk);
    or_leads_to_combine(spec, req_in_flight, resp_in_flight, at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService));
    temp_pred_equality::<ClusterState>(
        lift_state(req_in_flight).or(lift_state(resp_in_flight)),
        lift_state(at_after_create_client_service_step_and_pending_req_in_flight_or_resp_in_flight)
    );

    lemma_from_after_create_admin_server_service_step_to_reconcile_idle(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)),
        lift_state(at_after_create_client_service_step_and_pending_req_in_flight_or_resp_in_flight),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)),
        lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref()))
    );
}

pub proof fn lemma_from_after_create_headless_service_step_to_reconcile_idle(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(
            lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService))
                .leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    let at_after_create_headless_service_step_and_pending_req_in_flight_or_resp_in_flight = |s: ClusterState| {
        at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)(s)
        && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        && is_controller_request(s.pending_req_of(zk.object_ref()))
        && (s.message_in_flight(s.pending_req_of(zk.object_ref()))
        || exists |resp_msg: Message| {
            #[trigger] s.message_in_flight(resp_msg)
            && resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        })
    };
    temp_pred_equality::<ClusterState>(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)), lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)).implies(lift_state(at_after_create_headless_service_step_and_pending_req_in_flight_or_resp_in_flight)));
    implies_to_leads_to::<ClusterState>(spec, lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)), lift_state(at_after_create_headless_service_step_and_pending_req_in_flight_or_resp_in_flight));

    let req_in_flight = at_after_create_headless_service_step_and_pending_req_in_flight(zk.object_ref());
    let resp_in_flight = at_after_create_headless_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref());

    lemma_from_at_after_create_headless_service_step_and_resp_matches_pending_req_in_flight_to_after_create_client_service_step(spec, zk);
    lemma_from_at_after_create_headless_service_step_and_pending_req_in_flight_to_after_create_client_service_step(spec, zk);
    or_leads_to_combine(spec, req_in_flight, resp_in_flight, at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService));
    temp_pred_equality::<ClusterState>(
        lift_state(req_in_flight).or(lift_state(resp_in_flight)),
        lift_state(at_after_create_headless_service_step_and_pending_req_in_flight_or_resp_in_flight)
    );

    lemma_from_after_create_client_service_step_to_reconcile_idle(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)),
        lift_state(at_after_create_headless_service_step_and_pending_req_in_flight_or_resp_in_flight),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)),
        lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref()))
    );
}

pub proof fn lemma_from_init_step_to_reconcile_idle(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(
            lift_state(reconciler_reconcile_init::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref()))
                .leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    temp_pred_equality::<ClusterState>(
        lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())),
        lift_state(reconciler_reconcile_init::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref()))
        .implies(lift_state(reconciler_init_and_no_pending_req::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())))
    );
    implies_to_leads_to(
        spec,
        lift_state(reconciler_reconcile_init::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())),
        lift_state(reconciler_init_and_no_pending_req::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref()))
    );
    let stronger_next = |s, s_prime: ClusterState| {
        next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        && !s.crash_enabled
    };
    strengthen_next::<ClusterState>(
        spec, next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(), crash_disabled(), stronger_next
    );
    lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, (Option::None, Option::Some(zk.object_ref())),
        stronger_next,
        continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(),
        reconciler_init_and_no_pending_req::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref()),
        at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)
    );
    lemma_from_after_create_headless_service_step_to_reconcile_idle(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(reconciler_reconcile_init::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())),
        lift_state(reconciler_init_and_no_pending_req::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)),
        lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref()))
    );
}

proof fn lemma_from_at_after_update_stateful_set_step_and_pending_req_in_flight_to_done_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_update_stateful_set_step_and_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())))),
{
    let pre = at_after_update_stateful_set_step_and_pending_req_in_flight(zk.object_ref());
    let post = reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
    assert forall |req_msg: Message| spec.entails(
        lift_state(#[trigger] req_msg_is_the_in_flight_pending_req_at_after_update_stateful_set_step(zk.object_ref(), req_msg))
            .leads_to(lift_state(at_after_update_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref())))
    ) by {
        let pre_1 = req_msg_is_the_in_flight_pending_req_at_after_update_stateful_set_step(zk.object_ref(), req_msg);
        let post_1 = at_after_update_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
        let stronger_next = |s, s_prime: ClusterState| {
            &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
            &&& crash_disabled()(s)
            &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        };
        entails_always_and_n!(
            spec,
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
            lift_state(crash_disabled()),
            lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())
        );
        temp_pred_equality(
            lift_action(stronger_next),
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
            .and(lift_state(crash_disabled()))
            .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        );
        let input = Option::Some(req_msg);
        assert forall |s, s_prime: ClusterState| pre_1(s) && #[trigger] stronger_next(s, s_prime)
        && kubernetes_api_next().forward(input)(s, s_prime) implies post_1(s_prime) by {
            let resp_msg = transition_by_etcd(req_msg, s.kubernetes_api_state).1;
            assert({
                &&& s_prime.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            });
        };
        lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
            spec, input, stronger_next, handle_request(), pre_1, post_1
        );
    }
    let msg_2_temp = |msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_stateful_set_step(zk.object_ref(), msg));
    leads_to_exists_intro(
        spec, msg_2_temp,
        lift_state(at_after_update_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref()))
    );
    assert_by(
        tla_exists(|msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_stateful_set_step(zk.object_ref(), msg)))
        == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies
            tla_exists(msg_2_temp).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(zk.object_ref());
                assert(msg_2_temp(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(pre), tla_exists(msg_2_temp));
        }
    );
    lemma_from_at_after_update_stateful_set_step_and_resp_matches_pending_req_in_flight_to_done_step(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(pre),
        lift_state(at_after_update_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref())),
        lift_state(post)
    );
}

proof fn lemma_from_at_after_update_stateful_set_step_and_resp_matches_pending_req_in_flight_to_done_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_update_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())))),
{
    let pre = at_after_update_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
    let post = reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
        &&& controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
        .and(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
    );
    let known_resp_in_flight = |resp| lift_state(
        |s: ClusterState| {
            at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)(s)
            && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
            && is_controller_request(s.pending_req_of(zk.object_ref()))
            && s.message_in_flight(resp)
            && resp_msg_matches_req_msg(resp, s.pending_req_of(zk.object_ref()))
        }
    );
    assert forall |msg: Message| spec.entails(#[trigger] known_resp_in_flight(msg)
        .leads_to(lift_state(post))) by {
            let resp_in_flight_state = |s: ClusterState| {
                at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)(s)
                && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
                && is_controller_request(s.pending_req_of(zk.object_ref()))
                && s.message_in_flight(msg)
                && resp_msg_matches_req_msg(msg, s.pending_req_of(zk.object_ref()))
            };
            let input = (Option::Some(msg), Option::Some(zk.object_ref()));
            lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
                spec,
                input,
                stronger_next,
                continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(),
                resp_in_flight_state,
                post
            );
    };
    leads_to_exists_intro::<ClusterState, Message>(spec, known_resp_in_flight, lift_state(post));
    assert_by(
        tla_exists(known_resp_in_flight) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex)
            implies tla_exists(known_resp_in_flight).satisfied_by(ex) by {
                let s = ex.head();
                let msg = choose |resp_msg: Message| {
                    #[trigger] s.message_in_flight(resp_msg)
                    && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(zk.object_ref()).pending_req_msg.get_Some_0())
                };
                assert(known_resp_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_resp_in_flight), lift_state(pre));
        }
    );
}

proof fn lemma_from_at_after_create_stateful_set_step_and_pending_req_in_flight_to_done_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_create_stateful_set_step_and_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())))),
{
    let pre = at_after_create_stateful_set_step_and_pending_req_in_flight(zk.object_ref());
    let post = reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
    assert forall |req_msg: Message| spec.entails(
        lift_state(#[trigger] req_msg_is_the_in_flight_pending_req_at_after_create_stateful_set_step(zk.object_ref(), req_msg))
            .leads_to(lift_state(at_after_create_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref())))
    ) by {
        let pre_1 = req_msg_is_the_in_flight_pending_req_at_after_create_stateful_set_step(zk.object_ref(), req_msg);
        let post_1 = at_after_create_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
        let stronger_next = |s, s_prime: ClusterState| {
            &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
            &&& crash_disabled()(s)
            &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        };
        entails_always_and_n!(
            spec,
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
            lift_state(crash_disabled()),
            lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())
        );
        temp_pred_equality(
            lift_action(stronger_next),
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
            .and(lift_state(crash_disabled()))
            .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        );
        let input = Option::Some(req_msg);
        assert forall |s, s_prime: ClusterState| pre_1(s) && #[trigger] stronger_next(s, s_prime)
        && kubernetes_api_next().forward(input)(s, s_prime) implies post_1(s_prime) by {
            let resp_msg = transition_by_etcd(req_msg, s.kubernetes_api_state).1;
            assert({
                &&& s_prime.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            });
        };
        lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
            spec, input, stronger_next, handle_request(), pre_1, post_1
        );
    }
    let msg_2_temp = |msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_stateful_set_step(zk.object_ref(), msg));
    leads_to_exists_intro(
        spec, msg_2_temp,
        lift_state(at_after_create_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref()))
    );
    assert_by(
        tla_exists(|msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_stateful_set_step(zk.object_ref(), msg)))
        == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies
            tla_exists(msg_2_temp).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(zk.object_ref());
                assert(msg_2_temp(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(pre), tla_exists(msg_2_temp));
        }
    );
    lemma_from_at_after_create_stateful_set_step_and_resp_matches_pending_req_in_flight_to_done_step(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(pre),
        lift_state(at_after_create_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref())),
        lift_state(post)
    );
}

proof fn lemma_from_at_after_create_stateful_set_step_and_resp_matches_pending_req_in_flight_to_done_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_create_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())))),
{
    let pre = at_after_create_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
    let post = reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
        &&& controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
        .and(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
    );
    let known_resp_in_flight = |resp| lift_state(
        |s: ClusterState| {
            at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)(s)
            && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
            && is_controller_request(s.pending_req_of(zk.object_ref()))
            && s.message_in_flight(resp)
            && resp_msg_matches_req_msg(resp, s.pending_req_of(zk.object_ref()))
        }
    );
    assert forall |msg: Message| spec.entails(#[trigger] known_resp_in_flight(msg)
        .leads_to(lift_state(post))) by {
            let resp_in_flight_state = |s: ClusterState| {
                at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)(s)
                && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
                && is_controller_request(s.pending_req_of(zk.object_ref()))
                && s.message_in_flight(msg)
                && resp_msg_matches_req_msg(msg, s.pending_req_of(zk.object_ref()))
            };
            let input = (Option::Some(msg), Option::Some(zk.object_ref()));
            lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
                spec,
                input,
                stronger_next,
                continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(),
                resp_in_flight_state,
                post
            );
    };
    leads_to_exists_intro::<ClusterState, Message>(spec, known_resp_in_flight, lift_state(post));
    assert_by(
        tla_exists(known_resp_in_flight) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex)
            implies tla_exists(known_resp_in_flight).satisfied_by(ex) by {
                let s = ex.head();
                let msg = choose |resp_msg: Message| {
                    #[trigger] s.message_in_flight(resp_msg)
                    && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(zk.object_ref()).pending_req_msg.get_Some_0())
                };
                assert(known_resp_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_resp_in_flight), lift_state(pre));
        }
    );
}

proof fn lemma_from_at_after_create_headless_service_step_and_pending_req_in_flight_to_after_create_client_service_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_create_headless_service_step_and_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
{
    let pre = at_after_create_headless_service_step_and_pending_req_in_flight(zk.object_ref());
    let post = at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService);
    assert forall |req_msg: Message| spec.entails(
        lift_state(#[trigger] req_msg_is_the_in_flight_pending_req_at_after_create_headless_service_step(zk.object_ref(), req_msg))
            .leads_to(lift_state(at_after_create_headless_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref())))
    ) by {
        let pre_1 = req_msg_is_the_in_flight_pending_req_at_after_create_headless_service_step(zk.object_ref(), req_msg);
        let post_1 = at_after_create_headless_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
        let stronger_next = |s, s_prime: ClusterState| {
            &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
            &&& crash_disabled()(s)
            &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        };
        entails_always_and_n!(
            spec,
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
            lift_state(crash_disabled()),
            lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())
        );
        temp_pred_equality(
            lift_action(stronger_next),
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
            .and(lift_state(crash_disabled()))
            .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        );
        let input = Option::Some(req_msg);
        assert forall |s, s_prime: ClusterState| pre_1(s) && #[trigger] stronger_next(s, s_prime)
        && kubernetes_api_next().forward(input)(s, s_prime) implies post_1(s_prime) by {
            let resp_msg = transition_by_etcd(req_msg, s.kubernetes_api_state).1;
            assert({
                &&& s_prime.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            });
        };
        lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
            spec, input, stronger_next, handle_request(), pre_1, post_1
        );
    }
    let msg_2_temp = |msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_headless_service_step(zk.object_ref(), msg));
    leads_to_exists_intro(
        spec, msg_2_temp,
        lift_state(at_after_create_headless_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref()))
    );
    assert_by(
        tla_exists(|msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_headless_service_step(zk.object_ref(), msg)))
        == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies
            tla_exists(msg_2_temp).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(zk.object_ref());
                assert(msg_2_temp(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(pre), tla_exists(msg_2_temp));
        }
    );
    lemma_from_at_after_create_headless_service_step_and_resp_matches_pending_req_in_flight_to_after_create_client_service_step(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(pre),
        lift_state(at_after_create_headless_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref())),
        lift_state(post)
    );
}

proof fn lemma_from_at_after_create_headless_service_step_and_resp_matches_pending_req_in_flight_to_after_create_client_service_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_create_headless_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
{
    let pre = at_after_create_headless_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
    let post = at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService);
    // TODO: lift stronger next to a public spec
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
        &&& controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
        .and(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
    );
    let known_resp_in_flight = |resp| lift_state(
        |s: ClusterState| {
            at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)(s)
            && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
            && is_controller_request(s.pending_req_of(zk.object_ref()))
            && s.message_in_flight(resp)
            && resp_msg_matches_req_msg(resp, s.pending_req_of(zk.object_ref()))
        }
    );
    assert forall |msg: Message| spec.entails(#[trigger] known_resp_in_flight(msg)
        .leads_to(lift_state(post))) by {
            let resp_in_flight_state = |s: ClusterState| {
                at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)(s)
                && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
                && is_controller_request(s.pending_req_of(zk.object_ref()))
                && s.message_in_flight(msg)
                && resp_msg_matches_req_msg(msg, s.pending_req_of(zk.object_ref()))
            };
            let input = (Option::Some(msg), Option::Some(zk.object_ref()));
            lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
                spec,
                input,
                stronger_next,
                continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(),
                resp_in_flight_state,
                post
            );
    };
    leads_to_exists_intro::<ClusterState, Message>(spec, known_resp_in_flight, lift_state(post));
    assert_by(
        tla_exists(known_resp_in_flight) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex)
            implies tla_exists(known_resp_in_flight).satisfied_by(ex) by {
                let s = ex.head();
                let msg = choose |resp_msg: Message| {
                    #[trigger] s.message_in_flight(resp_msg)
                    && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(zk.object_ref()).pending_req_msg.get_Some_0())
                };
                assert(known_resp_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_resp_in_flight), lift_state(pre));
        }
    );
}

proof fn lemma_from_at_after_create_client_service_step_and_pending_req_in_flight_to_after_create_admin_server_service_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_create_client_service_step_and_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
{
    let pre = at_after_create_client_service_step_and_pending_req_in_flight(zk.object_ref());
    let post = at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService);
    assert forall |req_msg: Message| spec.entails(
        lift_state(#[trigger] req_msg_is_the_in_flight_pending_req_at_after_create_client_service_step(zk.object_ref(), req_msg))
            .leads_to(lift_state(at_after_create_client_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref())))
    ) by {
        let pre_1 = req_msg_is_the_in_flight_pending_req_at_after_create_client_service_step(zk.object_ref(), req_msg);
        let post_1 = at_after_create_client_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
        let stronger_next = |s, s_prime: ClusterState| {
            &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
            &&& crash_disabled()(s)
            &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        };
        entails_always_and_n!(
            spec,
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
            lift_state(crash_disabled()),
            lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())
        );
        temp_pred_equality(
            lift_action(stronger_next),
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
            .and(lift_state(crash_disabled()))
            .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        );
        let input = Option::Some(req_msg);
        assert forall |s, s_prime: ClusterState| pre_1(s) && #[trigger] stronger_next(s, s_prime)
        && kubernetes_api_next().forward(input)(s, s_prime) implies post_1(s_prime) by {
            let resp_msg = transition_by_etcd(req_msg, s.kubernetes_api_state).1;
            assert({
                &&& s_prime.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            });
        };
        lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
            spec, input, stronger_next, handle_request(), pre_1, post_1
        );
    }
    let msg_2_temp = |msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_client_service_step(zk.object_ref(), msg));
    leads_to_exists_intro(
        spec, msg_2_temp,
        lift_state(at_after_create_client_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref()))
    );
    assert_by(
        tla_exists(|msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_client_service_step(zk.object_ref(), msg)))
        == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies
            tla_exists(msg_2_temp).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(zk.object_ref());
                assert(msg_2_temp(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(pre), tla_exists(msg_2_temp));
        }
    );
    lemma_from_at_after_create_client_service_step_and_resp_matches_pending_req_in_flight_to_after_create_admin_server_service_step(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(pre),
        lift_state(at_after_create_client_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref())),
        lift_state(post)
    );
}

proof fn lemma_from_at_after_create_client_service_step_and_resp_matches_pending_req_in_flight_to_after_create_admin_server_service_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_create_client_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
{
    let pre = at_after_create_client_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
    let post = at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService);
    // TODO: lift stronger next to a public spec
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
        &&& controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
        .and(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
    );
    let known_resp_in_flight = |resp| lift_state(
        |s: ClusterState| {
            at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)(s)
            && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
            && is_controller_request(s.pending_req_of(zk.object_ref()))
            && s.message_in_flight(resp)
            && resp_msg_matches_req_msg(resp, s.pending_req_of(zk.object_ref()))
        }
    );
    assert forall |msg: Message| spec.entails(#[trigger] known_resp_in_flight(msg)
        .leads_to(lift_state(post))) by {
            let resp_in_flight_state = |s: ClusterState| {
                at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)(s)
                && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
                && is_controller_request(s.pending_req_of(zk.object_ref()))
                && s.message_in_flight(msg)
                && resp_msg_matches_req_msg(msg, s.pending_req_of(zk.object_ref()))
            };
            let input = (Option::Some(msg), Option::Some(zk.object_ref()));
            lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
                spec,
                input,
                stronger_next,
                continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(),
                resp_in_flight_state,
                post
            );
    };
    leads_to_exists_intro::<ClusterState, Message>(spec, known_resp_in_flight, lift_state(post));
    assert_by(
        tla_exists(known_resp_in_flight) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex)
            implies tla_exists(known_resp_in_flight).satisfied_by(ex) by {
                let s = ex.head();
                let msg = choose |resp_msg: Message| {
                    #[trigger] s.message_in_flight(resp_msg)
                    && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(zk.object_ref()).pending_req_msg.get_Some_0())
                };
                assert(known_resp_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_resp_in_flight), lift_state(pre));
        }
    );
}

proof fn lemma_from_at_after_create_admin_server_service_step_and_resp_matches_pending_req_in_flight_to_after_create_config_map_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_create_admin_server_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
{
    let pre = at_after_create_admin_server_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
    let post = at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap);
    // TODO: lift stronger next to a public spec
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
        &&& controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
        .and(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
    );
    let known_resp_in_flight = |resp| lift_state(
        |s: ClusterState| {
            at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)(s)
            && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
            && is_controller_request(s.pending_req_of(zk.object_ref()))
            && s.message_in_flight(resp)
            && resp_msg_matches_req_msg(resp, s.pending_req_of(zk.object_ref()))
        }
    );
    assert forall |msg: Message| spec.entails(#[trigger] known_resp_in_flight(msg)
        .leads_to(lift_state(post))) by {
            let resp_in_flight_state = |s: ClusterState| {
                at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)(s)
                && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
                && is_controller_request(s.pending_req_of(zk.object_ref()))
                && s.message_in_flight(msg)
                && resp_msg_matches_req_msg(msg, s.pending_req_of(zk.object_ref()))
            };
            let input = (Option::Some(msg), Option::Some(zk.object_ref()));
            lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
                spec,
                input,
                stronger_next,
                continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(),
                resp_in_flight_state,
                post
            );
    };
    leads_to_exists_intro::<ClusterState, Message>(spec, known_resp_in_flight, lift_state(post));
    assert_by(
        tla_exists(known_resp_in_flight) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex)
            implies tla_exists(known_resp_in_flight).satisfied_by(ex) by {
                let s = ex.head();
                let msg = choose |resp_msg: Message| {
                    #[trigger] s.message_in_flight(resp_msg)
                    && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(zk.object_ref()).pending_req_msg.get_Some_0())
                };
                assert(known_resp_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_resp_in_flight), lift_state(pre));
        }
    );
}

proof fn lemma_from_at_after_create_admin_server_service_step_and_pending_req_in_flight_to_after_create_config_map_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_create_admin_server_service_step_and_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
{
    let pre = at_after_create_admin_server_service_step_and_pending_req_in_flight(zk.object_ref());
    let post = at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap);
    assert forall |req_msg: Message| spec.entails(
        lift_state(#[trigger] req_msg_is_the_in_flight_pending_req_at_after_create_admin_server_service_step(zk.object_ref(), req_msg))
            .leads_to(lift_state(at_after_create_admin_server_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref())))
    ) by {
        let pre_1 = req_msg_is_the_in_flight_pending_req_at_after_create_admin_server_service_step(zk.object_ref(), req_msg);
        let post_1 = at_after_create_admin_server_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
        let stronger_next = |s, s_prime: ClusterState| {
            &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
            &&& crash_disabled()(s)
            &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        };
        entails_always_and_n!(
            spec,
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
            lift_state(crash_disabled()),
            lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())
        );
        temp_pred_equality(
            lift_action(stronger_next),
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
            .and(lift_state(crash_disabled()))
            .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        );
        let input = Option::Some(req_msg);
        assert forall |s, s_prime: ClusterState| pre_1(s) && #[trigger] stronger_next(s, s_prime)
        && kubernetes_api_next().forward(input)(s, s_prime) implies post_1(s_prime) by {
            let resp_msg = transition_by_etcd(req_msg, s.kubernetes_api_state).1;
            assert({
                &&& s_prime.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            });
        };
        lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
            spec, input, stronger_next, handle_request(), pre_1, post_1
        );
    }
    let msg_2_temp = |msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_admin_server_service_step(zk.object_ref(), msg));
    leads_to_exists_intro(
        spec, msg_2_temp,
        lift_state(at_after_create_admin_server_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref()))
    );
    assert_by(
        tla_exists(|msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_admin_server_service_step(zk.object_ref(), msg)))
        == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies
            tla_exists(msg_2_temp).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(zk.object_ref());
                assert(msg_2_temp(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(pre), tla_exists(msg_2_temp));
        }
    );
    lemma_from_at_after_create_admin_server_service_step_and_resp_matches_pending_req_in_flight_to_after_create_config_map_step(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(pre),
        lift_state(at_after_create_admin_server_service_step_and_resp_matches_pending_req_in_flight(zk.object_ref())),
        lift_state(post)
    );
}

proof fn lemma_from_at_after_create_config_map_step_and_resp_matches_pending_req_in_flight_to_after_get_stateful_set_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_create_config_map_step_and_resp_matches_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
{
    let pre = at_after_create_config_map_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
    let post = at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet);
    // TODO: lift stronger next to a public spec
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
        &&& controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
        .and(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
    );
    let known_resp_in_flight = |resp| lift_state(
        |s: ClusterState| {
            at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)(s)
            && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
            && is_controller_request(s.pending_req_of(zk.object_ref()))
            && s.message_in_flight(resp)
            && resp_msg_matches_req_msg(resp, s.pending_req_of(zk.object_ref()))
        }
    );
    assert forall |msg: Message| spec.entails(#[trigger] known_resp_in_flight(msg)
        .leads_to(lift_state(post))) by {
            let resp_in_flight_state = |s: ClusterState| {
                at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)(s)
                && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
                && is_controller_request(s.pending_req_of(zk.object_ref()))
                && s.message_in_flight(msg)
                && resp_msg_matches_req_msg(msg, s.pending_req_of(zk.object_ref()))
            };
            let input = (Option::Some(msg), Option::Some(zk.object_ref()));
            lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
                spec,
                input,
                stronger_next,
                continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(),
                resp_in_flight_state,
                post
            );
    };
    leads_to_exists_intro::<ClusterState, Message>(spec, known_resp_in_flight, lift_state(post));
    assert_by(
        tla_exists(known_resp_in_flight) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex)
            implies tla_exists(known_resp_in_flight).satisfied_by(ex) by {
                let s = ex.head();
                let msg = choose |resp_msg: Message| {
                    #[trigger] s.message_in_flight(resp_msg)
                    && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(zk.object_ref()).pending_req_msg.get_Some_0())
                };
                assert(known_resp_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_resp_in_flight), lift_state(pre));
        }
    );
}

proof fn lemma_from_at_after_create_config_map_step_and_pending_req_in_flight_to_after_get_stateful_set_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_create_config_map_step_and_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
{
    let pre = at_after_create_config_map_step_and_pending_req_in_flight(zk.object_ref());
    let post = at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet);
    assert forall |req_msg: Message| spec.entails(
        lift_state(#[trigger] req_msg_is_the_in_flight_pending_req_at_after_create_config_map_step(zk.object_ref(), req_msg))
            .leads_to(lift_state(at_after_create_config_map_step_and_resp_matches_pending_req_in_flight(zk.object_ref())))
    ) by {
        let pre_1 = req_msg_is_the_in_flight_pending_req_at_after_create_config_map_step(zk.object_ref(), req_msg);
        let post_1 = at_after_create_config_map_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
        let stronger_next = |s, s_prime: ClusterState| {
            &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
            &&& crash_disabled()(s)
            &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        };
        entails_always_and_n!(
            spec,
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
            lift_state(crash_disabled()),
            lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())
        );
        temp_pred_equality(
            lift_action(stronger_next),
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
            .and(lift_state(crash_disabled()))
            .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        );
        let input = Option::Some(req_msg);
        assert forall |s, s_prime: ClusterState| pre_1(s) && #[trigger] stronger_next(s, s_prime)
        && kubernetes_api_next().forward(input)(s, s_prime) implies post_1(s_prime) by {
            let resp_msg = transition_by_etcd(req_msg, s.kubernetes_api_state).1;
            assert({
                &&& s_prime.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            });
        };
        lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
            spec, input, stronger_next, handle_request(), pre_1, post_1
        );
    }
    let msg_2_temp = |msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_config_map_step(zk.object_ref(), msg));
    leads_to_exists_intro(
        spec, msg_2_temp,
        lift_state(at_after_create_config_map_step_and_resp_matches_pending_req_in_flight(zk.object_ref()))
    );
    assert_by(
        tla_exists(|msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_config_map_step(zk.object_ref(), msg)))
        == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies
            tla_exists(msg_2_temp).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(zk.object_ref());
                assert(msg_2_temp(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(pre), tla_exists(msg_2_temp));
        }
    );
    lemma_from_at_after_create_config_map_step_and_resp_matches_pending_req_in_flight_to_after_get_stateful_set_step(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(pre),
        lift_state(at_after_create_config_map_step_and_resp_matches_pending_req_in_flight(zk.object_ref())),
        lift_state(post)
    );
}

proof fn lemma_from_at_after_get_stateful_set_step_and_resp_matches_pending_req_in_flight_to_reconcile_idle(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_get_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(|s: ClusterState| { !s.reconcile_state_contains(zk.object_ref()) }))),
{
    let pre = at_after_get_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
    let post = |s: ClusterState| {
        s.reconcile_state_contains(zk.object_ref())
        && (
            s.reconcile_state_of(zk.object_ref()).local_state.reconcile_step == ZookeeperReconcileStep::AfterUpdateStatefulSet
            || s.reconcile_state_of(zk.object_ref()).local_state.reconcile_step == ZookeeperReconcileStep::AfterCreateStatefulSet
            || s.reconcile_state_of(zk.object_ref()).local_state.reconcile_step == ZookeeperReconcileStep::Error
        )
    };
    // TODO: lift stronger next to a public spec
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
        &&& controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
        .and(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
    );
    let known_resp_in_flight = |resp| lift_state(
        |s: ClusterState| {
            at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)(s)
            && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
            && is_controller_request(s.pending_req_of(zk.object_ref()))
            && s.message_in_flight(resp)
            && resp_msg_matches_req_msg(resp, s.pending_req_of(zk.object_ref()))
        }
    );
    assert forall |msg: Message| spec.entails(#[trigger] known_resp_in_flight(msg)
        .leads_to(lift_state(post))) by {
            let resp_in_flight_state = |s: ClusterState| {
                at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)(s)
                && s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
                && is_controller_request(s.pending_req_of(zk.object_ref()))
                && s.message_in_flight(msg)
                && resp_msg_matches_req_msg(msg, s.pending_req_of(zk.object_ref()))
            };
            let input = (Option::Some(msg), Option::Some(zk.object_ref()));
            lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
                spec,
                input,
                stronger_next,
                continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(),
                resp_in_flight_state,
                post
            );
    };
    leads_to_exists_intro::<ClusterState, Message>(spec, known_resp_in_flight, lift_state(post));
    assert_by(
        tla_exists(known_resp_in_flight) == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex)
            implies tla_exists(known_resp_in_flight).satisfied_by(ex) by {
                let s = ex.head();
                let msg = choose |resp_msg: Message| {
                    #[trigger] s.message_in_flight(resp_msg)
                    && resp_msg_matches_req_msg(resp_msg, s.reconcile_state_of(zk.object_ref()).pending_req_msg.get_Some_0())
                };
                assert(known_resp_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_resp_in_flight), lift_state(pre));
        }
    );
    lemma_from_after_update_stateful_set_step_to_reconcile_idle(spec, zk);
    lemma_from_after_create_stateful_set_step_to_reconcile_idle(spec, zk);
    lemma_reconcile_error_leads_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, zk.object_ref());
    or_leads_to_combine_n!(
        spec,
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)),
        lift_state(reconciler_reconcile_error::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref()));
        lift_state(|s: ClusterState| { !s.reconcile_state_contains(zk.object_ref()) })
    );
    temp_pred_equality(
        lift_state(post),
        lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet))
        .or(lift_state(at_zookeeper_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))
        .or(lift_state(reconciler_reconcile_error::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref())))
    );
    leads_to_trans_n!(spec, lift_state(pre), lift_state(post), lift_state(|s: ClusterState| { !s.reconcile_state_contains(zk.object_ref()) }));
}

proof fn lemma_from_at_after_get_stateful_set_step_and_pending_req_in_flight_to_reconcile_idle(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(reconcile_init_implies_no_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap)))),
        spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_step(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet)))),
    ensures
        spec.entails(lift_state(at_after_get_stateful_set_step_and_pending_req_in_flight(zk.object_ref())).leads_to(lift_state(|s: ClusterState| { !s.reconcile_state_contains(zk.object_ref()) }))),
{
    let pre = at_after_get_stateful_set_step_and_pending_req_in_flight(zk.object_ref());
    let post = |s: ClusterState| { !s.reconcile_state_contains(zk.object_ref()) };
    assert forall |req_msg: Message| spec.entails(
        lift_state(#[trigger] req_msg_is_the_in_flight_pending_req_at_after_get_stateful_set_step(zk.object_ref(), req_msg))
            .leads_to(lift_state(at_after_get_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref())))
    ) by {
        let pre_1 = req_msg_is_the_in_flight_pending_req_at_after_get_stateful_set_step(zk.object_ref(), req_msg);
        let post_1 = at_after_get_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref());
        let stronger_next = |s, s_prime: ClusterState| {
            &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
            &&& crash_disabled()(s)
            &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        };
        entails_always_and_n!(
            spec,
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
            lift_state(crash_disabled()),
            lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())
        );
        temp_pred_equality(
            lift_action(stronger_next),
            lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
            .and(lift_state(crash_disabled()))
            .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        );
        let input = Option::Some(req_msg);
        assert forall |s, s_prime: ClusterState| pre_1(s) && #[trigger] stronger_next(s, s_prime)
        && kubernetes_api_next().forward(input)(s, s_prime) implies post_1(s_prime) by {
            let resp_msg = transition_by_etcd(req_msg, s.kubernetes_api_state).1;
            assert({
                &&& s_prime.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            });
        };
        lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
            spec, input, stronger_next, handle_request(), pre_1, post_1
        );
    }
    let msg_2_temp = |msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_stateful_set_step(zk.object_ref(), msg));
    leads_to_exists_intro(
        spec, msg_2_temp,
        lift_state(at_after_get_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref()))
    );
    assert_by(
        tla_exists(|msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_stateful_set_step(zk.object_ref(), msg)))
        == lift_state(pre),
        {
            assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies
            tla_exists(msg_2_temp).satisfied_by(ex) by {
                let req_msg = ex.head().pending_req_of(zk.object_ref());
                assert(msg_2_temp(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(lift_state(pre), tla_exists(msg_2_temp));
        }
    );
    lemma_from_at_after_get_stateful_set_step_and_resp_matches_pending_req_in_flight_to_reconcile_idle(spec, zk);
    leads_to_trans_n!(
        spec,
        lift_state(pre),
        lift_state(at_after_get_stateful_set_step_and_resp_matches_pending_req_in_flight(zk.object_ref())),
        lift_state(post)
    );
}

}
