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
        controller::common::{controller_req_msg, ControllerActionInput<E>, ControllerStep},
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::*,
        kubernetes_api::state_machine::{handle_request, transition_by_etcd, update_is_noop},
        message::*,
    },
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::zookeeper_controller::{
    common::ZookeeperReconcileStep,
    proof::common::*,
    spec::{reconciler::*, zookeepercluster::*},
};
use vstd::prelude::*;

verus! {

pub proof fn reconcile_eventually_terminates(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateStatefulSet))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterCreateStatefulSet))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterCreateHeadlessService))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterCreateClientService))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterCreateAdminServerService))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterCreateConfigMap))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterGetStatefulSet))),
        spec.entails(always(pending_req_or_resp_at(zk.object_ref(), ZookeeperReconcileStep::AfterUpdateZKNode))),
        spec.entails(always(pending_req_is_none(zk.object_ref(), ZookeeperReconcileStep::AfterCreateZKNode))),
        spec.entails(always(pending_req_is_none(zk.object_ref(), ZookeeperReconcileStep::Init))),
    ensures
        spec.entails(
            true_pred().leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
{
    let reconcile_idle = |s: ClusterState| { !s.reconcile_state_contains(zk.object_ref()) };
    lemma_reconcile_error_leads_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(spec, zk.object_ref());
    lemma_reconcile_done_leads_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(spec, zk.object_ref());
    temp_pred_equality(
        lift_state(at_step(zk, ZookeeperReconcileStep::Done)),
        lift_state(reconciler_reconcile_done::<ZookeeperClusterView, ZookeeperReconciler>(zk.object_ref()))
    );
    temp_pred_equality(
        lift_state(at_step(zk, ZookeeperReconcileStep::Error)),
        lift_state(reconciler_reconcile_error::<ZookeeperClusterView, ZookeeperReconciler>(zk.object_ref()))
    );
    or_leads_to_combine(
        spec, at_step(zk, ZookeeperReconcileStep::Done), at_step(zk, ZookeeperReconcileStep::Error),
        reconcile_idle
    );
    temp_pred_equality(
        lift_state(at_step(zk, ZookeeperReconcileStep::Done)).or(lift_state(at_step(zk, ZookeeperReconcileStep::Error))),
        lift_state(at_expected_reconcile_states(
            zk.object_ref(),
            |s: ZookeeperReconcileState| {s.reconcile_step == ZookeeperReconcileStep::Error || s.reconcile_step == ZookeeperReconcileStep::Done}
        ))
    );
    lemma_from_some_state_with_ext_resp_to_two_next_states_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateZKNode,
        |s: ZookeeperReconcileState| {s.reconcile_step == ZookeeperReconcileStep::Error || s.reconcile_step == ZookeeperReconcileStep::Done}
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterUpdateStatefulSet,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateZKNode
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateStatefulSet,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateZKNode
    );

    or_leads_to_combine(
        spec, at_step(zk, ZookeeperReconcileStep::AfterUpdateStatefulSet), at_step(zk, ZookeeperReconcileStep::Error),
        reconcile_idle
    );
    temp_pred_equality(
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterUpdateStatefulSet)).or(lift_state(at_step(zk, ZookeeperReconcileStep::Error))),
        lift_state(at_expected_reconcile_states(
            zk.object_ref(),
            |s: ZookeeperReconcileState| {s.reconcile_step == ZookeeperReconcileStep::AfterUpdateStatefulSet || s.reconcile_step == ZookeeperReconcileStep::Error}
        ))
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterUpdateZKNode,
        |s: ZookeeperReconcileState| {s.reconcile_step == ZookeeperReconcileStep::AfterUpdateStatefulSet || s.reconcile_step == ZookeeperReconcileStep::Error}
    );
    or_leads_to_combine_n!(
        spec,
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateStatefulSet)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterUpdateZKNode)),
        lift_state(at_step(zk, ZookeeperReconcileStep::Error));
        lift_state(reconcile_idle)
    );
    temp_pred_equality(
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateStatefulSet))
        .or(lift_state(at_step(zk, ZookeeperReconcileStep::AfterUpdateZKNode)))
        .or(lift_state(at_step(zk, ZookeeperReconcileStep::Error))),
        lift_state(at_expected_reconcile_states(
            zk.object_ref(),
            |s: ZookeeperReconcileState| {
                s.reconcile_step == ZookeeperReconcileStep::AfterCreateStatefulSet
                || s.reconcile_step == ZookeeperReconcileStep::AfterUpdateZKNode
                || s.reconcile_step == ZookeeperReconcileStep::Error
            }
        ))
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterGetStatefulSet,
        |s: ZookeeperReconcileState| {
            s.reconcile_step == ZookeeperReconcileStep::AfterCreateStatefulSet
            || s.reconcile_step == ZookeeperReconcileStep::AfterUpdateZKNode
            || s.reconcile_step == ZookeeperReconcileStep::Error
        }
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateConfigMap,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterGetStatefulSet
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateAdminServerService,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateConfigMap
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateClientService,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateAdminServerService
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateHeadlessService,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateClientService
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateStatefulSet,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateZKNode
    );
    lemma_from_init_state_to_next_state_to_reconcile_idle::<ZookeeperClusterView, ZookeeperReconciler>(
        spec, zk, |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::Init,
        |s: ZookeeperReconcileState| s.reconcile_step == ZookeeperReconcileStep::AfterCreateHeadlessService);
    valid_implies_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(reconciler_reconcile_error::<ZookeeperClusterView, ZookeeperReconciler>(zk.object_ref())),
        lift_state(at_step(zk, ZookeeperReconcileStep::Init)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateHeadlessService)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateClientService)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateAdminServerService)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateConfigMap)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterGetStatefulSet)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateStatefulSet)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterUpdateStatefulSet)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterCreateZKNode)),
        lift_state(at_step(zk, ZookeeperReconcileStep::AfterUpdateZKNode)),
        lift_state(at_step(zk, ZookeeperReconcileStep::Done));
        lift_state(reconcile_idle)
    );
}

pub open spec fn at_step(zk: ZookeeperClusterView, step: ZookeeperReconcileStep) -> StatePred<ClusterState> {
    at_expected_reconcile_states::<ZookeeperClusterView, ZookeeperReconciler>(
        zk.object_ref(), |s: ZookeeperReconcileState| s.reconcile_step == step
    )
}

pub open spec fn pending_req_or_resp_at(key: ObjectRef, step: ZookeeperReconcileStep) -> TempPred<ClusterState> {
    lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<ZookeeperClusterView, ZookeeperReconciler>(
        key, |s: ZookeeperReconcileState| s.reconcile_step == step
    ))
}

pub open spec fn pending_req_is_none(key: ObjectRef, step: ZookeeperReconcileStep) -> TempPred<ClusterState> {
    lift_state(no_pending_req_msg_or_external_api_input_at_reconcile_state::<ZookeeperClusterView, ZookeeperReconciler>(
        key, |s: ZookeeperReconcileState| s.reconcile_step == step
    ))
}

}
