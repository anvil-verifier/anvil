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
use crate::rabbitmq_controller::{
    common::RabbitmqReconcileStep,
    proof::common::*,
    spec::{rabbitmqcluster::*, reconciler::*},
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub proof fn reconcile_eventually_terminates(spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(next::<RabbitmqClusterView, RabbitmqReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<RabbitmqClusterView, RabbitmqReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(pending_req_is_none_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconciler>(
            rabbitmq.object_ref(), |s: RabbitmqReconcileState| s.reconcile_step == RabbitmqReconcileStep::Init)))),
        forall |step: RabbitmqReconcileStep|
        step != RabbitmqReconcileStep::Init && step != RabbitmqReconcileStep::Error && step != RabbitmqReconcileStep::Done
        ==> spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, RabbitmqReconciler>(
            rabbitmq.object_ref(), (#[trigger] get_closure(step))
        )))),
    ensures
        spec.entails(
            true_pred().leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(rabbitmq.object_ref())))
        ),
{
    let reconcile_idle = |s: ClusterState| { !s.reconcile_state_contains(rabbitmq.object_ref()) };
    lemma_reconcile_error_leads_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq.object_ref());
    lemma_reconcile_done_leads_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq.object_ref());
    temp_pred_equality(
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::Done)),
        lift_state(reconciler_reconcile_done::<RabbitmqClusterView, RabbitmqReconciler>(rabbitmq.object_ref()))
    );
    temp_pred_equality(
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::Error)),
        lift_state(reconciler_reconcile_error::<RabbitmqClusterView, RabbitmqReconciler>(rabbitmq.object_ref()))
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterUpdateStatefulSet), get_closure(RabbitmqReconcileStep::Done));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterCreateStatefulSet), get_closure(RabbitmqReconcileStep::Done));
    or_leads_to_combine_n!(
        spec,
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterUpdateStatefulSet)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateStatefulSet)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::Error));
        lift_state(|s: ClusterState| { !s.reconcile_state_contains(rabbitmq.object_ref()) })
    );
    let next_state = |s: RabbitmqReconcileState| {
        s.reconcile_step == RabbitmqReconcileStep::AfterUpdateStatefulSet
        || s.reconcile_step == RabbitmqReconcileStep::AfterCreateStatefulSet 
        || s.reconcile_step == RabbitmqReconcileStep::Error
    };
    temp_pred_equality(
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterUpdateStatefulSet))
        .or(lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateStatefulSet)))
        .or(lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::Error))),
        lift_state(at_expected_reconcile_states(rabbitmq.object_ref(), next_state))
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(
        spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterGetStatefulSet), next_state
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterCreateRoleBinding), get_closure(RabbitmqReconcileStep::AfterGetStatefulSet));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterCreateRole), get_closure(RabbitmqReconcileStep::AfterCreateRoleBinding));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterCreateServiceAccount), get_closure(RabbitmqReconcileStep::AfterCreateRole));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterCreateServerConfigMap), get_closure(RabbitmqReconcileStep::AfterCreateServiceAccount));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterUpdateServerConfigMap), get_closure(RabbitmqReconcileStep::AfterCreateServiceAccount));

    or_leads_to_combine_n!(
        spec,
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterUpdateServerConfigMap)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateServerConfigMap)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::Error));
        lift_state(|s: ClusterState| { !s.reconcile_state_contains(rabbitmq.object_ref()) })
    );
    let next_state_1 = |s: RabbitmqReconcileState| {
        s.reconcile_step == RabbitmqReconcileStep::AfterUpdateServerConfigMap
        || s.reconcile_step == RabbitmqReconcileStep::AfterCreateServerConfigMap 
        || s.reconcile_step == RabbitmqReconcileStep::Error
    };
    temp_pred_equality(
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterUpdateServerConfigMap))
        .or(lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateServerConfigMap)))
        .or(lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::Error))),
        lift_state(at_expected_reconcile_states(rabbitmq.object_ref(), next_state_1))
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(
        spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterGetServerConfigMap), next_state_1
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterCreatePluginsConfigMap), get_closure(RabbitmqReconcileStep::AfterGetServerConfigMap));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterCreateDefaultUserSecret), get_closure(RabbitmqReconcileStep::AfterCreatePluginsConfigMap));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterCreateErlangCookieSecret), get_closure(RabbitmqReconcileStep::AfterCreateDefaultUserSecret));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterCreateService), get_closure(RabbitmqReconcileStep::AfterCreateErlangCookieSecret));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::AfterCreateHeadlessService), get_closure(RabbitmqReconcileStep::AfterCreateService));
    lemma_from_init_state_to_next_state_to_reconcile_idle::<RabbitmqClusterView, RabbitmqReconciler>(spec, rabbitmq, get_closure(RabbitmqReconcileStep::Init), get_closure(RabbitmqReconcileStep::AfterCreateHeadlessService));
    valid_implies_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::Init)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateHeadlessService)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateService)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateErlangCookieSecret)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateDefaultUserSecret)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreatePluginsConfigMap)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterGetServerConfigMap)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateServerConfigMap)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterUpdateServerConfigMap)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateServiceAccount)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateRole)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateRoleBinding)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterGetStatefulSet)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterCreateStatefulSet)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::AfterUpdateStatefulSet)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::Done)),
        lift_state(get_reconcile_state(rabbitmq, RabbitmqReconcileStep::Error));
        lift_state(reconcile_idle)
    );
}

}
