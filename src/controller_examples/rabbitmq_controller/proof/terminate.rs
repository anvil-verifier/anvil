// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::EmptyAPI;
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
        spec.entails(always(lift_action(next::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(busy_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(no_pending_req_msg_or_external_api_input_at_reconcile_state::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(
            rabbitmq.object_ref(), |s: RabbitmqReconcileState| s.reconcile_step == RabbitmqReconcileStep::Init)))),
        forall |step: RabbitmqReconcileStep|
        step != RabbitmqReconcileStep::Init && step != RabbitmqReconcileStep::Error && step != RabbitmqReconcileStep::Done
        ==> spec.entails(always(lift_state(pending_req_in_flight_or_resp_in_flight_at_reconcile_state::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(
            rabbitmq.object_ref(), (#[trigger] at_step_closure(step))
        )))),
    ensures
        spec.entails(
            true_pred().leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(rabbitmq.object_ref())))
        ),
{
    let reconcile_idle = |s: ClusterState| { !s.reconcile_state_contains(rabbitmq.object_ref()) };
    lemma_reconcile_error_leads_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq.object_ref());
    lemma_reconcile_done_leads_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq.object_ref());
    temp_pred_equality(
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Done)),
        lift_state(reconciler_reconcile_done::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(rabbitmq.object_ref()))
    );
    temp_pred_equality(
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error)),
        lift_state(reconciler_reconcile_error::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(rabbitmq.object_ref()))
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterUpdateStatefulSet), at_step_closure(RabbitmqReconcileStep::Done));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateStatefulSet), at_step_closure(RabbitmqReconcileStep::Done));
    or_leads_to_combine_n!(
        spec,
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterUpdateStatefulSet)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateStatefulSet)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error));
        lift_state(|s: ClusterState| { !s.reconcile_state_contains(rabbitmq.object_ref()) })
    );
    let next_state = |s: RabbitmqReconcileState| {
        s.reconcile_step == RabbitmqReconcileStep::AfterUpdateStatefulSet
        || s.reconcile_step == RabbitmqReconcileStep::AfterCreateStatefulSet
        || s.reconcile_step == RabbitmqReconcileStep::Error
    };
    temp_pred_equality(
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterUpdateStatefulSet))
        .or(lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateStatefulSet)))
        .or(lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error))),
        lift_state(at_expected_reconcile_states(rabbitmq.object_ref(), next_state))
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(
        spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterGetStatefulSet), next_state
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateRoleBinding), at_step_closure(RabbitmqReconcileStep::AfterGetStatefulSet));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateRole), at_step_closure(RabbitmqReconcileStep::AfterCreateRoleBinding));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateServiceAccount), at_step_closure(RabbitmqReconcileStep::AfterCreateRole));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateServerConfigMap), at_step_closure(RabbitmqReconcileStep::AfterCreateServiceAccount));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterUpdateServerConfigMap), at_step_closure(RabbitmqReconcileStep::AfterCreateServiceAccount));

    or_leads_to_combine_n!(
        spec,
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterUpdateServerConfigMap)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateServerConfigMap)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error));
        lift_state(|s: ClusterState| { !s.reconcile_state_contains(rabbitmq.object_ref()) })
    );
    let next_state_1 = |s: RabbitmqReconcileState| {
        s.reconcile_step == RabbitmqReconcileStep::AfterUpdateServerConfigMap
        || s.reconcile_step == RabbitmqReconcileStep::AfterCreateServerConfigMap
        || s.reconcile_step == RabbitmqReconcileStep::Error
    };
    temp_pred_equality(
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterUpdateServerConfigMap))
        .or(lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateServerConfigMap)))
        .or(lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error))),
        lift_state(at_expected_reconcile_states(rabbitmq.object_ref(), next_state_1))
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(
        spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterGetServerConfigMap), next_state_1
    );
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreatePluginsConfigMap), at_step_closure(RabbitmqReconcileStep::AfterGetServerConfigMap));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateDefaultUserSecret), at_step_closure(RabbitmqReconcileStep::AfterCreatePluginsConfigMap));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateErlangCookieSecret), at_step_closure(RabbitmqReconcileStep::AfterCreateDefaultUserSecret));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateService), at_step_closure(RabbitmqReconcileStep::AfterCreateErlangCookieSecret));
    lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateHeadlessService), at_step_closure(RabbitmqReconcileStep::AfterCreateService));
    lemma_from_init_state_to_next_state_to_reconcile_idle::<RabbitmqClusterView, EmptyAPI,  RabbitmqReconciler>(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::Init), at_step_closure(RabbitmqReconcileStep::AfterCreateHeadlessService));
    valid_implies_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Init)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateHeadlessService)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateService)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateErlangCookieSecret)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateDefaultUserSecret)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreatePluginsConfigMap)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterGetServerConfigMap)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateServerConfigMap)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterUpdateServerConfigMap)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateServiceAccount)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateRole)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateRoleBinding)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterGetStatefulSet)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateStatefulSet)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterUpdateStatefulSet)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Done)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error));
        lift_state(reconcile_idle)
    );
}

pub open spec fn at_step_state_pred(rabbitmq: RabbitmqClusterView, step: RabbitmqReconcileStep) -> StatePred<ClusterState> {
    at_expected_reconcile_states(rabbitmq.object_ref(), |s: RabbitmqReconcileState| s.reconcile_step == step)
}

}
