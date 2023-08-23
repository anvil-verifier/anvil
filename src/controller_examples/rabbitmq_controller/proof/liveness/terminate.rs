// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::EmptyAPI;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, error::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
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

pub proof fn reconcile_eventually_terminates(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(
            rabbitmq.object_ref(), |s: RabbitmqReconcileState| s.reconcile_step == RabbitmqReconcileStep::Init)))),
        forall |step: RabbitmqReconcileStep|
        step != RabbitmqReconcileStep::Init && step != RabbitmqReconcileStep::Error && step != RabbitmqReconcileStep::Done
        ==> spec.entails(always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            rabbitmq.object_ref(), (#[trigger] at_step_closure(step))
        )))),
    ensures
        spec.entails(
            true_pred().leads_to(lift_state(|s: RMQCluster| !s.reconcile_state_contains(rabbitmq.object_ref())))
        ),
{
    let reconcile_idle = |s: RMQCluster| { !s.reconcile_state_contains(rabbitmq.object_ref()) };
    RMQCluster::lemma_reconcile_error_leads_to_reconcile_idle(spec, rabbitmq.object_ref());
    RMQCluster::lemma_reconcile_done_leads_to_reconcile_idle(spec, rabbitmq.object_ref());
    temp_pred_equality(
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Done)),
        lift_state(RMQCluster::reconciler_reconcile_done(rabbitmq.object_ref()))
    );
    temp_pred_equality(
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error)),
        lift_state(RMQCluster::reconciler_reconcile_error(rabbitmq.object_ref()))
    );
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterUpdateStatefulSet), at_step_closure(RabbitmqReconcileStep::Done));
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateStatefulSet), at_step_closure(RabbitmqReconcileStep::Done));
    let next_state = |s: RabbitmqReconcileState| {
        s.reconcile_step == RabbitmqReconcileStep::AfterUpdateStatefulSet
        || s.reconcile_step == RabbitmqReconcileStep::AfterCreateStatefulSet
        || s.reconcile_step == RabbitmqReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(RMQCluster::at_expected_reconcile_states(rabbitmq.object_ref(), next_state)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterUpdateStatefulSet)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateStatefulSet)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error));
        lift_state(|s: RMQCluster| { !s.reconcile_state_contains(rabbitmq.object_ref()) })
    );
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterGetStatefulSet), next_state
    );
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateRoleBinding), at_step_closure(RabbitmqReconcileStep::AfterGetStatefulSet));
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateRole), at_step_closure(RabbitmqReconcileStep::AfterCreateRoleBinding));
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateServiceAccount), at_step_closure(RabbitmqReconcileStep::AfterCreateRole));
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateServerConfigMap), at_step_closure(RabbitmqReconcileStep::AfterCreateServiceAccount));
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterUpdateServerConfigMap), at_step_closure(RabbitmqReconcileStep::AfterCreateServiceAccount));

    let next_state_1 = |s: RabbitmqReconcileState| {
        s.reconcile_step == RabbitmqReconcileStep::AfterUpdateServerConfigMap
        || s.reconcile_step == RabbitmqReconcileStep::AfterCreateServerConfigMap
        || s.reconcile_step == RabbitmqReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(RMQCluster::at_expected_reconcile_states(rabbitmq.object_ref(), next_state_1)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterUpdateServerConfigMap)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::AfterCreateServerConfigMap)),
        lift_state(at_step_state_pred(rabbitmq, RabbitmqReconcileStep::Error));
        lift_state(|s: RMQCluster| { !s.reconcile_state_contains(rabbitmq.object_ref()) })
    );
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterGetServerConfigMap), next_state_1
    );
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreatePluginsConfigMap), at_step_closure(RabbitmqReconcileStep::AfterGetServerConfigMap));
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateDefaultUserSecret), at_step_closure(RabbitmqReconcileStep::AfterCreatePluginsConfigMap));
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateErlangCookieSecret), at_step_closure(RabbitmqReconcileStep::AfterCreateDefaultUserSecret));
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateService), at_step_closure(RabbitmqReconcileStep::AfterCreateErlangCookieSecret));
    RMQCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::AfterCreateHeadlessService), at_step_closure(RabbitmqReconcileStep::AfterCreateService));
    RMQCluster::lemma_from_init_state_to_next_state_to_reconcile_idle(spec, rabbitmq, at_step_closure(RabbitmqReconcileStep::Init), at_step_closure(RabbitmqReconcileStep::AfterCreateHeadlessService));
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

pub open spec fn at_step_state_pred(rabbitmq: RabbitmqClusterView, step: RabbitmqReconcileStep) -> StatePred<RMQCluster> {
    RMQCluster::at_expected_reconcile_states(rabbitmq.object_ref(), |s: RabbitmqReconcileState| s.reconcile_step == step)
}

}
