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
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        spec.entails(always(lift_state(VRSCluster::no_pending_req_msg_at_reconcile_state(
            vrs.object_ref(), |s: VReplicaSetReconcileState| s.reconcile_step == VReplicaSetReconcileStep::Init)))),
        spec.entails(always(lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            vrs.object_ref(), |s: VReplicaSetReconcileState| s.reconcile_step == VReplicaSetReconcileStep::AfterListPods)))),
        spec.entails(always(tla_forall(|diff: usize| lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterCreatePod(diff))
            ))))),
        spec.entails(always(tla_forall(|diff: usize| lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterDeletePod(diff))
            ))))),

    ensures spec.entails(true_pred().leads_to(lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref())))),
{
    assert forall |diff: usize| #![auto]
    spec.entails(always(lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterCreatePod(diff))
    )))) by {
        always_tla_forall_apply::<VRSCluster, usize>(
            spec, |diff: usize| lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterCreatePod(diff))
            )), diff
        );
    }
    assert forall |diff: usize| #![auto]
    spec.entails(always(lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterDeletePod(diff))
    )))) by {
        always_tla_forall_apply::<VRSCluster, usize>(
            spec, |diff: usize| lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterDeletePod(diff))
            )), diff
        );
    }

    let reconcile_idle = |s: VRSCluster| { !s.ongoing_reconciles().contains_key(vrs.object_ref()) };

    // First, prove that reconcile_done \/ reconcile_error \/ reconcile_ide ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    VRSCluster::lemma_reconcile_error_leads_to_reconcile_idle(spec, vrs.object_ref());
    VRSCluster::lemma_reconcile_done_leads_to_reconcile_idle(spec, vrs.object_ref());
    temp_pred_equality(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Done)), lift_state(VRSCluster::reconciler_reconcile_done(vrs.object_ref())));
    temp_pred_equality(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error)), lift_state(VRSCluster::reconciler_reconcile_error(vrs.object_ref())));
    entails_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));

    // Second, prove that after_create_pod_rank(0) \/ after_delete_pod_rank(0) ~> reconcile_idle.
    lemma_from_after_create_or_delete_pod_rank_zero_to_reconcile_idle(spec, vrs);

    // Third, prove for all n that AfterCreatePod(n) ~> reconcile_idle.
    assert forall |n: usize| #![auto]
        spec.entails(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n)))
                    .leads_to(lift_state(reconcile_idle))) by {
        assert forall |n: usize| #![trigger after_create_pod_rank(vrs, n)]
                    n > 0 implies spec.entails(lift_state(after_create_pod_rank(vrs, n))
                                    .leads_to(lift_state(after_create_pod_rank(vrs, (n - 1) as usize)))) by {
            lemma_from_after_create_pod_rank_n_to_create_pod_rank_n_minus_1(spec, vrs, n);
        }
        leads_to_rank_step_one_usize(spec, |n| lift_state(after_create_pod_rank(vrs, n)));

        always_implies_to_leads_to(
            spec,
            lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n))),
            lift_state(after_create_pod_rank(vrs, n))
        );
        assert(spec.entails((|n| lift_state(after_create_pod_rank(vrs, n)))(n)
                                .leads_to((|n| lift_state(after_create_pod_rank(vrs, n)))(0))));
        leads_to_trans_n!(
            spec,
            lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n))),
            lift_state(after_create_pod_rank(vrs, n)),
            lift_state(after_create_pod_rank(vrs, 0)),
            lift_state(reconcile_idle)
        );
    }

    // Similarly prove for all n that AfterDeletePod(n) ~> reconcile_idle.
    assert forall |n: usize| #![auto]
        spec.entails(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n)))
                    .leads_to(lift_state(reconcile_idle))) by {
        assert forall |n: usize| #![trigger after_delete_pod_rank(vrs, n)]
                    n > 0 implies spec.entails(lift_state(after_delete_pod_rank(vrs, n))
                                    .leads_to(lift_state(after_delete_pod_rank(vrs, (n - 1) as usize)))) by {
            lemma_from_after_delete_pod_rank_n_to_delete_pod_rank_n_minus_1(spec, vrs, n);
        }
        leads_to_rank_step_one_usize(spec, |n| lift_state(after_delete_pod_rank(vrs, n)));

        always_implies_to_leads_to(
            spec,
            lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n))),
            lift_state(after_delete_pod_rank(vrs, n))
        );
        assert(spec.entails((|n| lift_state(after_delete_pod_rank(vrs, n)))(n)
                            .leads_to((|n| lift_state(after_delete_pod_rank(vrs, n)))(0))));
        leads_to_trans_n!(
            spec,
            lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n))),
            lift_state(after_delete_pod_rank(vrs, n)),
            lift_state(after_delete_pod_rank(vrs, 0)),
            lift_state(reconcile_idle)
        );
    }

    // Fourth, prove that after_list_pods ~> reconcile_idle.
    lemma_from_after_list_pods_to_reconcile_idle(spec, vrs);

    // Fifth, prove that reconcile init state can reach AfterListPods.
    VRSCluster::lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, vrs, at_step_closure(VReplicaSetReconcileStep::Init), at_step_closure(VReplicaSetReconcileStep::AfterListPods));

    // Finally, combine all cases
    leads_to_exists_intro(
        spec,
        |n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n))),
        lift_state(reconcile_idle)
    );
    leads_to_exists_intro(
        spec,
        |n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n))),
        lift_state(reconcile_idle)
    );
    let at_after_create_pod = |n: usize| {
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n)))
    };
    let at_after_delete_pod = |n: usize| {
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n)))
    };

    lemma_true_equal_to_reconcile_idle_or_at_any_state(vrs);

    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Init)),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterListPods)),
        tla_exists(at_after_create_pod),
        tla_exists(at_after_delete_pod),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Done)),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error));
        lift_state(reconcile_idle)
    );
}

pub open spec fn at_step_state_pred(vrs: VReplicaSetView, step: VReplicaSetReconcileStep) -> StatePred<VRSCluster> {
    VRSCluster::at_expected_reconcile_states(vrs.object_ref(), |s: VReplicaSetReconcileState| s.reconcile_step == step)
}

pub open spec fn after_create_pod_rank(vrs: VReplicaSetView, diff: usize) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        ||| at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(diff))(s)
        // There may have been an error as well.
        ||| at_step_state_pred(vrs, VReplicaSetReconcileStep::Error)(s)
    }
}

pub open spec fn after_delete_pod_rank(vrs: VReplicaSetView, diff: usize) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        ||| at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(diff))(s)
        // There may have been an error as well.
        ||| at_step_state_pred(vrs, VReplicaSetReconcileStep::Error)(s)
    }
}

proof fn lemma_from_after_create_or_delete_pod_rank_zero_to_reconcile_idle(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView
)
    requires
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        // Make sure there is a message in flight, so we can progress to the next state.
        spec.entails(always(lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterCreatePod(0)))))),
        spec.entails(always(lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterDeletePod(0)))))),
        // The next state will lead to reconcile_idle.
        spec.entails(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Done))
            .leads_to(lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref())))),
        spec.entails(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error))
            .leads_to(lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref())))),
    ensures
        spec.entails(lift_state(after_create_pod_rank(vrs, 0))
            .leads_to(lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref())))),
        spec.entails(lift_state(after_delete_pod_rank(vrs, 0))
            .leads_to(lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref())))),
{
    let state_after_create_or_delete = |s: VReplicaSetReconcileState| {
        s.reconcile_step == VReplicaSetReconcileStep::Done
        || s.reconcile_step == VReplicaSetReconcileStep::Error
    };
    or_leads_to_combine_and_equality!(
        spec, lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), state_after_create_or_delete)),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Done)),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error));
        lift_state(|s: VRSCluster| { !s.ongoing_reconciles().contains_key(vrs.object_ref()) })
    );

    VRSCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, vrs, at_step_closure(VReplicaSetReconcileStep::AfterCreatePod(0)), state_after_create_or_delete);
    VRSCluster::lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, vrs, at_step_closure(VReplicaSetReconcileStep::AfterDeletePod(0)), state_after_create_or_delete);

    or_leads_to_combine_and_equality!(
        spec, lift_state(after_create_pod_rank(vrs, 0)),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(0))),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error));
        lift_state(|s: VRSCluster| { !s.ongoing_reconciles().contains_key(vrs.object_ref()) })
    );
    or_leads_to_combine_and_equality!(
        spec, lift_state(after_delete_pod_rank(vrs, 0)),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(0))),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error));
        lift_state(|s: VRSCluster| { !s.ongoing_reconciles().contains_key(vrs.object_ref()) })
    );
}

proof fn lemma_from_after_create_pod_rank_n_to_create_pod_rank_n_minus_1(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, n: usize
)
    requires
        n > 0,
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        // Make sure there is a message in flight, so we can progress to the next state.
        spec.entails(always(lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterCreatePod(n)))))),
    ensures
        spec.entails(lift_state(after_create_pod_rank(vrs, n))
            .leads_to(lift_state(after_create_pod_rank(vrs, (n - 1) as usize)))),
{
    let state_after_create = |s: VReplicaSetReconcileState| {
        s.reconcile_step == VReplicaSetReconcileStep::AfterCreatePod((n - 1) as usize)
        || s.reconcile_step == VReplicaSetReconcileStep::Error
    };

    entails_implies_leads_to(
        spec,
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error)),
        lift_state(after_create_pod_rank(vrs, (n - 1) as usize))
    );

    VRSCluster::lemma_from_some_state_to_arbitrary_next_state(spec, vrs, at_step_closure(VReplicaSetReconcileStep::AfterCreatePod(n)), state_after_create);

    always_implies_to_leads_to(
        spec,
        lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), state_after_create)),
        lift_state(after_create_pod_rank(vrs, (n - 1) as usize))
    );
    leads_to_trans_n!(
        spec,
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n))),
        lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), state_after_create)),
        lift_state(after_create_pod_rank(vrs, (n - 1) as usize))
    );

    or_leads_to_combine_and_equality!(
        spec, lift_state(after_create_pod_rank(vrs, n)),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n))),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error));
        lift_state(after_create_pod_rank(vrs, (n - 1) as usize))
    );
}

proof fn lemma_from_after_delete_pod_rank_n_to_delete_pod_rank_n_minus_1(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, n: usize
)
    requires
        n > 0,
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        // Make sure there is a message in flight, so we can progress to the next state.
        spec.entails(always(lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterDeletePod(n)))))),
    ensures
        spec.entails(lift_state(after_delete_pod_rank(vrs, n))
            .leads_to(lift_state(after_delete_pod_rank(vrs, (n - 1) as usize)))),
{
    let state_after_delete = |s: VReplicaSetReconcileState| {
        s.reconcile_step == VReplicaSetReconcileStep::AfterDeletePod((n - 1) as usize)
        || s.reconcile_step == VReplicaSetReconcileStep::Error
    };

    entails_implies_leads_to(
        spec,
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error)),
        lift_state(after_delete_pod_rank(vrs, (n - 1) as usize))
    );

    VRSCluster::lemma_from_some_state_to_arbitrary_next_state(spec, vrs, at_step_closure(VReplicaSetReconcileStep::AfterDeletePod(n)), state_after_delete);

    always_implies_to_leads_to(
        spec,
        lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), state_after_delete)),
        lift_state(after_delete_pod_rank(vrs, (n - 1) as usize))
    );
    leads_to_trans_n!(
        spec,
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n))),
        lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), state_after_delete)),
        lift_state(after_delete_pod_rank(vrs, (n - 1) as usize))
    );

    or_leads_to_combine_and_equality!(
        spec, lift_state(after_delete_pod_rank(vrs, n)),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n))),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error));
        lift_state(after_delete_pod_rank(vrs, (n - 1) as usize))
    );
}

proof fn lemma_from_after_list_pods_to_reconcile_idle(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView
)
    requires
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::external_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        // Make sure there is a message in flight, so we can progress to the next state.
        spec.entails(always(lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            vrs.object_ref(), |s: VReplicaSetReconcileState| s.reconcile_step == VReplicaSetReconcileStep::AfterListPods)))),
        // The next state will lead to reconcile_idle.
        forall |n: usize| #![auto]
            spec.entails(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n)))
                .leads_to(lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref())))),
        forall |n: usize| #![auto]
            spec.entails(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n)))
                .leads_to(lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref())))),
        spec.entails(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Done))
            .leads_to(lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref())))),
        spec.entails(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error))
            .leads_to(lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref())))),
    ensures
        spec.entails(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterListPods))
            .leads_to(lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref())))),
{
    let state_after_list_pods = |s: VReplicaSetReconcileState| {
        ||| exists |n: usize| s.reconcile_step == VReplicaSetReconcileStep::AfterCreatePod(n)
        ||| exists |n: usize| s.reconcile_step == VReplicaSetReconcileStep::AfterDeletePod(n)
        ||| s.reconcile_step == VReplicaSetReconcileStep::Done
        ||| s.reconcile_step == VReplicaSetReconcileStep::Error
    };
    leads_to_exists_intro(
        spec,
        |n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n))),
        lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref()))
    );
    leads_to_exists_intro(
        spec,
        |n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n))),
        lift_state(|s: VRSCluster| !s.ongoing_reconciles().contains_key(vrs.object_ref()))
    );
    let at_after_create_pod = |n: usize| {
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n)))
    };
    let at_after_delete_pod = |n: usize| {
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n)))
    };

    assert_by(
        tla_exists(at_after_create_pod) ==
        lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), |s: VReplicaSetReconcileState|
        exists |n: usize| s.reconcile_step == VReplicaSetReconcileStep::AfterCreatePod(n))),
        {
            assert forall |ex| #![auto]
            lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), |s: VReplicaSetReconcileState|
            exists |n: usize| s.reconcile_step == VReplicaSetReconcileStep::AfterCreatePod(n))).satisfied_by(ex) implies
            tla_exists(at_after_create_pod).satisfied_by(ex) by {
                let s = ex.head().ongoing_reconciles()[vrs.object_ref()].local_state;
                let witness_n = choose |n: usize| s.reconcile_step == VReplicaSetReconcileStep::AfterCreatePod(n);
                assert(at_after_create_pod(witness_n).satisfied_by(ex));
            }

            temp_pred_equality(
                tla_exists(at_after_create_pod),
                lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), |s: VReplicaSetReconcileState|
                exists |n: usize| s.reconcile_step == VReplicaSetReconcileStep::AfterCreatePod(n)))
            );
        }
    );
    assert_by(
        tla_exists(at_after_delete_pod) ==
        lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), |s: VReplicaSetReconcileState|
        exists |n: usize| s.reconcile_step == VReplicaSetReconcileStep::AfterDeletePod(n))),
        {
            assert forall |ex| #![auto]
            lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), |s: VReplicaSetReconcileState|
            exists |n: usize| s.reconcile_step == VReplicaSetReconcileStep::AfterDeletePod(n))).satisfied_by(ex) implies
            tla_exists(at_after_delete_pod).satisfied_by(ex) by {
                let s = ex.head().ongoing_reconciles()[vrs.object_ref()].local_state;
                let witness_n = choose |n: usize| s.reconcile_step == VReplicaSetReconcileStep::AfterDeletePod(n);
                assert(at_after_delete_pod(witness_n).satisfied_by(ex));
            }

            temp_pred_equality(
                tla_exists(at_after_delete_pod),
                lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), |s: VReplicaSetReconcileState|
                exists |n: usize| s.reconcile_step == VReplicaSetReconcileStep::AfterDeletePod(n)))
            );
        }
    );
    or_leads_to_combine_and_equality!(
        spec, lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), state_after_list_pods)),
        tla_exists(at_after_create_pod),
        tla_exists(at_after_delete_pod),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Done)),
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error));
        lift_state(|s: VRSCluster| { !s.ongoing_reconciles().contains_key(vrs.object_ref()) })
    );


    VRSCluster::lemma_from_some_state_to_arbitrary_next_state(spec, vrs, at_step_closure(VReplicaSetReconcileStep::AfterListPods), state_after_list_pods);

    leads_to_trans_n!(
        spec,
        lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterListPods)),
        lift_state(VRSCluster::at_expected_reconcile_states(vrs.object_ref(), state_after_list_pods)),
        lift_state(|s: VRSCluster| { !s.ongoing_reconciles().contains_key(vrs.object_ref()) })
    );
}

proof fn lemma_true_equal_to_reconcile_idle_or_at_any_state(vrs: VReplicaSetView)
    ensures true_pred::<VRSCluster>()
                == lift_state(|s: VRSCluster| { !s.ongoing_reconciles().contains_key(vrs.object_ref()) })
                    .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Init)))
                    .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterListPods)))
                    .or(tla_exists(|n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n)))))
                    .or(tla_exists(|n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n)))))
                    .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Done)))
                    .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error)))
{
    let rhs = lift_state(|s: VRSCluster| { !s.ongoing_reconciles().contains_key(vrs.object_ref()) })
                .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Init)))
                .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterListPods)))
                .or(tla_exists(|n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n)))))
                .or(tla_exists(|n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n)))))
                .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Done)))
                .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error)));

    assert forall |ex| #![auto] true_pred::<VRSCluster>().satisfied_by(ex) implies rhs.satisfied_by(ex) by {
        let s = ex.head();
        if s.ongoing_reconciles().contains_key(vrs.object_ref()) {
            let step = s.ongoing_reconciles()[vrs.object_ref()].local_state.reconcile_step;
            match step {
                VReplicaSetReconcileStep::AfterCreatePod(n) => {
                    // Introduce tla_exists with n as witness.
                    assert((|n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n))))(n).satisfied_by(ex));
                    assert(tla_exists(|n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n)))).satisfied_by(ex));
                },
                VReplicaSetReconcileStep::AfterDeletePod(n) => {
                    // Introduce tla_exists with n as witness.
                    assert((|n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n))))(n).satisfied_by(ex));
                    assert(tla_exists(|n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n)))).satisfied_by(ex));
                },
                step => {},
            }
        }
    }

    temp_pred_equality(
        true_pred::<VRSCluster>(),
        lift_state(|s: VRSCluster| { !s.ongoing_reconciles().contains_key(vrs.object_ref()) })
            .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Init)))
            .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterListPods)))
            .or(tla_exists(|n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterCreatePod(n)))))
            .or(tla_exists(|n| lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::AfterDeletePod(n)))))
            .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Done)))
            .or(lift_state(at_step_state_pred(vrs, VReplicaSetReconcileStep::Error)))
    );
}

}
