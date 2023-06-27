// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::{
    proof::{
        cluster::*, cluster_safety, controller_runtime_liveness, controller_runtime_safety,
        kubernetes_api_liveness, kubernetes_api_safety,
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
    proof::{common::*, safety, terminate},
    spec::{reconciler::*, zookeepercluster::*},
};
use vstd::prelude::*;

verus! {

spec fn desired_state_exists(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.resource_key_exists(zk.object_ref())
        &&& ZookeeperClusterView::from_dynamic_object(s.resource_obj_of(zk.object_ref())).is_Ok()
    }
}

spec fn desired_state_is(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.resource_key_exists(zk.object_ref())
        &&& ZookeeperClusterView::from_dynamic_object(s.resource_obj_of(zk.object_ref())).is_Ok()
        &&& ZookeeperClusterView::from_dynamic_object(s.resource_obj_of(zk.object_ref())).get_Ok_0().spec == zk.spec
    }
}

spec fn current_state_matches(zk: ZookeeperClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(zk.object_ref()))).is_Ok()
        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(zk.object_ref()))).get_Ok_0().spec == make_stateful_set(zk).spec
    }
}

spec fn liveness(zk: ZookeeperClusterView) -> TempPred<ClusterState>
    recommends
        zk.well_formed(),
{
    always(lift_state(desired_state_is(zk))).leads_to(always(lift_state(current_state_matches(zk))))
}

proof fn liveness_proof_forall_zk()
    ensures
        forall |zk: ZookeeperClusterView| zk.well_formed() ==> #[trigger] cluster_spec().entails(liveness(zk)),
{
    assert forall |zk: ZookeeperClusterView| zk.well_formed()
    implies #[trigger] cluster_spec().entails(liveness(zk)) by {
        liveness_proof(zk);
    };
}

#[verifier(external_body)]
proof fn lemma_always_desired_state_exists(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        spec.entails(always(lift_state(desired_state_is(zk)))),
    ensures
        spec.entails(always(lift_state(desired_state_exists(zk)))),
{}

// TODO: generalize this
proof fn lemma_true_leads_to_always_the_object_in_schedule_has_spec_as(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(zk)))),
        spec.entails(always(lift_state(cluster_safety::each_object_in_etcd_is_well_formed()))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(safety::the_object_in_schedule_has_spec_as(zk))))),
{
    let pre = |s: ClusterState| true;
    let post = safety::the_object_in_schedule_has_spec_as(zk);
    let input = zk.object_ref();
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& desired_state_is(zk)(s)
        &&& cluster_safety::each_object_in_etcd_is_well_formed()(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(desired_state_is(zk)),
        lift_state(cluster_safety::each_object_in_etcd_is_well_formed())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(desired_state_is(zk)))
        .and(lift_state(cluster_safety::each_object_in_etcd_is_well_formed()))
    );

    lemma_always_desired_state_exists(spec, zk);
    temp_pred_equality::<ClusterState>(
        lift_state(desired_state_exists(zk)), lift_state(schedule_controller_reconcile().pre(input))
    );

    spec_implies_pre(spec, lift_state(pre), lift_state(schedule_controller_reconcile().pre(input)));
    use_tla_forall::<ClusterState, ObjectRef>(spec, |key| schedule_controller_reconcile().weak_fairness(key), input);

    schedule_controller_reconcile().wf1(input, spec, stronger_next, pre, post);
    leads_to_stable_temp(spec, lift_action(stronger_next), lift_state(pre), lift_state(post));
}

// TODO: generalize this
proof fn lemma_true_leads_to_always_the_object_in_reconcile_has_spec_as(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(tla_forall(|i| schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(zk)))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(cluster_safety::each_object_in_etcd_is_well_formed()))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(safety::the_object_in_reconcile_has_spec_as(zk))))),
{
    // We need to prepare a concrete spec which is stable because we will use unpack_conditions_from_spec later
    let stable_spec = always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))
        .and(tla_forall(|i| schedule_controller_reconcile().weak_fairness(i)))
        .and(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i)))
        .and(tla_forall(|i| kubernetes_api_next().weak_fairness(i)))
        .and(always(lift_state(desired_state_is(zk))))
        .and(always(lift_state(crash_disabled())))
        .and(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())))
        .and(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref()))))
        .and(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))))
        .and(always(lift_state(cluster_safety::each_object_in_etcd_is_well_formed())));

    let stable_spec_with_assumption = stable_spec.and(always(lift_state(safety::the_object_in_schedule_has_spec_as(zk))));

    // Let's first prove true ~> []the_object_in_reconcile_has_spec_as(zk)
    assert_by(
        stable_spec_with_assumption
        .entails(
            true_pred().leads_to(always(lift_state(safety::the_object_in_reconcile_has_spec_as(zk))))
        ),
        {
            let stronger_next = |s, s_prime: ClusterState| {
                &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
                &&& desired_state_is(zk)(s)
                &&& crash_disabled()(s)
                &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
                &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
                &&& controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
                &&& cluster_safety::each_object_in_etcd_is_well_formed()(s)
                &&& safety::the_object_in_schedule_has_spec_as(zk)(s)
            };
            entails_always_and_n!(
                stable_spec_with_assumption,
                lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
                lift_state(desired_state_is(zk)),
                lift_state(crash_disabled()),
                lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()),
                lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
                lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())),
                lift_state(cluster_safety::each_object_in_etcd_is_well_formed()),
                lift_state(safety::the_object_in_schedule_has_spec_as(zk))
            );
            temp_pred_equality(
                lift_action(stronger_next),
                lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
                .and(lift_state(desired_state_is(zk)))
                .and(lift_state(crash_disabled()))
                .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
                .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
                .and(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
                .and(lift_state(cluster_safety::each_object_in_etcd_is_well_formed()))
                .and(lift_state(safety::the_object_in_schedule_has_spec_as(zk)))
            );

            terminate::reconcile_eventually_terminates(stable_spec_with_assumption, zk);

            // Here we split the cases by whether s.reconcile_scheduled_for(zk.object_ref()) is true
            assert_by(
                stable_spec_with_assumption
                .entails(
                    lift_state(|s: ClusterState| {
                        &&& !s.reconcile_state_contains(zk.object_ref())
                        &&& s.reconcile_scheduled_for(zk.object_ref())
                    }).leads_to(lift_state(safety::the_object_in_reconcile_has_spec_as(zk)))
                ),
                {
                    let pre = |s: ClusterState| {
                        &&& !s.reconcile_state_contains(zk.object_ref())
                        &&& s.reconcile_scheduled_for(zk.object_ref())
                    };
                    let post = safety::the_object_in_reconcile_has_spec_as(zk);
                    let input = (Option::None, Option::Some(zk.object_ref()));
                    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
                        stable_spec_with_assumption, input, stronger_next,
                        run_scheduled_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(), pre, post
                    );
                }
            );

            assert_by(
                stable_spec_with_assumption
                .entails(
                    lift_state(|s: ClusterState| {
                        &&& !s.reconcile_state_contains(zk.object_ref())
                        &&& !s.reconcile_scheduled_for(zk.object_ref())
                    }).leads_to(lift_state(safety::the_object_in_reconcile_has_spec_as(zk)))
                ),
                {
                    let pre = |s: ClusterState| {
                        &&& !s.reconcile_state_contains(zk.object_ref())
                        &&& !s.reconcile_scheduled_for(zk.object_ref())
                    };
                    let post = |s: ClusterState| {
                        &&& !s.reconcile_state_contains(zk.object_ref())
                        &&& s.reconcile_scheduled_for(zk.object_ref())
                    };
                    let input = zk.object_ref();

                    lemma_always_desired_state_exists(stable_spec_with_assumption, zk);
                    temp_pred_equality::<ClusterState>(
                        lift_state(desired_state_exists(zk)), lift_state(schedule_controller_reconcile().pre(input))
                    );
                    spec_implies_pre(stable_spec_with_assumption, lift_state(pre), lift_state(schedule_controller_reconcile().pre(input)));
                    use_tla_forall::<ClusterState, ObjectRef>(stable_spec_with_assumption, |key| schedule_controller_reconcile().weak_fairness(key), input);
                    schedule_controller_reconcile().wf1(input, stable_spec_with_assumption, stronger_next, pre, post);
                    leads_to_trans_temp(stable_spec_with_assumption, lift_state(pre), lift_state(post), lift_state(safety::the_object_in_reconcile_has_spec_as(zk)));
                }
            );

            or_leads_to_combine_temp(
                stable_spec_with_assumption,
                lift_state(|s: ClusterState| {
                    &&& !s.reconcile_state_contains(zk.object_ref())
                    &&& s.reconcile_scheduled_for(zk.object_ref())
                }),
                lift_state(|s: ClusterState| {
                    &&& !s.reconcile_state_contains(zk.object_ref())
                    &&& !s.reconcile_scheduled_for(zk.object_ref())
                }),
                lift_state(safety::the_object_in_reconcile_has_spec_as(zk))
            );

            temp_pred_equality(
                lift_state(|s: ClusterState| {
                    &&& !s.reconcile_state_contains(zk.object_ref())
                    &&& s.reconcile_scheduled_for(zk.object_ref())
                }).or(lift_state(|s: ClusterState| {
                    &&& !s.reconcile_state_contains(zk.object_ref())
                    &&& !s.reconcile_scheduled_for(zk.object_ref())
                })),
                lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref()))
            );

            leads_to_trans_temp(
                stable_spec_with_assumption,
                true_pred(),
                lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())),
                lift_state(safety::the_object_in_reconcile_has_spec_as(zk))
            );
            leads_to_stable_temp(stable_spec_with_assumption, lift_action(stronger_next), true_pred(), lift_state(safety::the_object_in_reconcile_has_spec_as(zk)));
        }
    );

    // By unpacking the conditions we will have: stable_spec |= []the_object_in_schedule_has_spec_as(zk) ~> []the_object_in_reconcile_has_spec_as(zk)
    assume(valid(stable(stable_spec)));
    unpack_conditions_from_spec(
        stable_spec,
        always(lift_state(safety::the_object_in_schedule_has_spec_as(zk))),
        true_pred(),
        always(lift_state(safety::the_object_in_reconcile_has_spec_as(zk)))
    );
    temp_pred_equality(true_pred().and(always(lift_state(safety::the_object_in_schedule_has_spec_as(zk)))), always(lift_state(safety::the_object_in_schedule_has_spec_as(zk))));

    // Now we use the previously proved lemma: stable_spec |= true ~> []the_object_in_schedule_has_spec_as(zk)
    lemma_true_leads_to_always_the_object_in_schedule_has_spec_as(stable_spec, zk);

    leads_to_trans_temp(stable_spec, true_pred(), always(lift_state(safety::the_object_in_schedule_has_spec_as(zk))), always(lift_state(safety::the_object_in_reconcile_has_spec_as(zk))));

    // Because spec might be different from stable_spec, we need this extra step
    entails_and_n!(
        spec,
        always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())),
        tla_forall(|i| schedule_controller_reconcile().weak_fairness(i)),
        tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i)),
        tla_forall(|i| kubernetes_api_next().weak_fairness(i)),
        always(lift_state(desired_state_is(zk))),
        always(lift_state(crash_disabled())),
        always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())),
        always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref()))),
        always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))),
        always(lift_state(cluster_safety::each_object_in_etcd_is_well_formed()))
    );
    entails_trans(spec, stable_spec, true_pred().leads_to(always(lift_state(safety::the_object_in_reconcile_has_spec_as(zk)))));
}

spec fn next_with_wf() -> TempPred<ClusterState> {
    always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))
    .and(tla_forall(|input| kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(input)))
    .and(tla_forall(|input| schedule_controller_reconcile().weak_fairness(input)))
    .and(disable_crash().weak_fairness(()))
}

spec fn assumptions(zk: ZookeeperClusterView) -> TempPred<ClusterState> {
    always(lift_state(crash_disabled()))
    .and(always(lift_state(desired_state_is(zk))))
    .and(always(lift_state(safety::the_object_in_schedule_has_spec_as(zk))))
    .and(always(lift_state(safety::the_object_in_reconcile_has_spec_as(zk))))
}

spec fn invariants(zk: ZookeeperClusterView) -> TempPred<ClusterState> {
    always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref()))))
    .and(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))))
    .and(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(cluster_safety::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(cluster_safety::each_scheduled_key_is_consistent_with_its_object())))
    .and(always(lift_state(cluster_safety::each_key_in_reconcile_is_consistent_with_its_object())))
    .and(always(lift_state(safety::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(zk.object_ref()))))
    .and(always(lift_state(safety::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(zk.object_ref()))))
}

spec fn invariants_since_rest_id(zk: ZookeeperClusterView, rest_id: RestId) -> TempPred<ClusterState> {
    always(lift_state(rest_id_counter_is_no_smaller_than(rest_id)))
    .and(always(lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))))
    .and(always(lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))))
    .and(always(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))))
    .and(always(lift_state(safety::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id))))
}

spec fn invariants_led_to_by_rest_id(zk: ZookeeperClusterView, rest_id: RestId) -> TempPred<ClusterState> {
    always(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))
}

proof fn liveness_proof(zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
    ensures
        cluster_spec().entails(liveness(zk)),
{
    assert_by(
        next_with_wf().and(invariants(zk)).and(assumptions(zk))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            let spec = next_with_wf().and(invariants(zk)).and(assumptions(zk));

            let idle = lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref()));
            let idle_and_rest_id_is = |rest_id| lift_state(rest_id_counter_is(rest_id)).and(idle);
            assert forall |rest_id|
            spec.entails(#[trigger] idle_and_rest_id_is(rest_id).leads_to(always(lift_state(current_state_matches(zk))))) by {
                lemma_true_leads_to_always_current_state_matches_zk_from_idle_with_rest_id(zk, rest_id);
                assume(valid(stable(spec)));
                temp_pred_equality(
                    lift_state(rest_id_counter_is(rest_id))
                    .and(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
                    .and(next_with_wf()).and(invariants(zk)).and(assumptions(zk)),
                    spec.and(idle_and_rest_id_is(rest_id))
                );
                unpack_conditions_from_spec(spec, idle_and_rest_id_is(rest_id), true_pred(), always(lift_state(current_state_matches(zk))));
                temp_pred_equality(true_pred().and(idle_and_rest_id_is(rest_id)), idle_and_rest_id_is(rest_id));
            }

            leads_to_exists_intro(spec, idle_and_rest_id_is, always(lift_state(current_state_matches(zk))));

            assert_by(
                tla_exists(idle_and_rest_id_is) == idle,
                {
                    assert forall |ex| #[trigger] idle.satisfied_by(ex)
                    implies tla_exists(idle_and_rest_id_is).satisfied_by(ex) by {
                        let rest_id = ex.head().rest_id_allocator.rest_id_counter;
                        assert(idle_and_rest_id_is(rest_id).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(idle_and_rest_id_is), idle);
                }
            );

            terminate::reconcile_eventually_terminates(spec, zk);

            leads_to_trans_temp(spec, true_pred(), idle, always(lift_state(current_state_matches(zk))));
        }
    );

    assert_by(
        next_with_wf().and(invariants(zk)).and(always(lift_state(desired_state_is(zk)))).and(always(lift_state(crash_disabled())))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            let spec = next_with_wf().and(invariants(zk)).and(always(lift_state(desired_state_is(zk)))).and(always(lift_state(crash_disabled())));
            let other_assumptions = always(lift_state(safety::the_object_in_schedule_has_spec_as(zk)))
                .and(always(lift_state(safety::the_object_in_reconcile_has_spec_as(zk))));
            temp_pred_equality(
                next_with_wf().and(invariants(zk)).and(assumptions(zk)),
                next_with_wf().and(invariants(zk)).and(always(lift_state(desired_state_is(zk)))).and(always(lift_state(crash_disabled()))).and(other_assumptions)
            );
            assume(valid(stable(spec)));
            unpack_conditions_from_spec(spec, other_assumptions, true_pred(), always(lift_state(current_state_matches(zk))));
            temp_pred_equality(true_pred().and(other_assumptions), other_assumptions);

            lemma_true_leads_to_always_the_object_in_schedule_has_spec_as(spec, zk);
            lemma_true_leads_to_always_the_object_in_reconcile_has_spec_as(spec, zk);

            leads_to_always_combine_n!(
                spec, true_pred(),
                lift_state(safety::the_object_in_schedule_has_spec_as(zk)),
                lift_state(safety::the_object_in_reconcile_has_spec_as(zk))
            );

            always_and_equality_n!(
                lift_state(safety::the_object_in_schedule_has_spec_as(zk)),
                lift_state(safety::the_object_in_reconcile_has_spec_as(zk))
            );

            leads_to_trans_temp(spec, true_pred(), other_assumptions, always(lift_state(current_state_matches(zk))));
        }
    );

    assert_by(
        next_with_wf().and(invariants(zk)).and(always(lift_state(desired_state_is(zk))))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            let spec = next_with_wf().and(invariants(zk)).and(always(lift_state(desired_state_is(zk))));
            assume(valid(stable(spec)));
            unpack_conditions_from_spec(spec, always(lift_state(crash_disabled())), true_pred(), always(lift_state(current_state_matches(zk))));
            temp_pred_equality(true_pred().and(always(lift_state(crash_disabled()))), always(lift_state(crash_disabled::<ZookeeperClusterView, ZookeeperReconcileState>())));

            lemma_true_leads_to_crash_always_disabled::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec);

            leads_to_trans_temp(spec, true_pred(), always(lift_state(crash_disabled())), always(lift_state(current_state_matches(zk))));
        }
    );

    assert_by(
        next_with_wf().and(invariants(zk))
        .entails(
            always(lift_state(desired_state_is(zk))).leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            let spec = next_with_wf().and(invariants(zk));
            let assumption = always(lift_state(desired_state_is(zk)));
            assume(valid(stable(spec)));
            unpack_conditions_from_spec(spec, assumption, true_pred(), always(lift_state(current_state_matches(zk))));
            temp_pred_equality(true_pred().and(assumption), assumption);
        }
    );

    assert_by(
        cluster_spec()
        .entails(
            always(lift_state(desired_state_is(zk))).leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            let spec = cluster_spec();

            entails_trans(
                spec.and(invariants(zk)), next_with_wf().and(invariants(zk)),
                always(lift_state(desired_state_is(zk))).leads_to(always(lift_state(current_state_matches(zk))))
            );

            controller_runtime_safety::lemma_always_every_in_flight_msg_has_unique_id::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>();
            controller_runtime_safety::lemma_always_each_resp_matches_at_most_one_pending_req::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
            controller_runtime_safety::lemma_always_each_resp_if_matches_pending_req_then_no_other_resp_matches::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(zk.object_ref());
            controller_runtime_safety::lemma_always_every_in_flight_msg_has_lower_id_than_allocator::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>();
            cluster_safety::lemma_always_each_object_in_etcd_is_well_formed::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec);
            cluster_safety::lemma_always_each_scheduled_key_is_consistent_with_its_object::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec);
            cluster_safety::lemma_always_each_key_in_reconcile_is_consistent_with_its_object::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec);
            safety::lemma_always_pending_msg_at_after_create_stateful_set_step_is_create_sts_req(spec, zk.object_ref());
            safety::lemma_always_pending_msg_at_after_update_stateful_set_step_is_update_sts_req(spec, zk.object_ref());

            entails_and_n!(
                spec,
                always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id())),
                always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref()))),
                always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))),
                always(lift_state(controller_runtime_safety::every_in_flight_msg_has_lower_id_than_allocator())),
                always(lift_state(cluster_safety::each_object_in_etcd_is_well_formed())),
                always(lift_state(cluster_safety::each_scheduled_key_is_consistent_with_its_object())),
                always(lift_state(cluster_safety::each_key_in_reconcile_is_consistent_with_its_object())),
                always(lift_state(safety::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(zk.object_ref()))),
                always(lift_state(safety::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(zk.object_ref())))
            );

            simplify_predicate(spec, invariants(zk));
        }
    );

}

proof fn lemma_true_leads_to_always_current_state_matches_zk_from_idle_with_rest_id(zk: ZookeeperClusterView, rest_id: RestId)
    requires
        zk.well_formed(),
    ensures
        lift_state(rest_id_counter_is(rest_id))
        .and(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        .and(next_with_wf()).and(invariants(zk)).and(assumptions(zk))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(zk))))
        ),
{
    let stable_spec = next_with_wf().and(invariants(zk)).and(assumptions(zk));
    let spec = lift_state(rest_id_counter_is(rest_id))
        .and(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        .and(next_with_wf())
        .and(invariants(zk))
        .and(assumptions(zk));

    assert_by(
        spec.and(invariants_since_rest_id(zk, rest_id)).entails(
            invariants_led_to_by_rest_id(zk, rest_id).leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            lemma_true_leads_to_always_current_state_matches_zk_under_eventual_invariants(zk, rest_id);
            assume(valid(stable(stable_spec.and(invariants_since_rest_id(zk, rest_id)))));
            unpack_conditions_from_spec(
                stable_spec.and(invariants_since_rest_id(zk, rest_id)),
                invariants_led_to_by_rest_id(zk, rest_id),
                true_pred(),
                always(lift_state(current_state_matches(zk)))
            );
            temp_pred_equality(
                true_pred().and(invariants_led_to_by_rest_id(zk, rest_id)),
                invariants_led_to_by_rest_id(zk, rest_id)
            );
            entails_trans(
                spec.and(invariants_since_rest_id(zk, rest_id)),
                stable_spec.and(invariants_since_rest_id(zk, rest_id)),
                invariants_led_to_by_rest_id(zk, rest_id).leads_to(always(lift_state(current_state_matches(zk))))
            );
        }
    );

    kubernetes_api_liveness::lemma_true_leads_to_always_no_req_before_rest_id_is_in_flight::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec.and(invariants_since_rest_id(zk, rest_id)), rest_id
    );

    leads_to_trans_temp(spec.and(invariants_since_rest_id(zk, rest_id)), true_pred(), invariants_led_to_by_rest_id(zk, rest_id), always(lift_state(current_state_matches(zk))));

    assert_by(
        spec.entails(invariants_since_rest_id(zk, rest_id)),
        {
            eliminate_always(spec, lift_state(controller_runtime_safety::every_in_flight_msg_has_lower_id_than_allocator()));
            eliminate_always(spec, lift_state(safety::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(zk.object_ref())));
            eliminate_always(spec, lift_state(safety::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(zk.object_ref())));

            cluster_safety::lemma_always_rest_id_counter_is_no_smaller_than::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(spec, rest_id);
            safety::lemma_always_at_most_one_create_sts_req_since_rest_id_is_in_flight(spec, zk.object_ref(), rest_id);
            safety::lemma_always_at_most_one_update_sts_req_since_rest_id_is_in_flight(spec, zk.object_ref(), rest_id);
            safety::lemma_always_no_delete_sts_req_since_rest_id_is_in_flight(spec, zk.object_ref(), rest_id);
            safety::lemma_always_every_update_sts_req_since_rest_id_does_the_same(spec, zk, rest_id);

            entails_and_n!(
                spec,
                always(lift_state(rest_id_counter_is_no_smaller_than(rest_id))),
                always(lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))),
                always(lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))),
                always(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))),
                always(lift_state(safety::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id)))
            );
        }
    );

    simplify_predicate(spec, invariants_since_rest_id(zk, rest_id));
}


proof fn lemma_true_leads_to_always_current_state_matches_zk_under_eventual_invariants(zk: ZookeeperClusterView, rest_id: RestId)
    requires
        zk.well_formed(),
    ensures
        next_with_wf()
        .and(invariants(zk))
        .and(assumptions(zk))
        .and(invariants_since_rest_id(zk, rest_id))
        .and(invariants_led_to_by_rest_id(zk, rest_id))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(zk))))
        ),
{
    let spec = next_with_wf()
        .and(invariants(zk))
        .and(assumptions(zk))
        .and(invariants_since_rest_id(zk, rest_id))
        .and(invariants_led_to_by_rest_id(zk, rest_id));

    lemma_always_desired_state_exists(spec, zk);

    assert_by(
        spec.entails(
            true_pred().leads_to(lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())))
        ),
        {
            terminate::reconcile_eventually_terminates(spec, zk);
        }
    );

    assert_by(
        spec.entails(
            lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref()))
                .leads_to(lift_state(at_init_step_with_no_pending_req(zk)))
        ),
        {
            let unscheduled_and_not_in_reconcile = lift_state(|s: ClusterState| {
                &&& !s.reconcile_state_contains(zk.object_ref())
                &&& !s.reconcile_scheduled_for(zk.object_ref())
            });
            let scheduled_and_not_in_reconcile = lift_state(|s: ClusterState| {
                &&& !s.reconcile_state_contains(zk.object_ref())
                &&& s.reconcile_scheduled_for(zk.object_ref())
            });
            lemma_from_unscheduled_to_scheduled(spec, zk);
            lemma_from_scheduled_to_init_step(spec, zk);
            leads_to_trans_temp(
                spec,
                unscheduled_and_not_in_reconcile,
                scheduled_and_not_in_reconcile,
                lift_state(at_init_step_with_no_pending_req(zk))
            );
            or_leads_to_combine_temp(
                spec,
                unscheduled_and_not_in_reconcile,
                scheduled_and_not_in_reconcile,
                lift_state(at_init_step_with_no_pending_req(zk))
            );
            temp_pred_equality(
                lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())),
                unscheduled_and_not_in_reconcile.or(scheduled_and_not_in_reconcile)
            );
        }
    );

    assert_by(
        spec.entails(
            lift_state(at_init_step_with_no_pending_req(zk))
                .leads_to(lift_state(at_after_create_headless_service_step_with_zk_and_pending_req_in_flight(zk)))
        ),
        {
            lemma_from_init_step_to_after_create_headless_service_step(spec, zk);
        }
    );

    assert_by(
        spec.entails(
            lift_state(at_after_create_headless_service_step_with_zk_and_pending_req_in_flight(zk))
                .leads_to(lift_state(at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk)))
        ),
        {
            let pre_and_req_in_flight = |req_msg| lift_state(
                req_msg_is_the_in_flight_pending_req_at_after_create_headless_service_step_with_zk(zk, req_msg)
            );
            let pre_and_exists_resp_in_flight = lift_state(
                at_after_create_headless_service_step_with_zk_and_exists_resp_in_flight(zk)
            );
            let pre_and_resp_in_flight = |resp_msg| lift_state(
                resp_msg_is_the_in_flight_resp_at_after_create_headless_service_step_with_zk(zk, resp_msg)
            );
            assert forall |req_msg|
                spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
            by {
                lemma_receives_some_resp_at_after_create_headless_service_step_with_zk(spec, zk, req_msg);
            }
            leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
            assert_by(
                tla_exists(pre_and_req_in_flight) == lift_state(at_after_create_headless_service_step_with_zk_and_pending_req_in_flight(zk)),
                {
                    assert forall |ex|
                        #[trigger] lift_state(at_after_create_headless_service_step_with_zk_and_pending_req_in_flight(zk)).satisfied_by(ex)
                    implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                        let req_msg = ex.head().pending_req_of(zk.object_ref());
                        assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(
                        tla_exists(pre_and_req_in_flight),
                        lift_state(at_after_create_headless_service_step_with_zk_and_pending_req_in_flight(zk))
                    );
                }
            );

            assert forall |resp_msg|
                spec.entails(
                    #[trigger] pre_and_resp_in_flight(resp_msg)
                        .leads_to(lift_state(at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk)))
                )
            by {
                lemma_from_after_create_headless_service_step_to_after_create_client_service_step(spec, zk, resp_msg);
            }
            leads_to_exists_intro(
                spec,
                pre_and_resp_in_flight,
                lift_state(at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk))
            );
            assert_by(
                tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
                {
                    assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
                    implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                        let resp_msg = choose |resp_msg| {
                            &&& #[trigger] ex.head().message_in_flight(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, ex.head().pending_req_of(zk.object_ref()))
                        };
                        assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
                }
            );

            leads_to_trans_temp(
                spec,
                lift_state(at_after_create_headless_service_step_with_zk_and_pending_req_in_flight(zk)),
                pre_and_exists_resp_in_flight,
                lift_state(at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk))
            );
        }
    );

    assert_by(
        spec.entails(
            lift_state(at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk))
                .leads_to(lift_state(at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk)))
        ),
        {
            let pre_and_req_in_flight = |req_msg| lift_state(
                req_msg_is_the_in_flight_pending_req_at_after_create_client_service_step_with_zk(zk, req_msg)
            );
            let pre_and_exists_resp_in_flight = lift_state(
                at_after_create_client_service_step_with_zk_and_exists_resp_in_flight(zk)
            );
            let pre_and_resp_in_flight = |resp_msg| lift_state(
                resp_msg_is_the_in_flight_resp_at_after_create_client_service_step_with_zk(zk, resp_msg)
            );
            assert forall |req_msg|
                spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
            by {
                lemma_receives_some_resp_at_after_create_client_service_step_with_zk(spec, zk, req_msg);
            }
            leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
            assert_by(
                tla_exists(pre_and_req_in_flight) == lift_state(at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk)),
                {
                    assert forall |ex|
                        #[trigger] lift_state(at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk)).satisfied_by(ex)
                    implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                        let req_msg = ex.head().pending_req_of(zk.object_ref());
                        assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(
                        tla_exists(pre_and_req_in_flight),
                        lift_state(at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk))
                    );
                }
            );

            assert forall |resp_msg|
                spec.entails(
                    #[trigger] pre_and_resp_in_flight(resp_msg)
                        .leads_to(lift_state(at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk)))
                )
            by {
                lemma_from_after_create_client_service_step_to_after_create_admin_server_service_step(spec, zk, resp_msg);
            }
            leads_to_exists_intro(
                spec,
                pre_and_resp_in_flight,
                lift_state(at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk))
            );
            assert_by(
                tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
                {
                    assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
                    implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                        let resp_msg = choose |resp_msg| {
                            &&& #[trigger] ex.head().message_in_flight(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, ex.head().pending_req_of(zk.object_ref()))
                        };
                        assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
                }
            );

            leads_to_trans_temp(
                spec,
                lift_state(at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk)),
                pre_and_exists_resp_in_flight,
                lift_state(at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk))
            );
        }
    );

    assert_by(
        spec.entails(
            lift_state(at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk))
                .leads_to(lift_state(at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk)))
        ),
        {
            let pre_and_req_in_flight = |req_msg| lift_state(
                req_msg_is_the_in_flight_pending_req_at_after_create_admin_server_service_step_with_zk(zk, req_msg)
            );
            let pre_and_exists_resp_in_flight = lift_state(
                at_after_create_admin_server_service_step_with_zk_and_exists_resp_in_flight(zk)
            );
            let pre_and_resp_in_flight = |resp_msg| lift_state(
                resp_msg_is_the_in_flight_resp_at_after_create_admin_server_service_step_with_zk(zk, resp_msg)
            );
            assert forall |req_msg|
                spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
            by {
                lemma_receives_some_resp_at_after_create_admin_server_service_step_with_zk(spec, zk, req_msg);
            }
            leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
            assert_by(
                tla_exists(pre_and_req_in_flight) == lift_state(at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk)),
                {
                    assert forall |ex|
                        #[trigger] lift_state(at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk)).satisfied_by(ex)
                    implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                        let req_msg = ex.head().pending_req_of(zk.object_ref());
                        assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(
                        tla_exists(pre_and_req_in_flight),
                        lift_state(at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk))
                    );
                }
            );

            assert forall |resp_msg|
                spec.entails(
                    #[trigger] pre_and_resp_in_flight(resp_msg)
                        .leads_to(lift_state(at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk)))
                )
            by {
                lemma_from_after_create_admin_server_service_step_to_after_create_config_map_step(spec, zk, resp_msg);
            }
            leads_to_exists_intro(
                spec,
                pre_and_resp_in_flight,
                lift_state(at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk))
            );
            assert_by(
                tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
                {
                    assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
                    implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                        let resp_msg = choose |resp_msg| {
                            &&& #[trigger] ex.head().message_in_flight(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, ex.head().pending_req_of(zk.object_ref()))
                        };
                        assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
                }
            );

            leads_to_trans_temp(
                spec,
                lift_state(at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk)),
                pre_and_exists_resp_in_flight,
                lift_state(at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk))
            );
        }
    );

    assert_by(
        spec.entails(
            lift_state(at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk))
                .leads_to(lift_state(at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)))
        ),
        {
            let pre_and_req_in_flight = |req_msg| lift_state(
                req_msg_is_the_in_flight_pending_req_at_after_create_config_map_step_with_zk(zk, req_msg)
            );
            let pre_and_exists_resp_in_flight = lift_state(
                at_after_create_config_map_step_with_zk_and_exists_resp_in_flight(zk)
            );
            let pre_and_resp_in_flight = |resp_msg| lift_state(
                resp_msg_is_the_in_flight_resp_at_after_create_config_map_step_with_zk(zk, resp_msg)
            );
            assert forall |req_msg|
                spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
            by {
                lemma_receives_some_resp_at_after_create_config_map_step_with_zk(spec, zk, req_msg);
            }
            leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
            assert_by(
                tla_exists(pre_and_req_in_flight) == lift_state(at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk)),
                {
                    assert forall |ex|
                        #[trigger] lift_state(at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk)).satisfied_by(ex)
                    implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                        let req_msg = ex.head().pending_req_of(zk.object_ref());
                        assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(
                        tla_exists(pre_and_req_in_flight),
                        lift_state(at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk))
                    );
                }
            );

            assert forall |resp_msg|
                spec.entails(
                    #[trigger] pre_and_resp_in_flight(resp_msg)
                        .leads_to(lift_state(at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)))
                )
            by {
                lemma_from_after_create_config_map_step_to_after_get_stateful_set_step(spec, zk, resp_msg);
            }
            leads_to_exists_intro(
                spec,
                pre_and_resp_in_flight,
                lift_state(at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk))
            );
            assert_by(
                tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
                {
                    assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
                    implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                        let resp_msg = choose |resp_msg| {
                            &&& #[trigger] ex.head().message_in_flight(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, ex.head().pending_req_of(zk.object_ref()))
                        };
                        assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
                }
            );

            leads_to_trans_temp(
                spec,
                lift_state(at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk)),
                pre_and_exists_resp_in_flight,
                lift_state(at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk))
            );
        }
    );

    assert_by(
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                &&& at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)(s)
            })
                .leads_to(lift_state(current_state_matches(zk)))
        ),
        {
            let pre = lift_state(|s: ClusterState| {
                &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                &&& at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)(s)
            });
            let post = lift_state(|s: ClusterState| {
                &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                &&& at_after_create_stateful_set_step_with_zk_and_pending_req_in_flight(zk)(s)
            });
            let pre_and_req_in_flight = |req_msg| lift_state(
                |s: ClusterState| {
                    &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_after_get_stateful_set_step_with_zk(zk, req_msg)(s)
                }
            );
            let pre_and_exists_resp_in_flight = lift_state(
                |s: ClusterState| {
                    &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& at_after_get_stateful_set_step_with_zk_and_exists_not_found_resp_in_flight(zk)(s)
                }
            );
            let pre_and_resp_in_flight = |resp_msg| lift_state(
                |s: ClusterState| {
                    &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& resp_msg_is_the_in_flight_resp_at_after_get_stateful_set_step_with_zk(zk, resp_msg)(s)
                    &&& resp_msg.content.get_get_response().res.is_Err()
                    &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                }
            );
            let post_and_req_in_flight = |req_msg| lift_state(
                |s: ClusterState| {
                    &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_after_create_stateful_set_step_with_zk(zk, req_msg)(s)
                }
            );
            assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
            by {
                lemma_receives_not_found_resp_at_after_get_stateful_set_step_with_zk(spec, zk, rest_id, req_msg);
            }
            leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
            assert_by(
                tla_exists(pre_and_req_in_flight) == pre,
                {
                    assert forall |ex| #[trigger] pre.satisfied_by(ex)
                    implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                        let req_msg = ex.head().pending_req_of(zk.object_ref());
                        assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
                }
            );

            assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(post))
            by {
                lemma_from_after_get_stateful_set_step_to_after_create_stateful_set_step(spec, zk, rest_id, resp_msg);
            }
            leads_to_exists_intro(spec, pre_and_resp_in_flight, post);
            assert_by(
                tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
                {
                    assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
                    implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                        let resp_msg = choose |resp_msg| {
                            &&& #[trigger] ex.head().message_in_flight(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, ex.head().pending_req_of(zk.object_ref()))
                            &&& resp_msg.content.get_get_response().res.is_Err()
                            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                        };
                        assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
                }
            );

            assert forall |req_msg| spec.entails(#[trigger] post_and_req_in_flight(req_msg).leads_to(lift_state(current_state_matches(zk))))
            by {
                lemma_sts_is_created_at_after_create_stateful_set_step_with_zk(spec, zk, rest_id, req_msg);
            }
            leads_to_exists_intro(spec, post_and_req_in_flight, lift_state(current_state_matches(zk)));
            assert_by(
                tla_exists(post_and_req_in_flight) == post,
                {
                    assert forall |ex| #[trigger] post.satisfied_by(ex)
                    implies tla_exists(post_and_req_in_flight).satisfied_by(ex) by {
                        let req_msg = ex.head().pending_req_of(zk.object_ref());
                        assert(post_and_req_in_flight(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(post_and_req_in_flight), post);
                }
            );

            leads_to_trans_temp(spec, pre, pre_and_exists_resp_in_flight, post);
            leads_to_trans_temp(spec, pre, post, lift_state(current_state_matches(zk)));
        }
    );

    assert_by(
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                &&& at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)(s)
            })
                .leads_to(lift_state(current_state_matches(zk)))
        ),
        {
            let pre = lift_state(|s: ClusterState| {
                &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                &&& at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)(s)
            });
            let pre_with_object = |object| lift_state(
                |s: ClusterState| {
                    &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                    &&& at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)(s)
                }
            );
            assert forall |object: DynamicObjectView| spec.entails(#[trigger] pre_with_object(object).leads_to(lift_state(current_state_matches(zk))))
            by {
                let p1 = lift_state(|s: ClusterState| {
                    &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                    &&& at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)(s)
                });
                let p2 = lift_state(|s: ClusterState| {
                    &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                    &&& at_after_update_stateful_set_step_with_zk_and_pending_req_in_flight(zk, object)(s)
                });

                assert_by(
                    spec.entails(p1.leads_to(p2)),
                    {
                        let pre_and_req_in_flight = |req_msg| lift_state(
                            |s: ClusterState| {
                                &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                                &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                                &&& req_msg_is_the_in_flight_pending_req_at_after_get_stateful_set_step_with_zk(zk, req_msg)(s)
                            }
                        );
                        let pre_and_exists_resp_in_flight = lift_state(
                            |s: ClusterState| {
                                &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                                &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                                &&& at_after_get_stateful_set_step_with_zk_and_exists_ok_resp_in_flight(zk, object)(s)
                            }
                        );
                        let pre_and_resp_in_flight = |resp_msg| lift_state(
                            |s: ClusterState| {
                                &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                                &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                                &&& resp_msg_is_the_in_flight_resp_at_after_get_stateful_set_step_with_zk(zk, resp_msg)(s)
                                &&& resp_msg.content.get_get_response().res.is_Ok()
                                &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
                            }
                        );

                        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
                        by {
                            lemma_receives_ok_resp_at_after_get_stateful_set_step_with_zk(spec, zk, rest_id, req_msg, object);
                        }
                        leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
                        assert_by(
                            tla_exists(pre_and_req_in_flight) == p1,
                            {
                                assert forall |ex| #[trigger] p1.satisfied_by(ex)
                                implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                                    let req_msg = ex.head().pending_req_of(zk.object_ref());
                                    assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                                }
                                temp_pred_equality(tla_exists(pre_and_req_in_flight), p1);
                            }
                        );

                        assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(p2))
                        by {
                            lemma_from_after_get_stateful_set_step_to_after_update_stateful_set_step(spec, zk, rest_id, resp_msg, object);
                        }
                        leads_to_exists_intro(spec, pre_and_resp_in_flight, p2);
                        assert_by(
                            tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
                            {
                                assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
                                implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                                    let resp_msg = choose |resp_msg| {
                                        &&& #[trigger] ex.head().message_in_flight(resp_msg)
                                        &&& resp_msg_matches_req_msg(resp_msg, ex.head().pending_req_of(zk.object_ref()))
                                        &&& resp_msg.content.get_get_response().res.is_Ok()
                                        &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
                                    };
                                    assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
                                }
                                temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
                            }
                        );

                        leads_to_trans_temp(spec, p1, pre_and_exists_resp_in_flight, p2);
                    }
                );

                assert_by(
                    spec.entails(p2.leads_to(lift_state(current_state_matches(zk)))),
                    {
                        let pre_and_req_in_flight = |req_msg| lift_state(
                            |s: ClusterState| {
                                &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                                &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                                &&& req_msg_is_the_in_flight_pending_req_at_after_update_stateful_set_step_with_zk(zk, req_msg, object)(s)
                            }
                        );
                        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(lift_state(current_state_matches(zk))))
                        by {
                            lemma_sts_is_updated_at_after_update_stateful_set_step_with_zk(spec, zk, rest_id, req_msg, object);
                        }
                        leads_to_exists_intro(spec, pre_and_req_in_flight, lift_state(current_state_matches(zk)));
                        assert_by(
                            tla_exists(pre_and_req_in_flight) == p2,
                            {
                                assert forall |ex| #[trigger] p2.satisfied_by(ex)
                                implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                                    let req_msg = ex.head().pending_req_of(zk.object_ref());
                                    assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                                }
                                temp_pred_equality(tla_exists(pre_and_req_in_flight), p2);
                            }
                        );
                    }
                );

                leads_to_trans_temp(spec, p1, p2, lift_state(current_state_matches(zk)));
            }
            leads_to_exists_intro(spec, pre_with_object, lift_state(current_state_matches(zk)));
            assert_by(
                tla_exists(pre_with_object) == pre,
                {
                    assert forall |ex| #[trigger] pre.satisfied_by(ex)
                    implies tla_exists(pre_with_object).satisfied_by(ex) by {
                        let object = ex.head().resource_obj_of(make_stateful_set_key(zk.object_ref()));
                        assert(pre_with_object(object).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_with_object), pre);
                }
            );
        }
    );

    assert_by(
        spec.entails(
            lift_state(at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk))
                .leads_to(lift_state(current_state_matches(zk)))
        ),
        {
            let p1 = lift_state(|s: ClusterState| {
                &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                &&& at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)(s)
            });
            let p2 = lift_state(|s: ClusterState| {
                &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                &&& at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)(s)
            });
            or_leads_to_combine_temp(spec, p1, p2, lift_state(current_state_matches(zk)));
            temp_pred_equality(p1.or(p2), lift_state(at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)));
        }
    );

    assert_by(
        spec.entails(
            lift_state(current_state_matches(zk))
                .leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            leads_to_self_temp(lift_state(current_state_matches(zk)));
            lemma_stateful_set_is_stable(spec, zk, rest_id, lift_state(current_state_matches(zk)));
        }
    );

    leads_to_trans_n!(
        spec,
        true_pred(),
        lift_state(|s: ClusterState| !s.reconcile_state_contains(zk.object_ref())),
        lift_state(at_init_step_with_no_pending_req(zk)),
        lift_state(at_after_create_headless_service_step_with_zk_and_pending_req_in_flight(zk)),
        lift_state(at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk)),
        lift_state(at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk)),
        lift_state(at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk)),
        lift_state(at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)),
        lift_state(current_state_matches(zk)),
        always(lift_state(current_state_matches(zk)))
    );
}

proof fn lemma_from_unscheduled_to_scheduled(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_exists(zk)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& !s.reconcile_state_contains(zk.object_ref())
                &&& !s.reconcile_scheduled_for(zk.object_ref())
            })
                .leads_to(lift_state(|s: ClusterState| {
                    &&& !s.reconcile_state_contains(zk.object_ref())
                    &&& s.reconcile_scheduled_for(zk.object_ref())
                }))
        ),
{
    let pre = |s: ClusterState| {
        &&& !s.reconcile_state_contains(zk.object_ref())
        &&& !s.reconcile_scheduled_for(zk.object_ref())
    };
    let post = |s: ClusterState| {
        &&& !s.reconcile_state_contains(zk.object_ref())
        &&& s.reconcile_scheduled_for(zk.object_ref())
    };
    let input = zk.object_ref();
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& desired_state_exists(zk)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(desired_state_exists(zk))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(desired_state_exists(zk)))
    );

    temp_pred_equality::<ClusterState>(
        lift_state(desired_state_exists(zk)), lift_state(schedule_controller_reconcile().pre(input))
    );
    spec_implies_pre(spec, lift_state(pre), lift_state(schedule_controller_reconcile().pre(input)));
    use_tla_forall::<ClusterState, ObjectRef>(spec, |key| schedule_controller_reconcile().weak_fairness(key), input);
    schedule_controller_reconcile().wf1(input, spec, stronger_next, pre, post);
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<ClusterState>, zk: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(cluster_safety::each_scheduled_key_is_consistent_with_its_object()))),
        spec.entails(always(lift_state(safety::the_object_in_schedule_has_spec_as(zk)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& !s.reconcile_state_contains(zk.object_ref())
                &&& s.reconcile_scheduled_for(zk.object_ref())
            })
                .leads_to(lift_state(at_init_step_with_no_pending_req(zk)))
        ),
{
    let pre = |s: ClusterState| {
        &&& !s.reconcile_state_contains(zk.object_ref())
        &&& s.reconcile_scheduled_for(zk.object_ref())
    };
    let post = at_init_step_with_no_pending_req(zk);
    let input = (Option::None, Option::Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& cluster_safety::each_scheduled_key_is_consistent_with_its_object()(s)
        &&& safety::the_object_in_schedule_has_spec_as(zk)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(cluster_safety::each_scheduled_key_is_consistent_with_its_object()),
        lift_state(safety::the_object_in_schedule_has_spec_as(zk))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(cluster_safety::each_scheduled_key_is_consistent_with_its_object()))
        .and(lift_state(safety::the_object_in_schedule_has_spec_as(zk)))
    );

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next,
        run_scheduled_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(), pre, post
    );
}

proof fn lemma_from_init_step_to_after_create_headless_service_step(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(at_init_step_with_no_pending_req(zk))
                .leads_to(lift_state(at_after_create_headless_service_step_with_zk_and_pending_req_in_flight(zk)))
        ),
{
    let pre = at_init_step_with_no_pending_req(zk);
    let post = at_after_create_headless_service_step_with_zk_and_pending_req_in_flight(zk);
    let input = (Option::None, Option::Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
    );

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next,
        continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(), pre, post
    );
}

proof fn lemma_receives_some_resp_at_after_create_headless_service_step_with_zk(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_headless_service_step_with_zk(zk, req_msg))
                .leads_to(lift_state(at_after_create_headless_service_step_with_zk_and_exists_resp_in_flight(zk)))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_create_headless_service_step_with_zk(zk, req_msg);
    let post = at_after_create_headless_service_step_with_zk_and_exists_resp_in_flight(zk);
    let input = Option::Some(req_msg);
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

    assert forall |s, s_prime|
        pre(s) && #[trigger] stronger_next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = handle_create_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        });
    }

    kubernetes_api_liveness::lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_from_after_create_headless_service_step_to_after_create_client_service_step(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_resp_at_after_create_headless_service_step_with_zk(zk, resp_msg))
                .leads_to(lift_state(at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk)))
        ),
{
    let pre = resp_msg_is_the_in_flight_resp_at_after_create_headless_service_step_with_zk(zk, resp_msg);
    let post = at_after_create_client_service_step_with_zk_and_pending_req_in_flight(zk);
    let input = (Option::Some(resp_msg), Option::Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
    );

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next,
        continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(), pre, post
    );
}

proof fn lemma_receives_some_resp_at_after_create_client_service_step_with_zk(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_client_service_step_with_zk(zk, req_msg))
                .leads_to(lift_state(at_after_create_client_service_step_with_zk_and_exists_resp_in_flight(zk)))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_create_client_service_step_with_zk(zk, req_msg);
    let post = at_after_create_client_service_step_with_zk_and_exists_resp_in_flight(zk);
    let input = Option::Some(req_msg);
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

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = handle_create_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        });
    }

    kubernetes_api_liveness::lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_from_after_create_client_service_step_to_after_create_admin_server_service_step(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_resp_at_after_create_client_service_step_with_zk(zk, resp_msg))
                .leads_to(lift_state(at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk)))
        ),
{
    let pre = resp_msg_is_the_in_flight_resp_at_after_create_client_service_step_with_zk(zk, resp_msg);
    let post = at_after_create_admin_server_service_step_with_zk_and_pending_req_in_flight(zk);
    let input = (Option::Some(resp_msg), Option::Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
    );

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next,
        continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(), pre, post
    );
}

proof fn lemma_receives_some_resp_at_after_create_admin_server_service_step_with_zk(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_admin_server_service_step_with_zk(zk, req_msg))
                .leads_to(lift_state(at_after_create_admin_server_service_step_with_zk_and_exists_resp_in_flight(zk)))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_create_admin_server_service_step_with_zk(zk, req_msg);
    let post = at_after_create_admin_server_service_step_with_zk_and_exists_resp_in_flight(zk);
    let input = Option::Some(req_msg);
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

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = handle_create_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        });
    }

    kubernetes_api_liveness::lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_from_after_create_admin_server_service_step_to_after_create_config_map_step(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_resp_at_after_create_admin_server_service_step_with_zk(zk, resp_msg))
                .leads_to(lift_state(at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk)))
        ),
{
    let pre = resp_msg_is_the_in_flight_resp_at_after_create_admin_server_service_step_with_zk(zk, resp_msg);
    let post = at_after_create_config_map_step_with_zk_and_pending_req_in_flight(zk);
    let input = (Option::Some(resp_msg), Option::Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
    );

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next,
        continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(), pre, post
    );
}

proof fn lemma_receives_some_resp_at_after_create_config_map_step_with_zk(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_create_config_map_step_with_zk(zk, req_msg))
                .leads_to(lift_state(at_after_create_config_map_step_with_zk_and_exists_resp_in_flight(zk)))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_create_config_map_step_with_zk(zk, req_msg);
    let post = at_after_create_config_map_step_with_zk_and_exists_resp_in_flight(zk);
    let input = Option::Some(req_msg);
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

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = handle_create_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        });
    }

    kubernetes_api_liveness::lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_from_after_create_config_map_step_to_after_get_stateful_set_step(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_resp_at_after_create_config_map_step_with_zk(zk, resp_msg))
                .leads_to(lift_state(at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk)))
        ),
{
    let pre = resp_msg_is_the_in_flight_resp_at_after_create_config_map_step_with_zk(zk, resp_msg);
    let post = at_after_get_stateful_set_step_with_zk_and_pending_req_in_flight(zk);
    let input = (Option::Some(resp_msg), Option::Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
    );

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next,
        continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(), pre, post
    );
}

proof fn lemma_receives_ok_resp_at_after_get_stateful_set_step_with_zk(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, rest_id: nat, req_msg: Message, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        spec.entails(always(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                    &&& req_msg_is_the_in_flight_pending_req_at_after_get_stateful_set_step_with_zk(zk, req_msg)(s)
                }
            )
                .leads_to(lift_state(
                    |s: ClusterState| {
                        &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                        &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                        &&& at_after_get_stateful_set_step_with_zk_and_exists_ok_resp_in_flight(zk, object)(s)
                    }
                ))
        ),
{
    let pre = |s: ClusterState| {
        &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_stateful_set_step_with_zk(zk, req_msg)(s)
    };
    let post = |s: ClusterState| {
        &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
        &&& at_after_get_stateful_set_step_with_zk_and_exists_ok_resp_in_flight(zk, object)(s)
    };
    let input = Option::Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        &&& kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
        &&& safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()),
        lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)),
        lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        .and(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
        .and(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| next_step::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = handle_get_request(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.message_in_flight(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Ok()
                        &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
                    });
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
        });
    }

    kubernetes_api_liveness::lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_stateful_set_step_to_after_update_stateful_set_step(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, rest_id: nat, resp_msg: Message, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(cluster_safety::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        spec.entails(always(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                &&& resp_msg_is_the_in_flight_resp_at_after_get_stateful_set_step_with_zk(zk, resp_msg)(s)
                &&& resp_msg.content.get_get_response().res.is_Ok()
                &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
            })
                .leads_to(lift_state(|s: ClusterState| {
                    &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                    &&& at_after_update_stateful_set_step_with_zk_and_pending_req_in_flight(zk, object)(s)
                }))
        ),
{
    let pre = |s: ClusterState| {
        &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
        &&& resp_msg_is_the_in_flight_resp_at_after_get_stateful_set_step_with_zk(zk, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res.is_Ok()
        &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
    };
    let post = |s: ClusterState| {
        &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
        &&& at_after_update_stateful_set_step_with_zk_and_pending_req_in_flight(zk, object)(s)
    };
    let input = (Option::Some(resp_msg), Option::Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
        &&& controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
        &&& kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& cluster_safety::each_object_in_etcd_is_well_formed()(s)
        &&& safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
        &&& safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())),
        lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(cluster_safety::each_object_in_etcd_is_well_formed()),
        lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)),
        lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
        .and(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
        .and(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(cluster_safety::each_object_in_etcd_is_well_formed()))
        .and(lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
        .and(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next,
        continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(), pre, post
    );
}

proof fn lemma_sts_is_updated_at_after_update_stateful_set_step_with_zk(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, rest_id: nat, req_msg: Message, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(cluster_safety::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        spec.entails(always(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
                    &&& req_msg_is_the_in_flight_pending_req_at_after_update_stateful_set_step_with_zk(zk, req_msg, object)(s)
                }
            )
                .leads_to(lift_state(
                    |s: ClusterState| {
                        &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(zk.object_ref()))).is_Ok()
                        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(zk.object_ref()))).get_Ok_0().spec == make_stateful_set(zk).spec
                    }
                ))
        ),
{
    let pre = |s: ClusterState| {
        &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& s.resource_obj_of(make_stateful_set_key(zk.object_ref())) == object
        &&& req_msg_is_the_in_flight_pending_req_at_after_update_stateful_set_step_with_zk(zk, req_msg, object)(s)
    };
    let post = |s: ClusterState| {
        &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(zk.object_ref()))).is_Ok()
        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(zk.object_ref()))).get_Ok_0().spec == make_stateful_set(zk).spec
    };
    let input = Option::Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        &&& kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& cluster_safety::each_object_in_etcd_is_well_formed()(s)
        &&& safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
        &&& safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()),
        lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(cluster_safety::each_object_in_etcd_is_well_formed()),
        lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)),
        lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        .and(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(cluster_safety::each_object_in_etcd_is_well_formed()))
        .and(lift_state(safety::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
        .and(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| next_step::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                StatefulSetView::spec_integrity_is_preserved_by_marshal();
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        StatefulSetView::spec_integrity_is_preserved_by_marshal();
    }

    kubernetes_api_liveness::lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_receives_not_found_resp_at_after_get_stateful_set_step_with_zk(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, rest_id: nat, req_msg: Message
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_after_get_stateful_set_step_with_zk(zk, req_msg)(s)
                }
            )
                .leads_to(lift_state(
                    |s: ClusterState| {
                        &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                        &&& at_after_get_stateful_set_step_with_zk_and_exists_not_found_resp_in_flight(zk)(s)
                    }
                ))
        ),
{
    let pre = |s: ClusterState| {
        &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_stateful_set_step_with_zk(zk, req_msg)(s)
    };
    let post = |s: ClusterState| {
        &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& at_after_get_stateful_set_step_with_zk_and_exists_not_found_resp_in_flight(zk)(s)
    };
    let input = Option::Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        &&& kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()),
        lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        .and(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| next_step::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = handle_get_request(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.message_in_flight(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Err()
                        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                    });
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        });
    }

    kubernetes_api_liveness::lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_stateful_set_step_to_after_create_stateful_set_step(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, rest_id: nat, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| controller_next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                &&& resp_msg_is_the_in_flight_resp_at_after_get_stateful_set_step_with_zk(zk, resp_msg)(s)
                &&& resp_msg.content.get_get_response().res.is_Err()
                &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
            })
                .leads_to(lift_state(|s: ClusterState| {
                    &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& at_after_create_stateful_set_step_with_zk_and_pending_req_in_flight(zk)(s)
                }))
        ),
{
    let pre = |s: ClusterState| {
        &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& resp_msg_is_the_in_flight_resp_at_after_get_stateful_set_step_with_zk(zk, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res.is_Err()
        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
    };
    let post = |s: ClusterState| {
        &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& at_after_create_stateful_set_step_with_zk_and_pending_req_in_flight(zk)(s)
    };
    let input = (Option::Some(resp_msg), Option::Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
        &&& controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
        &&& kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())),
        lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
        .and(lift_state(controller_runtime_safety::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
        .and(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next,
        continue_reconcile::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(), pre, post
    );
}

proof fn lemma_sts_is_created_at_after_create_stateful_set_step_with_zk(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, rest_id: nat, req_msg: Message
)
    requires
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(crash_disabled()))),
        spec.entails(always(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_after_create_stateful_set_step_with_zk(zk, req_msg)(s)
                }
            )
                .leads_to(lift_state(
                    |s: ClusterState| {
                        &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
                        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(zk.object_ref()))).is_Ok()
                        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(zk.object_ref()))).get_Ok_0().spec == make_stateful_set(zk).spec
                    }
                ))
        ),
{
    let pre = |s: ClusterState| {
        &&& !s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& req_msg_is_the_in_flight_pending_req_at_after_create_stateful_set_step_with_zk(zk, req_msg)(s)
    };
    let post = |s: ClusterState| {
        &&& s.resource_key_exists(make_stateful_set_key(zk.object_ref()))
        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(zk.object_ref()))).is_Ok()
        &&& StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(zk.object_ref()))).get_Ok_0().spec == make_stateful_set(zk).spec
    };
    let input = Option::Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& crash_disabled()(s)
        &&& controller_runtime_safety::every_in_flight_msg_has_unique_id()(s)
        &&& kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(crash_disabled()),
        lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()),
        lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(crash_disabled()))
        .and(lift_state(controller_runtime_safety::every_in_flight_msg_has_unique_id()))
        .and(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(safety::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| next_step::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                StatefulSetView::spec_integrity_is_preserved_by_marshal();
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        StatefulSetView::spec_integrity_is_preserved_by_marshal();
    }

    kubernetes_api_liveness::lemma_pre_leads_to_post_by_kubernetes_api::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>(
        spec, input, stronger_next, handle_request(), pre, post
    );
}

proof fn lemma_stateful_set_is_stable(
    spec: TempPred<ClusterState>, zk: ZookeeperClusterView, rest_id: nat, p: TempPred<ClusterState>
)
    requires
        spec.entails(p.leads_to(lift_state(current_state_matches(zk)))),
        spec.entails(always(lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()))),
        spec.entails(always(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        spec.entails(always(lift_state(safety::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id)))),
    ensures
        spec.entails(p.leads_to(always(lift_state(current_state_matches(zk))))),
{
    let post = current_state_matches(zk);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()(s, s_prime)
        &&& kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
        &&& safety::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()),
        lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)),
        lift_state(safety::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(next::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>())
        .and(lift_state(kubernetes_api_liveness::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(safety::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
        .and(lift_state(safety::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id)))
    );

    assert forall |s, s_prime| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        StatefulSetView::spec_integrity_is_preserved_by_marshal();
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), p, lift_state(post));
}

}
