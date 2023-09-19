// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    controller::state_machine::*,
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::zookeeper_controller::{
    common::*,
    proof::{common::*, liveness::helper_invariants, liveness::terminate},
    spec::{reconciler::*, zookeepercluster::*},
};
use vstd::prelude::*;

verus! {

// The current state matches the desired state described in the cr.
// I.e., the corresponding stateful set exists and its spec is the same as desired.
spec fn current_state_matches(zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& StatefulSetView::unmarshal(s.resources()[make_stateful_set_key(zk.object_ref())]).is_Ok()
        &&& StatefulSetView::unmarshal(s.resources()[make_stateful_set_key(zk.object_ref())]).get_Ok_0().spec == make_stateful_set(zk).spec
    }
}

// The liveness property says []cluster::desired_state_is(zk) ~> []current_state_matches(zk).
spec fn liveness(zk: ZookeeperClusterView) -> TempPred<ZKCluster>
    recommends
        zk.well_formed(),
{
    always(lift_state(ZKCluster::desired_state_is(zk))).leads_to(always(lift_state(current_state_matches(zk))))
}

// We prove init /\ []next /\ []wf |= []cluster::desired_state_is(zk) ~> []current_state_matches(zk) holds for each zk.
proof fn liveness_proof_forall_zk()
    ensures
        forall |zk: ZookeeperClusterView| zk.well_formed() ==> #[trigger] cluster_spec().entails(liveness(zk)),
{
    assert forall |zk: ZookeeperClusterView| zk.well_formed()
    implies #[trigger] cluster_spec().entails(liveness(zk)) by {
        liveness_proof(zk);
    };
}

// Next and all the wf conditions.
spec fn next_with_wf() -> TempPred<ZKCluster> {
    always(lift_action(ZKCluster::next()))
    .and(tla_forall(|input| ZKCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| ZKCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| ZKCluster::schedule_controller_reconcile().weak_fairness(input)))
    .and(ZKCluster::disable_crash().weak_fairness(()))
    .and(ZKCluster::disable_busy().weak_fairness(()))
}

proof fn next_with_wf_is_stable()
    ensures
        valid(stable(next_with_wf())),
{
    always_p_is_stable(lift_action(ZKCluster::next()));
    ZKCluster::tla_forall_action_weak_fairness_is_stable(ZKCluster::kubernetes_api_next());
    ZKCluster::tla_forall_action_weak_fairness_is_stable(ZKCluster::controller_next());
    ZKCluster::tla_forall_action_weak_fairness_is_stable(ZKCluster::schedule_controller_reconcile());
    ZKCluster::action_weak_fairness_is_stable(ZKCluster::disable_crash());
    ZKCluster::action_weak_fairness_is_stable(ZKCluster::disable_busy());
    stable_and_n!(
        always(lift_action(ZKCluster::next())),
        tla_forall(|input| ZKCluster::kubernetes_api_next().weak_fairness(input)),
        tla_forall(|input| ZKCluster::controller_next().weak_fairness(input)),
        tla_forall(|input| ZKCluster::schedule_controller_reconcile().weak_fairness(input)),
        ZKCluster::disable_crash().weak_fairness(()),
        ZKCluster::disable_busy().weak_fairness(())
    );
}

// All assumptions that makes liveness possible, such as controller crash no longer happens,
// the cr's spec always remains unchanged, and so on.
spec fn assumptions(zk: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(lift_state(ZKCluster::crash_disabled()))
    .and(always(lift_state(ZKCluster::busy_disabled())))
    .and(always(lift_state(ZKCluster::desired_state_is(zk))))
    .and(always(lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zk))))
    .and(always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zk))))
}

proof fn assumptions_is_stable(zk: ZookeeperClusterView)
    ensures
        valid(stable(assumptions(zk))),
{
    stable_and_always_n!(
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::desired_state_is(zk)),
        lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zk)),
        lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zk))
    );
}

// The safety invariants that are required to prove liveness.
spec fn invariants(zk: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref()))))
    .and(always(lift_state(ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))))
    .and(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata())))
    .and(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())))
    .and(always(lift_state(helper_invariants::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(zk.object_ref()))))
    .and(always(lift_state(helper_invariants::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(zk.object_ref()))))
    .and(always(lift_state(ZKCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::Init)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterUpdateStatefulSet)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateStatefulSet)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateHeadlessService)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateClientService)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateAdminServerService)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateConfigMap)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterGetStatefulSet)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterGetStatefulSet)))))
    .and(always(lift_state(ZKCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateZKNode)))))
}

proof fn invariants_is_stable(zk: ZookeeperClusterView)
    ensures
        valid(stable(invariants(zk))),
{
    stable_and_always_n!(
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())),
        lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(helper_invariants::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(zk.object_ref())),
        lift_state(helper_invariants::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(zk.object_ref())),
        lift_state(ZKCluster::no_pending_req_msg_or_external_api_input_at_reconcile_init_state(zk.object_ref())),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterUpdateStatefulSet))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateStatefulSet))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateHeadlessService))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateClientService))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateAdminServerService))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateConfigMap))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterGetStatefulSet))),
        lift_state(ZKCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateZKNode)))
    );
}

// Some other invariants requires to prove liveness.
// Note that different from the above invariants, these do not hold for the entire execution from init.
// They only hold since some point (e.g., when the rest id counter is the same as rest_id).
// Some of these invariants are also based on the assumptions.
spec fn invariants_since_rest_id(zk: ZookeeperClusterView, rest_id: RestId) -> TempPred<ZKCluster> {
    always(lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)))
    .and(always(lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))))
    .and(always(lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))))
    .and(always(lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))))
    .and(always(lift_state(helper_invariants::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id))))
}

proof fn invariants_since_rest_id_is_stable(zk: ZookeeperClusterView, rest_id: RestId)
    ensures
        valid(stable(invariants_since_rest_id(zk, rest_id))),
{
    stable_and_always_n!(
        lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)),
        lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)),
        lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)),
        lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)),
        lift_state(helper_invariants::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id))
    );
}

// This invariant is also used to prove liveness.
// Different from above, it only holds after some time since the rest id counter is the same as rest_id.
spec fn invariants_led_to_by_rest_id(zk: ZookeeperClusterView, rest_id: RestId) -> TempPred<ZKCluster> {
    always(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))
}

proof fn invariants_led_to_by_rest_id_is_stable(zk: ZookeeperClusterView, rest_id: RestId)
    ensures
        valid(stable(invariants_led_to_by_rest_id(zk, rest_id))),
{
    always_p_is_stable(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)));
}

proof fn liveness_proof(zk: ZookeeperClusterView)
    requires
        zk.well_formed(),
    ensures
        cluster_spec().entails(liveness(zk)),
{
    // First prove that with all the invariants and assumptions, true leads to []current_state_matches(zk)
    assert_by(
        next_with_wf().and(invariants(zk)).and(assumptions(zk))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            let spec = next_with_wf().and(invariants(zk)).and(assumptions(zk));

            let idle = lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zk.object_ref()));
            let idle_and_rest_id_is = |rest_id| lift_state(ZKCluster::rest_id_counter_is(rest_id)).and(idle);
            assert forall |rest_id|
            spec.entails(#[trigger] idle_and_rest_id_is(rest_id).leads_to(always(lift_state(current_state_matches(zk))))) by {
                lemma_true_leads_to_always_current_state_matches_zk_from_idle_with_rest_id(zk, rest_id);
                assert_by(
                    valid(stable(spec)),
                    {
                        next_with_wf_is_stable();
                        invariants_is_stable(zk);
                        assumptions_is_stable(zk);

                        stable_and_n!(
                            next_with_wf(),
                            invariants(zk),
                            assumptions(zk)
                        );
                    }
                );
                temp_pred_equality(
                    lift_state(ZKCluster::rest_id_counter_is(rest_id))
                    .and(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zk.object_ref())))
                    .and(next_with_wf()).and(invariants(zk)).and(assumptions(zk)),
                    spec.and(idle_and_rest_id_is(rest_id))
                );
                unpack_conditions_from_spec(spec, idle_and_rest_id_is(rest_id), true_pred(), always(lift_state(current_state_matches(zk))));
                temp_pred_equality(true_pred().and(idle_and_rest_id_is(rest_id)), idle_and_rest_id_is(rest_id));
            }

            // Here we eliminate the rest_id using leads_to_exists_intro.
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

    // Then prove that with all the invariants and the base assumptions (i.e., controller does not crash and cr.spec remains unchanged)
    // true leads to []current_state_matches(zk).
    // This is done by eliminating the other assumptions derived from the base assumptions using the unpack rule.
    assert_by(
        next_with_wf().and(invariants(zk)).and(always(lift_state(ZKCluster::desired_state_is(zk))))
        .and(always(lift_state(ZKCluster::crash_disabled()))).and(always(lift_state(ZKCluster::busy_disabled())))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            let spec = next_with_wf().and(invariants(zk)).and(always(lift_state(ZKCluster::desired_state_is(zk)))).and(always(lift_state(ZKCluster::crash_disabled()))).and(always(lift_state(ZKCluster::busy_disabled())));
            let other_assumptions = always(lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zk)))
                .and(always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zk))));
            temp_pred_equality(
                next_with_wf().and(invariants(zk)).and(assumptions(zk)),
                next_with_wf().and(invariants(zk)).and(always(lift_state(ZKCluster::desired_state_is(zk))))
                .and(always(lift_state(ZKCluster::crash_disabled()))).and(always(lift_state(ZKCluster::busy_disabled()))).and(other_assumptions)
            );
            assert_by(
                valid(stable(spec)),
                {
                    next_with_wf_is_stable();
                    invariants_is_stable(zk);
                    always_p_is_stable(lift_state(ZKCluster::desired_state_is(zk)));
                    always_p_is_stable(lift_state(ZKCluster::crash_disabled()));
                    always_p_is_stable(lift_state(ZKCluster::busy_disabled()));

                    stable_and_n!(
                        next_with_wf(),
                        invariants(zk),
                        always(lift_state(ZKCluster::desired_state_is(zk))),
                        always(lift_state(ZKCluster::crash_disabled())),
                        always(lift_state(ZKCluster::busy_disabled()))
                    );
                }
            );
            unpack_conditions_from_spec(spec, other_assumptions, true_pred(), always(lift_state(current_state_matches(zk))));
            temp_pred_equality(true_pred().and(other_assumptions), other_assumptions);

            terminate::reconcile_eventually_terminates(spec, zk);
            ZKCluster::lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, zk);
            ZKCluster::lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, zk);

            leads_to_always_combine_n!(
                spec, true_pred(),
                lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zk)),
                lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zk))
            );

            always_and_equality_n!(
                lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zk)),
                lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zk))
            );

            leads_to_trans_temp(spec, true_pred(), other_assumptions, always(lift_state(current_state_matches(zk))));
        }
    );

    // Now we eliminate the assumption []ZKCluster::crash_disabled() /\ []busy_disabled.
    assert_by(
        next_with_wf().and(invariants(zk)).and(always(lift_state(ZKCluster::desired_state_is(zk))))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            let spec = next_with_wf().and(invariants(zk)).and(always(lift_state(ZKCluster::desired_state_is(zk))));
            assert_by(
                valid(stable(spec)),
                {
                    next_with_wf_is_stable();
                    invariants_is_stable(zk);
                    always_p_is_stable(lift_state(ZKCluster::desired_state_is(zk)));

                    stable_and_n!(
                        next_with_wf(),
                        invariants(zk),
                        always(lift_state(ZKCluster::desired_state_is(zk)))
                    );
                }
            );
            temp_pred_equality(
                spec.and(always(lift_state(ZKCluster::crash_disabled())).and(always(lift_state(ZKCluster::busy_disabled())))),
                spec.and(always(lift_state(ZKCluster::crash_disabled()))).and(always(lift_state(ZKCluster::busy_disabled())))
            );
            unpack_conditions_from_spec(spec, always(lift_state(ZKCluster::crash_disabled())).and(always(lift_state(ZKCluster::busy_disabled()))), true_pred(), always(lift_state(current_state_matches(zk))));
            temp_pred_equality(
                true_pred().and(always(lift_state(ZKCluster::crash_disabled())).and(always(lift_state(ZKCluster::busy_disabled())))),
                always(lift_state(ZKCluster::crash_disabled())).and(always(lift_state(ZKCluster::busy_disabled())))
            );

            ZKCluster::lemma_true_leads_to_crash_always_disabled(spec);
            ZKCluster::lemma_true_leads_to_busy_always_disabled(spec);
            _temp(
                spec,
                true_pred(),
                lift_state(ZKCluster::crash_disabled()),
                lift_state(ZKCluster::busy_disabled())
            );
            always_and_equality(
                lift_state(ZKCluster::crash_disabled()),
                lift_state(ZKCluster::busy_disabled())
            );
            leads_to_trans_temp(spec, true_pred(), always(lift_state(ZKCluster::crash_disabled())).and(always(lift_state(ZKCluster::busy_disabled()))), always(lift_state(current_state_matches(zk))));
        }
    );

    // Then we unpack the assumption of []cluster::desired_state_is(zk) from spec.
    assert_by(
        next_with_wf().and(invariants(zk))
        .entails(
            always(lift_state(ZKCluster::desired_state_is(zk))).leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            let spec = next_with_wf().and(invariants(zk));
            let assumption = always(lift_state(ZKCluster::desired_state_is(zk)));
            assert_by(
                valid(stable(spec)),
                {
                    next_with_wf_is_stable();
                    invariants_is_stable(zk);

                    stable_and_n!(next_with_wf(), invariants(zk));
                }
            );
            unpack_conditions_from_spec(spec, assumption, true_pred(), always(lift_state(current_state_matches(zk))));
            temp_pred_equality(true_pred().and(assumption), assumption);
        }
    );

    // Finally we eliminate all the invariants using simplify_predicate and also add init to the spec.
    assert_by(
        cluster_spec()
        .entails(
            always(lift_state(ZKCluster::desired_state_is(zk))).leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            let spec = cluster_spec();

            entails_trans(
                spec.and(invariants(zk)), next_with_wf().and(invariants(zk)),
                always(lift_state(ZKCluster::desired_state_is(zk))).leads_to(always(lift_state(current_state_matches(zk))))
            );

            ZKCluster::lemma_always_every_in_flight_msg_has_unique_id(spec);
            ZKCluster::lemma_always_each_resp_matches_at_most_one_pending_req(spec, zk.object_ref());
            ZKCluster::lemma_always_each_resp_if_matches_pending_req_then_no_other_resp_matches(spec, zk.object_ref());
            ZKCluster::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
            ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
            ZKCluster::lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec);
            ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
            helper_invariants::lemma_always_pending_msg_at_after_create_stateful_set_step_is_create_sts_req(spec, zk.object_ref());
            helper_invariants::lemma_always_pending_msg_at_after_update_stateful_set_step_is_update_sts_req(spec, zk.object_ref());
            ZKCluster::lemma_always_no_pending_req_msg_or_external_api_input_at_reconcile_state(spec, zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::Init));
            ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state_1(spec, zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterUpdateStatefulSet));
            ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state_1(spec, zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateStatefulSet));
            ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state_1(spec, zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateHeadlessService));
            ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state_1(spec, zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateClientService));
            ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state_1(spec, zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateAdminServerService));
            ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state_1(spec, zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateConfigMap));
            ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state_1(spec, zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterGetStatefulSet));
            ZKCluster::lemma_always_pending_req_msg_is_none_at_reconcile_state(spec, zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateZKNode));

            entails_and_n!(
                spec,
                always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id())),
                always(lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref()))),
                always(lift_state(ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref()))),
                always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator())),
                always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())),
                always(lift_state(ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata())),
                always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())),
                always(lift_state(helper_invariants::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(zk.object_ref()))),
                always(lift_state(helper_invariants::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(zk.object_ref()))),
                always(lift_state(ZKCluster::no_pending_req_msg_or_external_api_input_at_reconcile_init_state(zk.object_ref()))),
                always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterUpdateStatefulSet)))),
                always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateStatefulSet)))),
                always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateHeadlessService)))),
                always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateClientService)))),
                always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateAdminServerService)))),
                always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateConfigMap)))),
                always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterGetStatefulSet)))),
                always(lift_state(ZKCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(zk.object_ref(), zookeeper_reconcile_state(ZookeeperReconcileStep::AfterCreateZKNode))))
            );

            simplify_predicate(spec, invariants(zk));
        }
    );

}

// This lemma proves that starting from the point where rest id counter is rest_id, with all the invariants and assumptions,
// true leads to []current_state_matches(zk).
proof fn lemma_true_leads_to_always_current_state_matches_zk_from_idle_with_rest_id(zk: ZookeeperClusterView, rest_id: RestId)
    requires
        zk.well_formed(),
    ensures
        lift_state(ZKCluster::rest_id_counter_is(rest_id))
        .and(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zk.object_ref())))
        .and(next_with_wf()).and(invariants(zk)).and(assumptions(zk))
        .entails(
            true_pred().leads_to(always(lift_state(current_state_matches(zk))))
        ),
{
    let stable_spec = next_with_wf().and(invariants(zk)).and(assumptions(zk));
    let spec = lift_state(ZKCluster::rest_id_counter_is(rest_id))
        .and(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zk.object_ref())))
        .and(next_with_wf())
        .and(invariants(zk))
        .and(assumptions(zk));

    // To prove the liveness, we need some extra invariants (invariants_since_rest_id and invariants_led_to_by_rest_id)
    // that only holds since the rest id counter is rest_id.
    assert_by(
        spec.and(invariants_since_rest_id(zk, rest_id)).entails(
            invariants_led_to_by_rest_id(zk, rest_id).leads_to(always(lift_state(current_state_matches(zk))))
        ),
        {
            lemma_true_leads_to_always_current_state_matches_zk_under_eventual_invariants(zk, rest_id);
            assert_by(
                valid(stable(stable_spec.and(invariants_since_rest_id(zk, rest_id)))),
                {
                    next_with_wf_is_stable();
                    invariants_is_stable(zk);
                    assumptions_is_stable(zk);
                    invariants_since_rest_id_is_stable(zk, rest_id);

                    stable_and_n!(next_with_wf(), invariants(zk), assumptions(zk), invariants_since_rest_id(zk, rest_id));
                }
            );
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

    ZKCluster::lemma_true_leads_to_always_no_req_before_rest_id_is_in_flight(
        spec.and(invariants_since_rest_id(zk, rest_id)), rest_id
    );

    // Here we eliminate invariants_led_to_by_rest_id using leads_to_trans_temp
    leads_to_trans_temp(spec.and(invariants_since_rest_id(zk, rest_id)), true_pred(), invariants_led_to_by_rest_id(zk, rest_id), always(lift_state(current_state_matches(zk))));

    assert_by(
        spec.entails(invariants_since_rest_id(zk, rest_id)),
        {
            eliminate_always(spec, lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()));
            eliminate_always(spec, lift_state(helper_invariants::pending_msg_at_after_create_stateful_set_step_is_create_sts_req(zk.object_ref())));
            eliminate_always(spec, lift_state(helper_invariants::pending_msg_at_after_update_stateful_set_step_is_update_sts_req(zk.object_ref())));

            ZKCluster::lemma_always_has_rest_id_counter_no_smaller_than(spec, rest_id);
            helper_invariants::lemma_always_at_most_one_create_sts_req_since_rest_id_is_in_flight(spec, zk.object_ref(), rest_id);
            helper_invariants::lemma_always_at_most_one_update_sts_req_since_rest_id_is_in_flight(spec, zk.object_ref(), rest_id);
            helper_invariants::lemma_always_no_delete_sts_req_since_rest_id_is_in_flight(spec, zk.object_ref(), rest_id);
            helper_invariants::lemma_always_every_update_sts_req_since_rest_id_does_the_same(spec, zk, rest_id);

            entails_and_n!(
                spec,
                always(lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id))),
                always(lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))),
                always(lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))),
                always(lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))),
                always(lift_state(helper_invariants::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id)))
            );
        }
    );

    // And we eliminate invariants_since_rest_id using simplify_predicate.
    simplify_predicate(spec, invariants_since_rest_id(zk, rest_id));
}

// This lemma proves that with all the invariants, assumptions, and even invariants that only hold since rest id counter is rest_id,
// true ~> []current_state_matches(zk).
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

    // First we prove true ~> not_in_reconcile, because reconcile always terminates.
    assert_by(
        spec.entails(
            true_pred().leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zk.object_ref())))
        ),
        {
            terminate::reconcile_eventually_terminates(spec, zk);
        }
    );

    // Then we prove not_in_reconcile ~> init_step by applying wf1.
    assert_by(
        spec.entails(
            lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zk.object_ref()))
                .leads_to(lift_state(no_pending_req_at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::Init)))
        ),
        {
            let unscheduled_and_not_in_reconcile = lift_state(|s: ZKCluster| {
                &&& !s.ongoing_reconciles().contains_key(zk.object_ref())
                &&& !s.scheduled_reconciles().contains_key(zk.object_ref())
            });
            let scheduled_and_not_in_reconcile = lift_state(|s: ZKCluster| {
                &&& !s.ongoing_reconciles().contains_key(zk.object_ref())
                &&& s.scheduled_reconciles().contains_key(zk.object_ref())
            });
            lemma_from_unscheduled_to_scheduled(spec, zk);
            lemma_from_scheduled_to_init_step(spec, zk);
            leads_to_trans_temp(
                spec,
                unscheduled_and_not_in_reconcile,
                scheduled_and_not_in_reconcile,
                lift_state(no_pending_req_at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::Init))
            );
            or_leads_to_combine_and_equality!(
                spec, lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zk.object_ref())),
                unscheduled_and_not_in_reconcile,
                scheduled_and_not_in_reconcile;
                lift_state(no_pending_req_at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::Init))
            );
        }
    );

    // Then we prove init_step ~> after_create_headless_service by applying wf1.
    assert_by(
        spec.entails(
            lift_state(no_pending_req_at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::Init))
                .leads_to(lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateHeadlessService, zk, arbitrary())))
        ),
        {
            lemma_from_init_step_to_after_create_headless_service_step(spec, zk);
        }
    );

    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, zk, ZookeeperReconcileStep::AfterCreateHeadlessService, ZookeeperReconcileStep::AfterCreateClientService);
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, zk, ZookeeperReconcileStep::AfterCreateClientService, ZookeeperReconcileStep::AfterCreateAdminServerService);
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, zk, ZookeeperReconcileStep::AfterCreateAdminServerService, ZookeeperReconcileStep::AfterCreateConfigMap);
    lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, zk, ZookeeperReconcileStep::AfterCreateConfigMap, ZookeeperReconcileStep::AfterGetStatefulSet);

    // after_get_stateful_set will lead to two different states depending on whether the stateful_set exists,
    // here we prove the first case: after_get_stateful_set /\ !exists ~> current_state_matches(zk) by creating operations.
    assert_by(
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, arbitrary())(s)
            })
                .leads_to(lift_state(current_state_matches(zk)))
        ),
        {
            let pre = lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, arbitrary())(s)
            });
            let post = lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateStatefulSet, zk, arbitrary())(s)
            });
            let pre_and_req_in_flight = |req_msg| lift_state(
                |s: ZKCluster| {
                    &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, req_msg, arbitrary())(s)
                }
            );
            let pre_and_exists_resp_in_flight = lift_state(
                |s: ZKCluster| {
                    &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& at_after_get_stateful_set_step_with_zk_and_exists_not_found_resp_in_flight(zk)(s)
                }
            );
            let pre_and_resp_in_flight = |resp_msg| lift_state(
                |s: ZKCluster| {
                    &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& resp_msg_is_the_in_flight_resp_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, resp_msg, arbitrary())(s)
                    &&& resp_msg.content.get_get_response().res.is_Err()
                    &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                }
            );
            let post_and_req_in_flight = |req_msg| lift_state(
                |s: ZKCluster| {
                    &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateStatefulSet, zk, req_msg, arbitrary())(s)
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
                        let req_msg = ex.head().ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
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
                            &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                            &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0())
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
                        let req_msg = ex.head().ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
                        assert(post_and_req_in_flight(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(post_and_req_in_flight), post);
                }
            );

            leads_to_trans_temp(spec, pre, pre_and_exists_resp_in_flight, post);
            leads_to_trans_temp(spec, pre, post, lift_state(current_state_matches(zk)));
        }
    );

    // after_get_stateful_set will lead to two different states depending on whether the stateful_set exists,
    // here we prove the second case: after_get_stateful_set /\ exists ~> current_state_matches(zk) by updating operations.
    assert_by(
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, arbitrary())(s)
            })
                .leads_to(lift_state(current_state_matches(zk)))
        ),
        {
            let pre = lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, arbitrary())(s)
            });
            let pre_with_object = |object| lift_state(
                |s: ZKCluster| {
                    &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                    &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, arbitrary())(s)
                }
            );
            assert forall |object: DynamicObjectView| spec.entails(#[trigger] pre_with_object(object).leads_to(lift_state(current_state_matches(zk))))
            by {
                let p1 = lift_state(|s: ZKCluster| {
                    &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                    &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, arbitrary())(s)
                });
                let p2 = lift_state(|s: ZKCluster| {
                    &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                    &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterUpdateStatefulSet, zk, object)(s)
                });

                assert_by(
                    spec.entails(p1.leads_to(p2)),
                    {
                        let pre_and_req_in_flight = |req_msg| lift_state(
                            |s: ZKCluster| {
                                &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                                &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                                &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, req_msg, arbitrary())(s)
                            }
                        );
                        let pre_and_exists_resp_in_flight = lift_state(
                            |s: ZKCluster| {
                                &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                                &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                                &&& at_after_get_stateful_set_step_with_zk_and_exists_ok_resp_in_flight(zk, object)(s)
                            }
                        );
                        let pre_and_resp_in_flight = |resp_msg| lift_state(
                            |s: ZKCluster| {
                                &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                                &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                                &&& resp_msg_is_the_in_flight_resp_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, resp_msg, arbitrary())(s)
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
                                    let req_msg = ex.head().ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
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
                                        &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                                        &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0())
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
                            |s: ZKCluster| {
                                &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                                &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                                &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterUpdateStatefulSet, zk, req_msg, object)(s)
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
                                    let req_msg = ex.head().ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
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
                        let object = ex.head().resources()[make_stateful_set_key(zk.object_ref())];
                        assert(pre_with_object(object).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_with_object), pre);
                }
            );
        }
    );

    // Now we prove after_get_stateful_set ~> current_state_matches(zk) by merging the above two cases.
    assert_by(
        spec.entails(
            lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, arbitrary()))
                .leads_to(lift_state(current_state_matches(zk)))
        ),
        {
            let p1 = lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, arbitrary())(s)
            });
            let p2 = lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, arbitrary())(s)
            });
            or_leads_to_combine_and_equality!(
                spec, lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, arbitrary())),
                p1, p2; lift_state(current_state_matches(zk))
            );
        }
    );

    // Now we prove that once current_state_matches(zk), it is always the case (stability).
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

    // Finally, chain everything together using leads_to_trans_n!.
    leads_to_trans_n!(
        spec,
        true_pred(),
        lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zk.object_ref())),
        lift_state(no_pending_req_at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::Init)),
        lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateHeadlessService, zk, arbitrary())),
        lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateClientService, zk, arbitrary())),
        lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateAdminServerService, zk, arbitrary())),
        lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateConfigMap, zk, arbitrary())),
        lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, arbitrary())),
        lift_state(current_state_matches(zk)),
        always(lift_state(current_state_matches(zk)))
    );
}

// This lemma ensures that zookeeper controller at some step with pending request in flight will finally enter its next step.
// For step and next_step, they both require the reconcile_state to have a pending request which is the correct request for that step.
// Note that in this lemma we add some constraints to step:
//    1. There is only one possible next_step for it.
//    2. When the controller enters this step, it must create a request (which is piggybacked by the pending request message)
// We don't care about update step here, so arbitraray() is used to show that the object parameter in
// pending_req_in_flight_at_zookeeper_step_with_zk is unrelated.
proof fn lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView, step: ZookeeperReconcileStep, next_step: ZookeeperReconcileStep
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        step != ZookeeperReconcileStep::Error, step != ZookeeperReconcileStep::Done,
        // next_step != ZookeeperReconcileStep::Init,
        forall |zk_1, resp_o| #[trigger] reconcile_core(zk_1, resp_o, ZookeeperReconcileState{ reconcile_step: step }).0.reconcile_step == next_step
            && reconcile_core(zk, resp_o, ZookeeperReconcileState{ reconcile_step: step }).1.is_Some()
            && reconcile_core(zk, resp_o, ZookeeperReconcileState{ reconcile_step: step }).1.get_Some_0().is_KRequest()
            && (zk_1.object_ref() == zk.object_ref() && zk_1.spec == zk.spec ==>
            forall |object: DynamicObjectView| #[trigger] is_correct_pending_request_at_zookeeper_step(
                next_step, reconcile_core(zk, resp_o, ZookeeperReconcileState{ reconcile_step: step }).1.get_Some_0().get_KRequest_0(), zk, object
            )
        ),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(step, zk, arbitrary()))
            .leads_to(lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(next_step, zk, arbitrary())))
        ),
{
    // The proof of this lemma contains of two parts (two leads_to's) and then a leads_to_trans:
    //     1. at_step(step) /\ pending_request in flight /\ correct_request ~>
    //                         at_step(step) /\ response in flight /\ match(response, pending_request)
    //     2. at_step(step) /\ response in flight /\ match(response, pending_request) ~>
    //                         at_step(next_step) /\ pending_request in flight /\ correct_request
    // This predicate is used to give a specific request for the pre state for using wf1 which requires an input.
    let pre_and_req_in_flight = |req_msg| lift_state(
        req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(step, zk, req_msg, arbitrary())
    );
    // This predicate is the intermediate state of the two leads_to
    let pre_and_exists_resp_in_flight = lift_state(
        exists_resp_in_flight_at_zookeeper_step_with_zk(step, zk, arbitrary())
    );
    // This predicate is used to give a specific request for the intermediate state for using wf1 which requires an input.
    let pre_and_resp_in_flight = |resp_msg| lift_state(
        resp_msg_is_the_in_flight_resp_at_zookeeper_step_with_zk(step, zk, resp_msg, arbitrary())
    );
    // We use the lemma lemma_receives_some_resp_at_zookeeper_step_with_zk that takes a req_msg,
    // so we need to eliminate the req_msg using leads_to_exists_intro.
    assert forall |req_msg|
        spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
    by {
        lemma_receives_some_resp_at_zookeeper_step_with_zk(spec, zk, req_msg, step);
    }
    leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
    assert_by(
        tla_exists(pre_and_req_in_flight) == lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(step, zk, arbitrary())),
        {
            assert forall |ex|
                #[trigger] lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(step, zk, arbitrary())).satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(
                tla_exists(pre_and_req_in_flight),
                lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(step, zk, arbitrary()))
            );
        }
    );
    // Similarly we eliminate resp_msg using leads_to_exists_intro.
    assert forall |resp_msg|
        spec.entails(
            #[trigger] pre_and_resp_in_flight(resp_msg)
                .leads_to(lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(next_step, zk, arbitrary())))
        )
    by {
        lemma_from_resp_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, zk, resp_msg, step, next_step);
    }
    leads_to_exists_intro(
        spec,
        pre_and_resp_in_flight,
        lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(next_step, zk, arbitrary()))
    );
    assert_by(
        tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
        {
            assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
            implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0())
                };
                assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
        }
    );

    leads_to_trans_temp(
        spec,
        lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(step, zk, arbitrary())),
        pre_and_exists_resp_in_flight,
        lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(next_step, zk, arbitrary()))
    );
}

proof fn lemma_from_unscheduled_to_scheduled(spec: TempPred<ZKCluster>, zk: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zk)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& !s.ongoing_reconciles().contains_key(zk.object_ref())
                &&& !s.scheduled_reconciles().contains_key(zk.object_ref())
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& !s.ongoing_reconciles().contains_key(zk.object_ref())
                    &&& s.scheduled_reconciles().contains_key(zk.object_ref())
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& !s.ongoing_reconciles().contains_key(zk.object_ref())
        &&& !s.scheduled_reconciles().contains_key(zk.object_ref())
    };
    let post = |s: ZKCluster| {
        &&& !s.ongoing_reconciles().contains_key(zk.object_ref())
        &&& s.scheduled_reconciles().contains_key(zk.object_ref())
    };
    let input = zk.object_ref();

    ZKCluster::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(
        spec, input, ZKCluster::next(), ZKCluster::desired_state_is(zk), pre, post
    );
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<ZKCluster>, zk: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zk)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& !s.ongoing_reconciles().contains_key(zk.object_ref())
                &&& s.scheduled_reconciles().contains_key(zk.object_ref())
            })
                .leads_to(lift_state(no_pending_req_at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::Init)))
        ),
{
    let pre = |s: ZKCluster| {
        &&& !s.ongoing_reconciles().contains_key(zk.object_ref())
        &&& s.scheduled_reconciles().contains_key(zk.object_ref())
    };
    let post = no_pending_req_at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::Init);
    let input = (None, Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zk)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zk))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
        .and(lift_state(ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()))
        .and(lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zk)))
    );

    ZKCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        ZKCluster::run_scheduled_reconcile(), pre, post
    );
}

proof fn lemma_from_init_step_to_after_create_headless_service_step(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(no_pending_req_at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::Init))
                .leads_to(lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateHeadlessService, zk, arbitrary())))
        ),
{
    let pre = no_pending_req_at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::Init);
    let post = pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateHeadlessService, zk, arbitrary());
    let input = (None, Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
    );

    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}

// This lemma ensures that zookeeper controller at some step with a response in flight that matches its pending request will finally enter its next step.
// For step and next_step, they both require the reconcile_state to have a pending request which is the correct request
// for that step. For step alone, there is a known response (the parameter resp_msg) in flight that matches the pending request.
// Note that in this lemma we add some constraints to step:
//    1. There is only one possible next_step for it.
//    2. When the controller enters this step, it must creates a request (which will be used to create the pending request message)
// We don't care about update step here, so arbitraray() is used to show that the object parameter in
// pending_req_in_flight_at_zookeeper_step_with_zk is unrelated.
proof fn lemma_from_resp_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView, resp_msg: ZKMessage, step: ZookeeperReconcileStep, result_step: ZookeeperReconcileStep
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        step != ZookeeperReconcileStep::Done, step != ZookeeperReconcileStep::Error,
        // result_step != ZookeeperReconcileStep::Init,
        // This forall zk_1 constraint is used because the cr passed to reconcile_core is not necessarily zk here.
        // We only know that zk_1.object_ref() == zk.object_ref() && zk_1.spec == zk.spec.
        forall |zk_1, resp_o| #[trigger] reconcile_core(zk_1, resp_o, ZookeeperReconcileState{ reconcile_step: step }).0.reconcile_step == result_step
            && reconcile_core(zk, resp_o, ZookeeperReconcileState{ reconcile_step: step }).1.is_Some()
            && reconcile_core(zk, resp_o, ZookeeperReconcileState{ reconcile_step: step }).1.get_Some_0().is_KRequest()
            && (zk_1.object_ref() == zk.object_ref() && zk_1.spec == zk.spec ==>
            forall |object: DynamicObjectView| #[trigger] is_correct_pending_request_at_zookeeper_step(
                result_step, reconcile_core(zk, resp_o, ZookeeperReconcileState{ reconcile_step: step }).1.get_Some_0().get_KRequest_0(), zk, object
            )),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_resp_at_zookeeper_step_with_zk(step, zk, resp_msg, arbitrary()))
                .leads_to(lift_state(pending_req_in_flight_at_zookeeper_step_with_zk(result_step, zk, arbitrary())))
        ),
{
    let pre = resp_msg_is_the_in_flight_resp_at_zookeeper_step_with_zk(step, zk, resp_msg, arbitrary());
    let post = pending_req_in_flight_at_zookeeper_step_with_zk(result_step, zk, arbitrary());
    let input = (Some(resp_msg), Some(zk.object_ref()));

    // For every part of stronger_next:
    //   - next(): the next predicate of the state machine
    //   - ZKCluster::crash_disabled(): to ensure that the reconcile process can continue
    //   - ZKCluster::busy_disabled(): to ensure that the request will get its expected response
    //    (Note that this is not required for termination)
    //   - each_resp_matches_at_most_one_pending_req: to make sure that the resp_msg will not be used by other cr
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref()))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
        .and(lift_state(ZKCluster::busy_disabled()))
        .and(lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.1.is_Some() && input.1.get_Some_0() == zk.object_ref() {
                    assert(s_prime.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some());
                    assert(post(s_prime));
                } else {
                    assert(pre(s_prime));
                }
            }
            _ => {
                assert(pre(s_prime));
            }
        }
    }

    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}

proof fn lemma_receives_some_resp_at_zookeeper_step_with_zk(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView, req_msg: ZKMessage, step: ZookeeperReconcileStep
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        step != ZookeeperReconcileStep::Error, step != ZookeeperReconcileStep::Done,
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(step, zk, req_msg, arbitrary()))
                .leads_to(lift_state(exists_resp_in_flight_at_zookeeper_step_with_zk(step, zk, arbitrary())))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(step, zk, req_msg, arbitrary());
    let post = exists_resp_in_flight_at_zookeeper_step_with_zk(step, zk, arbitrary());
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
        .and(lift_state(ZKCluster::busy_disabled()))
        .and(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::transition_by_etcd(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
        });
    }

    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, ZKCluster::handle_request(), pre, post
    );
}

proof fn lemma_receives_ok_resp_at_after_get_stateful_set_step_with_zk(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView, rest_id: nat, req_msg: ZKMessage, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ZKCluster| {
                    &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                    &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, req_msg, arbitrary())(s)
                }
            )
                .leads_to(lift_state(
                    |s: ZKCluster| {
                        &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                        &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                        &&& at_after_get_stateful_set_step_with_zk_and_exists_ok_resp_in_flight(zk, object)(s)
                    }
                ))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
        &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, req_msg, arbitrary())(s)
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
        &&& at_after_get_stateful_set_step_with_zk_and_exists_ok_resp_in_flight(zk, object)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
        &&& helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)),
        lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
        .and(lift_state(ZKCluster::busy_disabled()))
        .and(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
        .and(lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = ZKCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Ok()
                        &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
                    });
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
        });
    }

    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, ZKCluster::handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_stateful_set_step_to_after_update_stateful_set_step(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView, rest_id: nat, resp_msg: ZKMessage, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                &&& resp_msg_is_the_in_flight_resp_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, resp_msg, arbitrary())(s)
                &&& resp_msg.content.get_get_response().res.is_Ok()
                &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                    &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterUpdateStatefulSet, zk, object)(s)
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
        &&& resp_msg_is_the_in_flight_resp_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, resp_msg, arbitrary())(s)
        &&& resp_msg.content.get_get_response().res.is_Ok()
        &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
        &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterUpdateStatefulSet, zk, object)(s)
    };
    let input = (Some(resp_msg), Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
        &&& ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
        &&& ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
        &&& helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())),
        lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)),
        lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
        .and(lift_state(ZKCluster::busy_disabled()))
        .and(lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
        .and(lift_state(ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
        .and(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))
        .and(lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
        .and(lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}

proof fn lemma_sts_is_updated_at_after_update_stateful_set_step_with_zk(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView, rest_id: nat, req_msg: ZKMessage, object: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ZKCluster| {
                    &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
                    &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterUpdateStatefulSet, zk, req_msg, object)(s)
                }
            )
                .leads_to(lift_state(
                    |s: ZKCluster| {
                        &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                        &&& StatefulSetView::unmarshal(s.resources()[make_stateful_set_key(zk.object_ref())]).is_Ok()
                        &&& StatefulSetView::unmarshal(s.resources()[make_stateful_set_key(zk.object_ref())]).get_Ok_0().spec == make_stateful_set(zk).spec
                    }
                ))
        ),
{
    let pre = |s: ZKCluster| {
        &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& s.resources()[make_stateful_set_key(zk.object_ref())] == object
        &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterUpdateStatefulSet, zk, req_msg, object)(s)
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& StatefulSetView::unmarshal(s.resources()[make_stateful_set_key(zk.object_ref())]).is_Ok()
        &&& StatefulSetView::unmarshal(s.resources()[make_stateful_set_key(zk.object_ref())]).get_Ok_0().spec == make_stateful_set(zk).spec
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
        &&& helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)),
        lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
        .and(lift_state(ZKCluster::busy_disabled()))
        .and(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))
        .and(lift_state(helper_invariants::at_most_one_update_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
        .and(lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                StatefulSetView::marshal_spec_preserves_integrity();
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        StatefulSetView::marshal_spec_preserves_integrity();
    }

    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, ZKCluster::handle_request(), pre, post
    );
}

proof fn lemma_receives_not_found_resp_at_after_get_stateful_set_step_with_zk(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView, rest_id: nat, req_msg: Message
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ZKCluster| {
                    &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, req_msg, arbitrary())(s)
                }
            )
                .leads_to(lift_state(
                    |s: ZKCluster| {
                        &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                        &&& at_after_get_stateful_set_step_with_zk_and_exists_not_found_resp_in_flight(zk)(s)
                    }
                ))
        ),
{
    let pre = |s: ZKCluster| {
        &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, req_msg, arbitrary())(s)
    };
    let post = |s: ZKCluster| {
        &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& at_after_get_stateful_set_step_with_zk_and_exists_not_found_resp_in_flight(zk)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
        .and(lift_state(ZKCluster::busy_disabled()))
        .and(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = ZKCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Err()
                        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                    });
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        });
    }

    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, ZKCluster::handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_stateful_set_step_to_after_create_stateful_set_step(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView, rest_id: nat, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                &&& resp_msg_is_the_in_flight_resp_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, resp_msg, arbitrary())(s)
                &&& resp_msg.content.get_get_response().res.is_Err()
                &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
            })
                .leads_to(lift_state(|s: ZKCluster| {
                    &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateStatefulSet, zk, arbitrary())(s)
                }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& resp_msg_is_the_in_flight_resp_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterGetStatefulSet, zk, resp_msg, arbitrary())(s)
        &&& resp_msg.content.get_get_response().res.is_Err()
        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
    };
    let post = |s: ZKCluster| {
        &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& pending_req_in_flight_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateStatefulSet, zk, arbitrary())(s)
    };
    let input = (Some(resp_msg), Some(zk.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())(s)
        &&& ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())(s)
        &&& ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };

    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())),
        lift_state(ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())),
        lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
        .and(lift_state(ZKCluster::each_resp_matches_at_most_one_pending_req(zk.object_ref())))
        .and(lift_state(ZKCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(zk.object_ref())))
        .and(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}

proof fn lemma_sts_is_created_at_after_create_stateful_set_step_with_zk(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView, rest_id: nat, req_msg: Message
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        zk.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: ZKCluster| {
                    &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                    &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateStatefulSet, zk, req_msg, arbitrary())(s)
                }
            )
                .leads_to(lift_state(
                    |s: ZKCluster| {
                        &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
                        &&& StatefulSetView::unmarshal(s.resources()[make_stateful_set_key(zk.object_ref())]).is_Ok()
                        &&& StatefulSetView::unmarshal(s.resources()[make_stateful_set_key(zk.object_ref())]).get_Ok_0().spec == make_stateful_set(zk).spec
                    }
                ))
        ),
{
    let pre = |s: ZKCluster| {
        &&& !s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(ZookeeperReconcileStep::AfterCreateStatefulSet, zk, req_msg, arbitrary())(s)
    };
    let post = |s: ZKCluster| {
        &&& s.resources().contains_key(make_stateful_set_key(zk.object_ref()))
        &&& StatefulSetView::unmarshal(s.resources()[make_stateful_set_key(zk.object_ref())]).is_Ok()
        &&& StatefulSetView::unmarshal(s.resources()[make_stateful_set_key(zk.object_ref())]).get_Ok_0().spec == make_stateful_set(zk).spec
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
        .and(lift_state(ZKCluster::busy_disabled()))
        .and(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))
        .and(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(helper_invariants::at_most_one_create_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                StatefulSetView::marshal_spec_preserves_integrity();
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        StatefulSetView::marshal_spec_preserves_integrity();
    }

    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, ZKCluster::handle_request(), pre, post
    );
}

proof fn lemma_stateful_set_is_stable(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView, rest_id: nat, p: TempPred<ZKCluster>
)
    requires
        spec.entails(p.leads_to(lift_state(current_state_matches(zk)))),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))),
        spec.entails(always(lift_state(helper_invariants::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id)))),
    ensures
        spec.entails(p.leads_to(always(lift_state(current_state_matches(zk))))),
{
    let post = current_state_matches(zk);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)(s)
        &&& helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)(s)
        &&& helper_invariants::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id)(s)
    };
    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)),
        lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)),
        lift_state(helper_invariants::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::no_req_before_rest_id_is_in_flight(rest_id)))
        .and(lift_state(helper_invariants::no_delete_sts_req_since_rest_id_is_in_flight(zk.object_ref(), rest_id)))
        .and(lift_state(helper_invariants::every_update_sts_req_since_rest_id_does_the_same(zk, rest_id)))
    );

    assert forall |s, s_prime| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        StatefulSetView::marshal_spec_preserves_integrity();
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), p, lift_state(post));
}

}
