// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use crate::zookeeper_controller::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants,
        liveness::{
            resource_match::*,
            spec::*,
            stateful_set_match::{
                lemma_from_after_get_stateful_set_step_to_stateful_set_matches,
                lemma_stateful_set_is_stable,
            },
            terminate,
            zookeeper_api::lemma_from_after_exists_stateful_set_step_to_after_get_stateful_set_step,
        },
        predicate::*,
        resource::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use vstd::{prelude::*, string::*};

verus! {

// We prove init /\ []next /\ []wf |= []ZKCluster::desired_state_is(zookeeper) ~> []current_state_matches(zookeeper) holds for each zookeeper.
proof fn liveness_proof_forall_zookeeper()
    ensures liveness_theorem::<ZookeeperMaker>(),
{
    assert forall |zookeeper: ZookeeperClusterView| #[trigger] cluster_spec().entails(liveness::<ZookeeperMaker>(zookeeper)) by {
        liveness_proof(zookeeper);
    };
    spec_entails_tla_forall(cluster_spec(), |zookeeper: ZookeeperClusterView| liveness::<ZookeeperMaker>(zookeeper));
}

proof fn liveness_proof(zookeeper: ZookeeperClusterView)
    ensures cluster_spec().entails(liveness::<ZookeeperMaker>(zookeeper)),
{
    assumption_and_invariants_of_all_phases_is_stable(zookeeper);
    lemma_true_leads_to_always_current_state_matches(zookeeper);
    reveal_with_fuel(spec_before_phase_n, 8);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(7, zookeeper);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(6, zookeeper);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(5, zookeeper);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(4, zookeeper);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(3, zookeeper);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(2, zookeeper);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(1, zookeeper);

    let assumption = always(lift_state(ZKCluster::desired_state_is(zookeeper)));
    unpack_conditions_from_spec(invariants(zookeeper), assumption, true_pred(), always(lift_state(current_state_matches::<ZookeeperMaker>(zookeeper))));
    temp_pred_equality(true_pred().and(assumption), assumption);

    valid_implies_trans(
        cluster_spec().and(derived_invariants_since_beginning(zookeeper)), invariants(zookeeper),
        always(lift_state(ZKCluster::desired_state_is(zookeeper))).leads_to(always(lift_state(current_state_matches::<ZookeeperMaker>(zookeeper))))
    );
    sm_spec_entails_all_invariants(zookeeper);
    simplify_predicate(cluster_spec(), derived_invariants_since_beginning(zookeeper));
}

proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(i: nat, zookeeper: ZookeeperClusterView)
    requires
        1 <= i <= 7,
        valid(stable(spec_before_phase_n(i, zookeeper))),
        spec_before_phase_n(i + 1, zookeeper).entails(true_pred().leads_to(always(lift_state(current_state_matches::<ZookeeperMaker>(zookeeper)))))
    ensures spec_before_phase_n(i, zookeeper).entails(true_pred().leads_to(always(lift_state(current_state_matches::<ZookeeperMaker>(zookeeper))))),
{
    reveal_with_fuel(spec_before_phase_n, 8);
    temp_pred_equality(spec_before_phase_n(i + 1, zookeeper), spec_before_phase_n(i, zookeeper).and(invariants_since_phase_n(i, zookeeper)));
    spec_of_previous_phases_entails_eventually_new_invariants(i, zookeeper);
    unpack_conditions_from_spec(spec_before_phase_n(i, zookeeper), invariants_since_phase_n(i, zookeeper), true_pred(), always(lift_state(current_state_matches::<ZookeeperMaker>(zookeeper))));
    temp_pred_equality(true_pred().and(invariants_since_phase_n(i, zookeeper)), invariants_since_phase_n(i, zookeeper));
    leads_to_trans_temp(spec_before_phase_n(i, zookeeper), true_pred(), invariants_since_phase_n(i, zookeeper), always(lift_state(current_state_matches::<ZookeeperMaker>(zookeeper))));
}

proof fn lemma_true_leads_to_always_current_state_matches(zookeeper: ZookeeperClusterView)
    ensures assumption_and_invariants_of_all_phases(zookeeper).entails(true_pred().leads_to(always(lift_state(current_state_matches::<ZookeeperMaker>(zookeeper))))),
{
    let spec = assumption_and_invariants_of_all_phases(zookeeper);
    lemma_true_leads_to_always_state_matches_for_all_resources(zookeeper);
    let a_to_p = |res: SubResource| lift_state(sub_resource_state_matches(res, zookeeper));
    helper_invariants::leads_to_always_tla_forall_subresource(spec, true_pred(), a_to_p);
    assert forall |ex| #[trigger] tla_forall(a_to_p).satisfied_by(ex) implies lift_state(current_state_matches::<ZookeeperMaker>(zookeeper)).satisfied_by(ex) by {
        let s = ex.head();
        assert forall |res: SubResource| #[trigger] resource_state_matches::<ZookeeperMaker>(res, zookeeper, s.resources()) by {
            tla_forall_apply(a_to_p, res);
            assert(a_to_p(res).satisfied_by(ex));
            assert(sub_resource_state_matches(res, zookeeper)(s));
        }
    }
    temp_pred_equality(tla_forall(|res: SubResource| lift_state(sub_resource_state_matches(res, zookeeper))), lift_state(current_state_matches::<ZookeeperMaker>(zookeeper)));
}

proof fn lemma_true_leads_to_always_state_matches_for_all_resources(zookeeper: ZookeeperClusterView)
    ensures
        forall |sub_resource: SubResource|
            assumption_and_invariants_of_all_phases(zookeeper)
            .entails(true_pred().leads_to(always(lift_state(#[trigger] sub_resource_state_matches(sub_resource, zookeeper))))),
{
    lemma_true_leads_to_always_state_matches_for_all_but_stateful_set(zookeeper);
    lemma_true_leads_to_always_state_matches_for_stateful_set(zookeeper);
}

proof fn lemma_true_leads_to_always_state_matches_for_all_but_stateful_set(zookeeper: ZookeeperClusterView)
    ensures
        forall |sub_resource: SubResource| sub_resource != SubResource::StatefulSet
        ==> assumption_and_invariants_of_all_phases(zookeeper)
            .entails(true_pred().leads_to(always(lift_state(#[trigger] sub_resource_state_matches(sub_resource, zookeeper))))),
{
    let spec = assumption_and_invariants_of_all_phases(zookeeper);

    assert forall |action: ActionKind, sub_resource: SubResource| #![auto] spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(action, sub_resource)))))) by {
        always_tla_forall_apply(spec, |step: (ActionKind, SubResource)| lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(step.0, step.1)))), (action, sub_resource));
    }

    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(spec, zookeeper);
    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(zookeeper).

    // The following two lemmas show that spec |= reconcile_idle ~> init /\ no_pending_req.
    lemma_from_reconcile_idle_to_scheduled(spec, zookeeper);
    lemma_from_scheduled_to_init_step(spec, zookeeper);

    // After applying this lemma, we get spec |= init /\ no_pending_req ~> create_headless_service /\ pending_req.
    lemma_from_init_step_to_after_create_headless_service_step(spec, zookeeper);

    // always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, zookeeper)), SubResource::ConfigMap);

    // We first show that the reconciler can go to at_after_get_resource_step(next_resource) from at_after_get_resource_step(sub_resource)
    // where sub_resource cannot be StatefulSet because it's the last resource to be processed and doesn't have its next_resource.
    // Through this, we can string all the resources together in sequence. This also means that the system can go to any
    // at_after_get_resource_step(sub_resource) from an arbitrary state.
    assert forall |sub_resource: SubResource| sub_resource != SubResource::StatefulSet && sub_resource != SubResource::ConfigMap implies
    spec.entails(
        lift_state(#[trigger] pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper))
            .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource).get_AfterKRequestStep_1(), zookeeper)))
    ) by {
        always_tla_forall_apply_for_sub_resource(spec, sub_resource, zookeeper);
        lemma_from_after_get_resource_step_to_resource_matches(spec, zookeeper, sub_resource);
    }
    // Thanks to the recursive construction of macro.
    leads_to_trans_n!(
        spec, true_pred(), lift_state(|s: ZKCluster| { !s.ongoing_reconciles().contains_key(zookeeper.object_ref()) }),
        lift_state(|s: ZKCluster| { !s.ongoing_reconciles().contains_key(zookeeper.object_ref()) && s.scheduled_reconciles().contains_key(zookeeper.object_ref())}),
        lift_state(no_pending_req_at_zookeeper_step_with_zookeeper(zookeeper, ZookeeperReconcileStep::Init)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, zookeeper)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ClientService, zookeeper)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::AdminServerService, zookeeper)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ConfigMap, zookeeper))
    );

    // Since we already have true ~> at_after_get_resource_step(sub_resource), and we can get at_after_get_resource_step(sub_resource)
    // ~> sub_resource_state_matches(sub_resource, zookeeper) by applying lemma lemma_from_after_get_resource_step_to_resource_matches,
    // we now have true ~> sub_resource_state_matches(sub_resource, zookeeper).
    assert forall |sub_resource: SubResource| sub_resource != SubResource::StatefulSet implies
    spec.entails(
        true_pred().leads_to(lift_state(#[trigger] sub_resource_state_matches(sub_resource, zookeeper)))
    ) by {
        always_tla_forall_apply_for_sub_resource(spec, sub_resource, zookeeper);
        lemma_from_after_get_resource_step_to_resource_matches(spec, zookeeper, sub_resource);
        leads_to_trans_temp(
            spec, true_pred(), lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper)),
            lift_state(sub_resource_state_matches(sub_resource, zookeeper))
        );
    }

    // Now we further prove stability: given true ~> sub_resource_state_matches(sub_resource, zookeeper)
    // we prove true ~> []sub_resource_state_matches(sub_resource, zookeeper)
    assert forall |sub_resource: SubResource| sub_resource != SubResource::StatefulSet implies
    spec.entails(
        true_pred().leads_to(always(lift_state(#[trigger] sub_resource_state_matches(sub_resource, zookeeper))))
    ) by {
        always_tla_forall_apply_for_sub_resource(spec, sub_resource, zookeeper);
        lemma_resource_object_is_stable(spec, sub_resource, zookeeper, true_pred());
    }
}

proof fn lemma_true_leads_to_always_state_matches_for_stateful_set(zookeeper: ZookeeperClusterView)
    requires assumption_and_invariants_of_all_phases(zookeeper).entails(true_pred().leads_to(always(lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper))))),
    ensures assumption_and_invariants_of_all_phases(zookeeper).entails(true_pred().leads_to(always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper))))),
{
    let spec1 = assumption_and_invariants_of_all_phases(zookeeper);
    let spec2 = spec1.and(always(lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper))));
    always_tla_forall_apply_for_sub_resource(spec2, SubResource::ConfigMap, zookeeper);
    always_tla_forall_apply_for_sub_resource(spec2, SubResource::StatefulSet, zookeeper);
    helper_invariants::lemma_always_cm_rv_stays_unchanged(spec2, zookeeper);
    simplify_predicate(spec2, always(lift_action(helper_invariants::cm_rv_stays_unchanged(zookeeper))));
    // Later we will use the invariant helper_invariants::cm_rv_stays_unchanged(zookeeper) to call
    // lemma_eventually_always_stateful_set_not_exists_or_matches_or_no_more_status_update
    let spec = spec2.and(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper))));
    always_tla_forall_apply_for_sub_resource(spec, SubResource::ConfigMap, zookeeper);
    always_tla_forall_apply_for_sub_resource(spec, SubResource::StatefulSet, zookeeper);

    assert_by(valid(stable(spec1)), {
        assumption_and_invariants_of_all_phases_is_stable(zookeeper);
    });

    assert_by(valid(stable(spec2)), {
        always_p_is_stable(lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper)));
        always_p_is_stable(lift_action(helper_invariants::cm_rv_stays_unchanged(zookeeper)));
        stable_and_n!(spec1, always(lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper))), always(lift_action(helper_invariants::cm_rv_stays_unchanged(zookeeper))));
    });

    assert_by(valid(stable(spec)), {
        always_p_is_stable(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)));
        stable_and_n!(spec2, always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper))));
    });

    assert_by(spec.entails(true_pred().leads_to(always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper))))), {
        // We first prove true ~> pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)
        terminate::reconcile_eventually_terminates(spec, zookeeper);
        lemma_from_reconcile_idle_to_scheduled(spec, zookeeper);
        lemma_from_scheduled_to_init_step(spec, zookeeper);
        lemma_from_init_step_to_after_create_headless_service_step(spec, zookeeper);
        assert forall |sub_resource: SubResource| sub_resource != SubResource::StatefulSet && sub_resource != SubResource::ConfigMap implies
        spec.entails(
            lift_state(#[trigger] pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper))
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource).get_AfterKRequestStep_1(), zookeeper)))
        ) by {
            always_tla_forall_apply_for_sub_resource(spec, sub_resource, zookeeper);
            lemma_from_after_get_resource_step_to_resource_matches(spec, zookeeper, sub_resource);
        }
        lemma_from_after_get_resource_step_to_resource_matches(spec, zookeeper, SubResource::ConfigMap);
        lemma_from_after_exists_stateful_set_step_to_after_get_stateful_set_step(spec, zookeeper);
        leads_to_trans_n!(
            spec, true_pred(), lift_state(|s: ZKCluster| { !s.ongoing_reconciles().contains_key(zookeeper.object_ref()) }),
            lift_state(|s: ZKCluster| { !s.ongoing_reconciles().contains_key(zookeeper.object_ref()) && s.scheduled_reconciles().contains_key(zookeeper.object_ref())}),
            lift_state(no_pending_req_at_zookeeper_step_with_zookeeper(zookeeper, ZookeeperReconcileStep::Init)),
            lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, zookeeper)),
            lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ClientService, zookeeper)),
            lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::AdminServerService, zookeeper)),
            lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ConfigMap, zookeeper)),
            lift_state(pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper)),
            lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper))
        );

        // We then prove pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper) ~> sub_resource_state_matches(SubResource::StatefulSet, zookeeper)
        lemma_from_after_get_stateful_set_step_to_stateful_set_matches(spec, zookeeper);
        leads_to_trans_temp(
            spec, true_pred(), lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)),
            lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper))
        );
        // Finally we prove stability
        lemma_stateful_set_is_stable(spec, zookeeper, true_pred());
    });

    assert_by(spec2.entails(true_pred().leads_to(always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper))))), {
        unpack_conditions_from_spec(spec2, always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper))), true_pred(), always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper))));
        temp_pred_equality(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper))), true_pred().and(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)))));
        helper_invariants::lemma_eventually_always_stateful_set_not_exists_or_matches_or_no_more_status_update(spec2, zookeeper);
        leads_to_trans_temp(spec2, true_pred(), always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper))), always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper))));
    });

    assert_by(spec1.entails(true_pred().leads_to(always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper))))), {
        unpack_conditions_from_spec(spec1, always(lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper))), true_pred(), always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper))));
        temp_pred_equality(always(lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper))), true_pred().and(always(lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper)))));
        leads_to_trans_temp(spec1, true_pred(), always(lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper))), always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper))));
    });
}

proof fn lemma_from_reconcile_idle_to_scheduled(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::schedule_controller_reconcile().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
    ensures
        spec.entails(lift_state(|s: ZKCluster| { !s.ongoing_reconciles().contains_key(zookeeper.object_ref()) })
        .leads_to(lift_state(|s: ZKCluster| {
            &&& !s.ongoing_reconciles().contains_key(zookeeper.object_ref())
            &&& s.scheduled_reconciles().contains_key(zookeeper.object_ref())
        }))),
{
    let pre = |s: ZKCluster| {
        &&& !s.ongoing_reconciles().contains_key(zookeeper.object_ref())
        &&& !s.scheduled_reconciles().contains_key(zookeeper.object_ref())
    };
    let post = |s: ZKCluster| {
        &&& !s.ongoing_reconciles().contains_key(zookeeper.object_ref())
        &&& s.scheduled_reconciles().contains_key(zookeeper.object_ref())
    };
    let input = zookeeper.object_ref();
    ZKCluster::lemma_pre_leads_to_post_by_schedule_controller_reconcile_borrow_from_spec(spec, input, ZKCluster::next(), ZKCluster::desired_state_is(zookeeper), pre, post);
    valid_implies_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine_temp(spec, lift_state(pre), lift_state(post), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: ZKCluster| {!s.ongoing_reconciles().contains_key(zookeeper.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zookeeper)))),
    ensures
        spec.entails(lift_state(|s: ZKCluster| {
            &&& !s.ongoing_reconciles().contains_key(zookeeper.object_ref())
            &&& s.scheduled_reconciles().contains_key(zookeeper.object_ref())
        }).leads_to(lift_state(no_pending_req_at_zookeeper_step_with_zookeeper(zookeeper, ZookeeperReconcileStep::Init)))),
{
    let pre = |s: ZKCluster| {
        &&& !s.ongoing_reconciles().contains_key(zookeeper.object_ref())
        &&& s.scheduled_reconciles().contains_key(zookeeper.object_ref())
    };
    let post = no_pending_req_at_zookeeper_step_with_zookeeper(zookeeper, ZookeeperReconcileStep::Init);
    let input = (None, Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zookeeper))
    );
    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::run_scheduled_reconcile(), pre, post);
}

proof fn lemma_from_init_step_to_after_create_headless_service_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
    ensures
        spec.entails(lift_state(no_pending_req_at_zookeeper_step_with_zookeeper(zookeeper, ZookeeperReconcileStep::Init)).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, zookeeper)))),
{
    let pre = no_pending_req_at_zookeeper_step_with_zookeeper(zookeeper, ZookeeperReconcileStep::Init);
    let post = pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, zookeeper);
    let input = (None, Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(ZKCluster::next()), lift_state(ZKCluster::crash_disabled())
    );
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.1.get_Some_0() != zookeeper.object_ref() {
                    assert(pre(s_prime));
                } else {
                    assert(post(s_prime));
                }
            },
            _ => {
                assert(pre(s_prime));
            }
        }
    }
    ZKCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post);
}

proof fn always_tla_forall_apply_for_sub_resource(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, zookeeper))))),
    ensures
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(res, zookeeper)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(res, zookeeper)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(res, zookeeper)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, zookeeper)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(res, zookeeper)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, zookeeper)), sub_resource);
}

}
