// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants,
        liveness::{
            resource_match::*,
            spec::*,
            terminate,
        },
        predicate::*,
        resource::*,
    },
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{prelude::*, string::*};

verus! {

proof fn eventually_stable_reconciliation_holds_per_cr(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(next_with_wf(cluster, controller_id)),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(rmq_eventually_stable_reconciliation_per_cr(rabbitmq)),
{
    // There are two specs we wish to deal with: one, `spec`, has `cluster.init()` true,
    // while the other spec, `stable_spec`, has it false.
    let stable_spec = stable_spec(cluster, controller_id);
    assumption_and_invariants_of_all_phases_is_stable(controller_id, cluster, rabbitmq);
    stable_spec_and_assumption_and_invariants_of_all_phases_is_stable(controller_id, cluster, rabbitmq);

    lemma_true_leads_to_always_current_state_matches(stable_spec, controller_id, cluster, rabbitmq);
    reveal_with_fuel(spec_before_phase_n, 9);

    spec_before_phase_n_entails_true_leads_to_current_state_matches(stable_spec, controller_id, cluster, 8, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(stable_spec, controller_id, cluster, 7, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(stable_spec, controller_id, cluster, 6, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(stable_spec, controller_id, cluster, 5, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(stable_spec, controller_id, cluster, 4, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(stable_spec, controller_id, cluster, 3, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(stable_spec, controller_id, cluster, 2, rabbitmq);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(stable_spec, controller_id, cluster, 1, rabbitmq);

    let assumption = always(lift_state(Cluster::desired_state_is(rabbitmq)));
    temp_pred_equality(
        stable_spec.and(spec_before_phase_n(controller_id, 1, cluster, rabbitmq)),
        stable_spec.and(invariants(controller_id, cluster, rabbitmq))
            .and(assumption)
    );
    unpack_conditions_from_spec(stable_spec.and(invariants(controller_id, cluster, rabbitmq)), assumption, true_pred(), always(lift_state(current_state_matches(rabbitmq))));
    temp_pred_equality(true_pred().and(assumption), assumption);

    // Annoying non-automatic unpacking of the spec for one precondition.
    entails_trans(
        spec,
        next_with_wf(cluster, controller_id),
        always(lift_action(cluster.next()))
    );
    sm_spec_entails_all_invariants(controller_id, cluster, spec, rabbitmq);
    simplify_predicate(spec, derived_invariants_since_beginning(controller_id, cluster, rabbitmq));

    spec_and_invariants_entails_stable_spec_and_invariants(spec, controller_id, cluster, rabbitmq);
    entails_trans(
        spec.and(derived_invariants_since_beginning(controller_id, cluster, rabbitmq)),
        stable_spec.and(invariants(controller_id, cluster, rabbitmq)),
        always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(current_state_matches(rabbitmq))))
    );
}

proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(spec: TempPred<ClusterState>, controller_id: int, cluster: Cluster, i: nat, rabbitmq: RabbitmqClusterView)
    requires
        1 <= i <= 8,
        valid(stable(spec.and(spec_before_phase_n(controller_id, i, cluster, rabbitmq)))),
        spec.and(spec_before_phase_n(controller_id, i + 1, cluster, rabbitmq)).entails(true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.and(spec_before_phase_n(controller_id, i, cluster, rabbitmq)).entails(true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))),
{
    reveal_with_fuel(spec_before_phase_n, 9);
    temp_pred_equality(
        spec.and(spec_before_phase_n(controller_id, i + 1, cluster, rabbitmq)),
        spec.and(spec_before_phase_n(controller_id, i, cluster, rabbitmq))
            .and(invariants_since_phase_n(controller_id, i, cluster, rabbitmq))
    );
    spec_of_previous_phases_entails_eventually_new_invariants(spec, controller_id, cluster, i, rabbitmq);
    unpack_conditions_from_spec(spec.and(spec_before_phase_n(controller_id, i, cluster, rabbitmq)), invariants_since_phase_n(controller_id, i, cluster, rabbitmq), true_pred(), always(lift_state(current_state_matches(rabbitmq))));
    temp_pred_equality(
        true_pred().and(invariants_since_phase_n(controller_id, i, cluster, rabbitmq)),
        invariants_since_phase_n(controller_id, i, cluster, rabbitmq)
    );
    leads_to_trans(spec.and(spec_before_phase_n(controller_id, i, cluster, rabbitmq)), true_pred(), invariants_since_phase_n(controller_id, i, cluster, rabbitmq), always(lift_state(current_state_matches(rabbitmq))));
}

proof fn lemma_true_leads_to_always_current_state_matches(provided_spec: TempPred<ClusterState>, controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView)
    requires
        provided_spec.entails(next_with_wf(cluster, controller_id)),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        provided_spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures
        provided_spec.and(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)).entails(true_pred().leads_to(always(lift_state(current_state_matches(rabbitmq))))),
{
    let spec = provided_spec.and(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq));
    // Assert rely condition on combined spec.
    entails_and_different_temp(
        provided_spec,
        assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq),
        always(lift_state(rmq_rely_conditions(cluster, controller_id))),
        true_pred()
    );
    temp_pred_equality(
        always(lift_state(rmq_rely_conditions(cluster, controller_id))).and(true_pred()),
        always(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );

    // spec = provided_spec /\ assumption_and_invariants_of_all_phases => assumption_and_invariants_of_all_phases
    entails_and_different_temp(
        provided_spec,
        assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq),
        true_pred(),
        assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)
    );
    temp_pred_equality(
        true_pred().and(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)),
        assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)
    );

    // Derive cluster_invariants_since_reconciliation for each sub_resource from the combined spec.
    assert forall |sub_resource: SubResource| spec.entails(always(lift_state(#[trigger] cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))) by {
        spec_entails_assumptions_and_invariants_of_all_phases_implies_cluster_invariants_since_reconciliation(
            spec, controller_id, cluster, sub_resource, rabbitmq
        );
    }

    assert forall |sub_resource: SubResource| spec
        .entails(true_pred().leads_to(always(lift_state(#[trigger] resource_state_matches(sub_resource, rabbitmq))))) by {
        lemma_true_leads_to_always_state_matches_for_all(spec, cluster, controller_id, rabbitmq);
    }
    let a_to_p = |res: SubResource| lift_state(resource_state_matches(res, rabbitmq));
    helper_invariants::leads_to_always_tla_forall_subresource(spec, true_pred(), a_to_p);
    assert forall |ex| #[trigger] tla_forall(a_to_p).satisfied_by(ex) implies lift_state(current_state_matches(rabbitmq)).satisfied_by(ex) by {
        let s = ex.head();
        assert forall |res: SubResource| #[trigger] resource_state_matches(res, rabbitmq)(s) by {
            tla_forall_apply(a_to_p, res);
            assert(a_to_p(res).satisfied_by(ex));
            assert(resource_state_matches(res, rabbitmq)(s));
        }
    }
    temp_pred_equality(tla_forall(|res: SubResource| lift_state(resource_state_matches(res, rabbitmq))), lift_state(current_state_matches(rabbitmq)));
}

#[verifier(spinoff_prover)]
proof fn lemma_true_leads_to_always_state_matches_for_all(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        spec.entails(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)),
        forall |sub_resource: SubResource|
            spec.entails(always(lift_state(#[trigger] cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
    ensures
        forall |sub_resource: SubResource|
            spec.entails(true_pred().leads_to(always(lift_state(#[trigger] resource_state_matches(sub_resource, rabbitmq))))),
{
    let stable_spec = assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq);
    assert forall |action: ActionKind, sub_resource: SubResource| #![auto] spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(action, sub_resource)))))) by {
        always_tla_forall_apply(stable_spec, |step: (ActionKind, SubResource)| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1)))), (action, sub_resource));
        entails_trans(spec,
            stable_spec,
            always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(action, sub_resource)))))
        );
    }
    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(stable_spec, cluster, controller_id, rabbitmq);
    entails_trans(spec,
        stable_spec,
        true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))
    );
    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(rabbitmq).

    let idle_state = lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref()));
    let scheduled_state = lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref()) && s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref()));
    let init_state = lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, RabbitmqReconcileStep::Init));
    // The following two lemmas show that spec |= reconcile_idle ~> init /\ no_pending_req.
    lemma_from_reconcile_idle_to_scheduled(controller_id, cluster, stable_spec, rabbitmq);
    lemma_from_scheduled_to_init_step(controller_id, cluster, stable_spec, rabbitmq);

    // After applying this lemma, we get spec |= init /\ no_pending_req ~> create_headless_service /\ pending_req.
    lemma_from_init_step_to_after_get_headless_service_step(controller_id, cluster, stable_spec, rabbitmq);

    leads_to_trans_n!(stable_spec, true_pred(), idle_state, scheduled_state, init_state);
    entails_trans(spec, stable_spec, true_pred().leads_to(init_state));
    entails_trans(spec, stable_spec, init_state.leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, rabbitmq, controller_id))));

    entails_trans(spec, stable_spec, always(lift_action(cluster.next())));
    entails_trans(spec, stable_spec, tla_forall(|i| cluster.api_server_next().weak_fairness(i)));
    entails_trans(spec, stable_spec, tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1))));

    // We first show that the reconciler can go to at_after_get_resource_step(next_resource) from at_after_get_resource_step(sub_resource)
    // where sub_resource cannot be StatefulSet because it's the last resource to be processed and doesn't have its next_resource.
    // Through this, we can string all the resources together in sequence. This also means that the system can go to any
    // at_after_get_resource_step(sub_resource) from an arbitrary state.
    assert forall |sub_resource: SubResource| sub_resource != SubResource::VStatefulSetView implies
    spec.entails(
        lift_state(#[trigger] pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id))
            .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource)->AfterKRequestStep_1, rabbitmq, controller_id)))
    ) by {
        let next_resource = next_resource_after(sub_resource)->AfterKRequestStep_1;
        lemma_from_after_get_resource_step_to_resource_matches(controller_id, cluster, spec, rabbitmq, sub_resource, next_resource);
    }
    // Thanks to the recursive construction of macro.
    leads_to_trans_n!(
        spec, true_pred(),
        init_state,
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Service, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ErlangCookieSecret, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::DefaultUserSecret, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::PluginsConfigMap, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServerConfigMap, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::ServiceAccount, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::Role, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::RoleBinding, rabbitmq, controller_id)),
        lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq, controller_id))
    );

    // Since we already have true ~> at_after_get_resource_step(sub_resource), and we can get at_after_get_resource_step(sub_resource)
    // ~> resource_state_matches(sub_resource, rabbitmq) by applying lemma lemma_from_after_get_resource_step_to_resource_matches,
    // we now have true ~> resource_state_matches(sub_resource, rabbitmq).
    assert forall |sub_resource: SubResource|
    spec.entails(
        true_pred().leads_to(lift_state(#[trigger] resource_state_matches(sub_resource, rabbitmq)))
    ) by {
        // For non-VStatefulSetView resources, next_resource is used but the first ensures still applies to all.
        // We pass VStatefulSetView as a dummy next_resource for VStatefulSetView itself (the second ensures won't fire).
        let next_resource = if sub_resource != SubResource::VStatefulSetView {
            next_resource_after(sub_resource)->AfterKRequestStep_1
        } else {
            SubResource::VStatefulSetView
        };
        lemma_from_after_get_resource_step_to_resource_matches(controller_id, cluster, spec, rabbitmq, sub_resource, next_resource);
        leads_to_trans(
            spec, true_pred(), lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id)),
            lift_state(resource_state_matches(sub_resource, rabbitmq))
        );
    }

    // Now we further prove stability: given true ~> resource_state_matches(sub_resource, rabbitmq)
    // we prove true ~> []resource_state_matches(sub_resource, rabbitmq)
    //
    // The proof proceeds in two stages:
    // 1. First prove CM stability: true ~> []resource_state_matches(ServerConfigMap, rabbitmq)
    //    The CM lemma does not need cm_rv_stays_unchanged as a precondition.
    // 2. Then prove all other resources are stable, borrowing CM's always-true property
    //    to obtain cm_rv_stays_unchanged.

    // Stage 1: CM stability
    // We show resource_state_matches(CM) is preserved by the cluster transition,
    // then apply leads_to_stable.
    let cm_stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(cm_stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap))
    );
    assert forall |s: ClusterState, s_prime: ClusterState|
        resource_state_matches(SubResource::ServerConfigMap, rabbitmq)(s) && #[trigger] cm_stronger_next(s, s_prime)
        implies resource_state_matches(SubResource::ServerConfigMap, rabbitmq)(s_prime) by {
        lemma_current_state_matches_preserves_from_s_to_s_prime_for_cm(
            controller_id, cluster, rabbitmq, s, s_prime
        );
    }
    leads_to_stable(
        spec, lift_action(cm_stronger_next), true_pred(),
        lift_state(resource_state_matches(SubResource::ServerConfigMap, rabbitmq))
    );

    // Stage 2: Other resources.
    // For each sub_resource != CM:
    // 1. Use leads_to_with_always to get (true /\ []cm_mat) ~> (sub_mat /\ []cm_mat) from true ~> sub_mat
    // 2. Chain with true ~> []cm_mat to get true ~> (sub_mat /\ []cm_mat)
    // 3. Weaken to get true ~> (sub_mat /\ cm_mat) = true ~> combined
    // 4. Show combined is preserved (leads_to_stable) to get true ~> []combined
    // 5. Weaken to get true ~> []sub_mat
    assert forall |sub_resource: SubResource|
    spec.entails(
        true_pred().leads_to(always(lift_state(#[trigger] resource_state_matches(sub_resource, rabbitmq))))
    ) by {
        if sub_resource == SubResource::ServerConfigMap {
            // Already proved above in Stage 1.
        } else {

            // Define the combined predicate.
            let sub_mat = lift_state(resource_state_matches(sub_resource, rabbitmq));
            let cm_mat = lift_state(resource_state_matches(SubResource::ServerConfigMap, rabbitmq));
            let combined = |s: ClusterState| {
                &&& resource_state_matches(sub_resource, rabbitmq)(s)
                &&& resource_state_matches(SubResource::ServerConfigMap, rabbitmq)(s)
            };

            // Step 1: leads_to_with_always gives (true /\ []cm_mat) ~> (sub_mat /\ []cm_mat)
            leads_to_with_always(spec, true_pred(), sub_mat, cm_mat);

            // Step 2 & 3: Chain true ~> []cm_mat ~> (sub_mat /\ []cm_mat) then weaken to combined
            temp_pred_equality(true_pred().and(always(cm_mat)), always(cm_mat));
            leads_to_trans(spec, true_pred(), always(cm_mat), sub_mat.and(always(cm_mat)));

            // Weaken sub_mat /\ always(cm_mat) to lift_state(combined)
            // sub_mat /\ always(cm_mat) entails lift_state(combined) (at the current state)
            assert(sub_mat.and(always(cm_mat)).entails(lift_state(combined))) by {
                assert forall |ex| #[trigger] sub_mat.and(always(cm_mat)).satisfied_by(ex) implies lift_state(combined).satisfied_by(ex) by {
                    always_to_current(ex, cm_mat);
                }
            }
            entails_implies_leads_to(spec, sub_mat.and(always(cm_mat)), lift_state(combined));
            leads_to_trans(spec, true_pred(), sub_mat.and(always(cm_mat)), lift_state(combined));

            // Step 4: Show combined is stable using leads_to_stable
            let combined_stronger_next = |s: ClusterState, s_prime: ClusterState| {
                &&& cluster.next()(s, s_prime)
                &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
                &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap)(s)
            };
            combine_spec_entails_always_n!(
                spec, lift_action(combined_stronger_next),
                lift_action(cluster.next()),
                lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
                lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::ServerConfigMap))
            );
            assert forall |s: ClusterState, s_prime: ClusterState|
                combined(s) && #[trigger] combined_stronger_next(s, s_prime)
                implies combined(s_prime) by {
                // CM stays matched and cm_rv_stays_unchanged.
                lemma_current_state_matches_preserves_from_s_to_s_prime_for_cm(
                    controller_id, cluster, rabbitmq, s, s_prime
                );
                // The other resource stays matched (needs cm_rv_stays_unchanged).
                lemma_current_state_matches_preserves_from_s_to_s_prime(
                    controller_id, cluster, sub_resource, rabbitmq, s, s_prime
                );
            }
            leads_to_stable(
                spec, lift_action(combined_stronger_next), true_pred(),
                lift_state(combined)
            );

            // Step 5: Weaken true ~> []combined to true ~> []sub_mat
            leads_to_always_enhance(
                spec, true_pred(), true_pred(),
                lift_state(combined),
                lift_state(resource_state_matches(sub_resource, rabbitmq))
            );
        }
    }
}

proof fn lemma_from_reconcile_idle_to_scheduled(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
    ensures
        spec.entails(lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref()) })
        .leads_to(lift_state(|s: ClusterState| {
            &&& !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())
            &&& s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref())
        }))),
{
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())
        &&& !s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref())
    };
    let post = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref())
    };
    let input = rabbitmq.object_ref();
    let stronger_pre = |s| {
        &&& pre(s)
        &&& Cluster::desired_state_is(rabbitmq)(s)
    };
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(rabbitmq)(s_prime)
    };
    always_to_always_later(spec, lift_state(Cluster::desired_state_is(rabbitmq)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        later(lift_state(Cluster::desired_state_is(rabbitmq)))
    );
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, input, stronger_next, stronger_pre, post);
    temp_pred_equality(lift_state(pre).and(lift_state(Cluster::desired_state_is(rabbitmq))), lift_state(stronger_pre));
    leads_to_by_borrowing_inv(spec, lift_state(pre), lift_state(post), lift_state(Cluster::desired_state_is(rabbitmq)));
    entails_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine(spec, lift_state(pre), lift_state(post), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: ClusterState| {!s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
    ensures
        spec.entails(lift_state(|s: ClusterState| {
            &&& !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())
            &&& s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref())
        }).leads_to(lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, RabbitmqReconcileStep::Init)))),
{
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(rabbitmq.object_ref())
    };
    let post = no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, RabbitmqReconcileStep::Init);
    let input = (None, Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, rabbitmq)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s_prime)
    };
    always_to_always_later(spec, lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, rabbitmq)),
        later(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))
    );
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        RabbitmqReconcileState::marshal_preserves_integrity();
    }
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::RunScheduledReconcile, pre, post);
}

proof fn lemma_from_init_step_to_after_get_headless_service_step(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
    ensures
        spec.entails(lift_state(no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, RabbitmqReconcileStep::Init))
            .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, rabbitmq, controller_id)))),
{
    let pre = no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, RabbitmqReconcileStep::Init);
    let post = pending_req_in_flight_at_after_get_resource_step(SubResource::HeadlessService, rabbitmq, controller_id);
    let input = (None, Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id))
    );
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        RabbitmqReconcileState::marshal_preserves_integrity();
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.2->0 == rabbitmq.object_ref() {
                    assert(post(s_prime));
                } else {
                    assert(pre(s_prime));
                }
            },
            _ => {
                assert(pre(s_prime));
            }
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        RabbitmqReconcileState::marshal_preserves_integrity();
    }
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post);
}

proof fn always_tla_forall_apply_for_sub_resource(controller_id: int, spec: TempPred<ClusterState>, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)),
    ensures
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_get_then_requests_and_update_resource_status_requests_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)))),
{
    let stable_spec = assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq);
    entails_trans(spec, stable_spec, always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, res, rabbitmq)))));
    entails_trans(spec, stable_spec, always(tla_forall(|res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, res, rabbitmq)))));
    entails_trans(spec, stable_spec, always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(res, rabbitmq)))));
    entails_trans(spec, stable_spec, always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_get_then_requests_and_update_resource_status_requests_in_flight(res, rabbitmq)))));
    entails_trans(spec, stable_spec, always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq)))));
    entails_trans(spec, stable_spec, always(tla_forall(|res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, rabbitmq)))));
    entails_trans(spec, stable_spec, always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(res, rabbitmq)))));
    
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_get_then_requests_and_update_resource_status_requests_in_flight(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(res, rabbitmq)), sub_resource);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(res, rabbitmq)), sub_resource);
}

#[verifier(rlimit(300))]
#[verifier(spinoff_prover)]
pub proof fn spec_entails_assumptions_and_invariants_of_all_phases_implies_cluster_invariants_since_reconciliation(
    spec: TempPred<ClusterState>, controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
requires
    spec.entails(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)),
ensures
    spec.entails(always(lift_state(#[trigger] cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
{
    let stable_spec = assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq);
    always_tla_forall_apply_for_sub_resource(controller_id, spec, cluster, sub_resource, rabbitmq);
    // FIXME
    assume(stable_spec.entails(always(lift_state(helper_invariants::sts_in_etcd_with_rmq_key_match_rmq_selector_and_owner(rabbitmq)))));

    assert(stable_spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))));
    assert(stable_spec.entails(always(lift_state(Cluster::req_drop_disabled()))));
    assert(stable_spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))));
    assert(stable_spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))));
    assert(stable_spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))));
    assert(stable_spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)))));
    assert(stable_spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))));
    assert(stable_spec.entails(always(lift_state(Cluster::etcd_objects_have_unique_uids()))));
    assert(stable_spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))));
    assert(stable_spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))));
    assert(stable_spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()))));
    assert(stable_spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))));
    assert(stable_spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))));
    assert(stable_spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))));
    assert(stable_spec.entails(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))));
    assert(stable_spec.entails(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)))));
    assert(stable_spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))));
    assert(stable_spec.entails(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))));
    assert(stable_spec.entails(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)))));
    assert(stable_spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(controller_id)))));
    assert(stable_spec.entails(always(lift_state(Cluster::etcd_is_finite()))));
    assert(stable_spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rabbitmq.object_ref())))));
    assert(stable_spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))));
    assert(stable_spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))));
    assert(stable_spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))));
    assert(stable_spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))));
    assert(stable_spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))));
    assert(stable_spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, rabbitmq.object_ref())))));
    assert(stable_spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))));
    assert(stable_spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)))));
    assert(stable_spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)))));
    assert(stable_spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)))));
    assert(stable_spec.entails(always(lift_state(helper_invariants::no_get_then_requests_and_update_resource_status_requests_in_flight(sub_resource, rabbitmq)))));
    assert(stable_spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)))));
    assert(stable_spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq)))));
    assert(stable_spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))));
    assert(stable_spec.entails(always(lift_state(helper_invariants::sts_in_etcd_with_rmq_key_match_rmq_selector_and_owner(rabbitmq)))));
    // Combine all extracted invariants into cluster_invariants_since_reconciliation
    combine_spec_entails_always_n!(stable_spec,
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::etcd_objects_have_unique_uids()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rabbitmq.object_ref())),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, rabbitmq.object_ref())),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)),
        lift_state(helper_invariants::no_get_then_requests_and_update_resource_status_requests_in_flight(sub_resource, rabbitmq)),
        lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)),
        lift_state(helper_invariants::sts_in_etcd_with_rmq_key_match_rmq_selector_and_owner(rabbitmq))
    );
    entails_trans(spec, stable_spec, always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource))));
}

}
