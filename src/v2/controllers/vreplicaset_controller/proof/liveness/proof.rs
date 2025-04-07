use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_lemmas::*, liveness::{resource_match::*, spec::*, terminate}, predicate::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use vstd::prelude::*;

verus! {

proof fn eventually_stable_reconciliation_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        spec.entails(next_with_wf(cluster, controller_id)),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vrs controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        // No other controllers interfere with the vrs controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
    ensures
        spec.entails(vrs_eventually_stable_reconciliation()),
{
    assert forall |vrs: VReplicaSetView| #[trigger] spec.entails(vrs_eventually_stable_reconciliation_per_cr(vrs)) by {
        eventually_stable_reconciliation_holds_per_cr(spec, vrs, cluster, controller_id);
    };
    spec_entails_tla_forall(spec, |vrs: VReplicaSetView| vrs_eventually_stable_reconciliation_per_cr(vrs));
    assert_by(
        tla_forall(|vrs: VReplicaSetView| vrs_eventually_stable_reconciliation_per_cr(vrs))
        == vrs_eventually_stable_reconciliation(), {
            assert forall |ex: Execution<ClusterState>| 
                tla_forall(|vrs: VReplicaSetView| vrs_eventually_stable_reconciliation_per_cr(vrs)).satisfied_by(ex)
                implies #[trigger] vrs_eventually_stable_reconciliation().satisfied_by(ex) by {
                assert((|vrs: VReplicaSetView| vrs_eventually_stable_reconciliation_per_cr(vrs)) 
                    =~= (|vrs: VReplicaSetView| Cluster::eventually_stable_reconciliation_per_cr(vrs, |vrs| current_state_matches(vrs))));
                assert((|vrs: VReplicaSetView| Cluster::eventually_stable_reconciliation_per_cr(vrs, |vrs| current_state_matches(vrs))) 
                    =~= (|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state((|vrs| current_state_matches(vrs))(vrs))))));
                assert(tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state((|vrs| current_state_matches(vrs))(vrs))))).satisfied_by(ex));
                assert(Cluster::eventually_stable_reconciliation(|vrs| current_state_matches(vrs)).satisfied_by(ex));
            }
            assert forall |ex: Execution<ClusterState>| 
                #[trigger] vrs_eventually_stable_reconciliation().satisfied_by(ex)
                implies tla_forall(|vrs: VReplicaSetView| vrs_eventually_stable_reconciliation_per_cr(vrs)).satisfied_by(ex) by {
                assert(Cluster::eventually_stable_reconciliation(|vrs| current_state_matches(vrs)).satisfied_by(ex));
                assert(tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state((|vrs| current_state_matches(vrs))(vrs))))).satisfied_by(ex));
                assert((|vrs: VReplicaSetView| Cluster::eventually_stable_reconciliation_per_cr(vrs, |vrs| current_state_matches(vrs))) 
                    =~= (|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state((|vrs| current_state_matches(vrs))(vrs))))));
                assert((|vrs: VReplicaSetView| vrs_eventually_stable_reconciliation_per_cr(vrs)) 
                    =~= (|vrs: VReplicaSetView| Cluster::eventually_stable_reconciliation_per_cr(vrs, |vrs| current_state_matches(vrs))));
            }

            temp_pred_equality(
                tla_forall(|vrs: VReplicaSetView| vrs_eventually_stable_reconciliation_per_cr(vrs)),
                vrs_eventually_stable_reconciliation()
            );
        }
    )
}

proof fn eventually_stable_reconciliation_holds_per_cr(spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        spec.entails(next_with_wf(cluster, controller_id)),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vrs controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        // No other controllers interfere with the vrs controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
    ensures
        spec.entails(vrs_eventually_stable_reconciliation_per_cr(vrs)),
{
    // There are two specs we wish to deal with: one, `spec`, has `cluster.init()` true,
    // while the other spec, `stable_spec`, has it false.
    assume(false);
    let stable_spec = stable_spec(cluster, controller_id);

    vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property(
        spec, cluster, controller_id
    );
    assert(spec.entails(stable_spec));
    
    // assert(spec.entails(stable_spec(cluster, controller_id)));
    // vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property(
    //     spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
    // )

    assumption_and_invariants_of_all_phases_is_stable(vrs, cluster, controller_id);
    lemma_true_leads_to_always_current_state_matches(spec, vrs, cluster, controller_id);
    reveal_with_fuel(spec_before_phase_n, 8);

    
    spec_before_phase_n_entails_true_leads_to_current_state_matches(7, spec, vrs, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(6, spec, vrs, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(5, spec, vrs, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(4, spec, vrs, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(3, spec, vrs, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(2, spec, vrs, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(1, spec, vrs, cluster, controller_id);

    let assumption = always(lift_state(Cluster::desired_state_is(vrs)));
    // TODO: rethink this a bit.
    unpack_conditions_from_spec(invariants(vrs, cluster, controller_id), assumption, true_pred(), always(lift_state(current_state_matches(vrs))));
    temp_pred_equality(true_pred().and(assumption), assumption);

    assert_by(spec.and(derived_invariants_since_beginning(vrs, cluster, controller_id)).entails(invariants(vrs, cluster, controller_id)), {
        assert(spec.and(derived_invariants_since_beginning(vrs, cluster, controller_id)).entails(derived_invariants_since_beginning(vrs, cluster, controller_id)));
        assert(spec.entails(next_with_wf(cluster, controller_id)));
        entails_and_different_temp(
            spec, derived_invariants_since_beginning(vrs, cluster, controller_id),
            next_with_wf(cluster, controller_id), true_pred(),
        );
        temp_pred_equality(next_with_wf(cluster, controller_id), next_with_wf(cluster, controller_id).and(true_pred()));
        assert(spec.and(derived_invariants_since_beginning(vrs, cluster, controller_id)).entails(next_with_wf(cluster, controller_id)));
        entails_and_temp(
            spec.and(derived_invariants_since_beginning(vrs, cluster, controller_id)),
            next_with_wf(cluster, controller_id),
            derived_invariants_since_beginning(vrs, cluster, controller_id)
        );
    });
    entails_trans(
        spec.and(derived_invariants_since_beginning(vrs, cluster, controller_id)), invariants(vrs, cluster, controller_id),
        always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches(vrs))))
    );
    //assert(spec.entails(next_with_wf(cluster, )));
    spec_entails_all_invariants(spec, vrs, cluster, controller_id);
    simplify_predicate(spec, derived_invariants_since_beginning(vrs, cluster, controller_id));
}

#[verifier(external_body)]
proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(i: nat, spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    requires
        1 <= i <= 7,
        valid(stable(spec_before_phase_n(i, vrs, cluster, controller_id))),
        spec.and(spec_before_phase_n(i + 1, vrs, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(current_state_matches(vrs))))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
    ensures spec.and(spec_before_phase_n(i, vrs, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(current_state_matches(vrs))))),
{
    reveal_with_fuel(spec_before_phase_n, 8);
    temp_pred_equality(
        spec.and(spec_before_phase_n(i + 1, vrs, cluster, controller_id)),
        spec.and(spec_before_phase_n(i, vrs, cluster, controller_id))
            .and(invariants_since_phase_n(i, vrs, cluster, controller_id))
    );
    spec_of_previous_phases_entails_eventually_new_invariants(spec, vrs, cluster, controller_id, i);
    //unpack_conditions_from_spec(spec.entails(spec_before_phase_n), )
    assume(false);
}

proof fn lemma_true_leads_to_always_current_state_matches(provided_spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int) 
    requires
        provided_spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        provided_spec.entails(next_with_wf(cluster, controller_id)),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vrs controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        // No other controllers interfere with the vrs controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> provided_spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
    ensures
        provided_spec.and(assumption_and_invariants_of_all_phases(vrs, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(current_state_matches(vrs))))),
{
    let spec = provided_spec.and(assumption_and_invariants_of_all_phases(vrs, cluster, controller_id));
    // assert non-interference property on combined spec.
    assert forall |other_id| 
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id) 
            ==> provided_spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))))
        implies 
        cluster.controller_models.remove(controller_id).contains_key(other_id) 
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))) by {
        if cluster.controller_models.remove(controller_id).contains_key(other_id) {
            assert(provided_spec.entails(always(lift_state(vrs_not_interfered_by(other_id)))));
            entails_and_different_temp(
                provided_spec,
                assumption_and_invariants_of_all_phases(vrs, cluster, controller_id),
                always(lift_state(vrs_not_interfered_by(other_id))),
                true_pred()
            );
            assert(spec.entails(always(lift_state(vrs_not_interfered_by(other_id))).and(true_pred())));
            temp_pred_equality(
                always(lift_state(vrs_not_interfered_by(other_id))).and(true_pred()),
                always(lift_state(vrs_not_interfered_by(other_id)))
            );
        }
    }

    let reconcile_idle = lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) });
    let reconcile_scheduled = lift_state(|s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(vrs.object_ref())
    });
    let at_init = lift_state(no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init));
    let diff_at_init = |diff| lift_state(
        |s: ClusterState| {
            &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let stronger_post = |s: ClusterState| {
        &&& current_state_matches(vrs)(s)
        &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
    };

    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(spec, cluster, controller_id);
    use_tla_forall(
        spec,
        |vrs: VReplicaSetView| 
            true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()))),
        vrs
    );
    always_tla_forall_apply(
        spec,
        |vrs: VReplicaSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        vrs
    );

    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(vrs).

    // The following two lemmas show that spec |= reconcile_idle ~> init /\ no_pending_req.
    lemma_from_reconcile_idle_to_scheduled(spec, vrs, cluster, controller_id);
    lemma_from_scheduled_to_init_step(spec, vrs, cluster, controller_id);

    // Show that true == exists |diff| num_diff_pods_is(diff).
    assert_by(true_pred::<ClusterState>() == tla_exists(|diff| lift_state(num_diff_pods_is(vrs, diff))), {
        let exists_num_diff_pods_is = tla_exists(|diff| lift_state(num_diff_pods_is(vrs, diff)));
        assert forall |ex: Execution<ClusterState>|
        true_pred::<ClusterState>().satisfied_by(ex) implies #[trigger] exists_num_diff_pods_is.satisfied_by(ex) by {
            let s = ex.head();
            let pods = matching_pods(vrs, s.resources());
            let diff = pods.len() - vrs.spec.replicas.unwrap_or(0);

            // Instantiate exists statement.
            assert((|diff| lift_state(num_diff_pods_is(vrs, diff)))(diff).satisfied_by(ex));
        }
        assert(valid(true_pred::<ClusterState>().implies(exists_num_diff_pods_is)));
        temp_pred_equality(true_pred::<ClusterState>(), tla_exists(|diff| lift_state(num_diff_pods_is(vrs, diff))));
    });

    // Show that init /\ no_pending_req ~> exists |diff| (num_diff_pods_is(diff) /\ init)
    assert_by(spec.entails(at_init.leads_to(tla_exists(diff_at_init))), {
        assert forall |ex: Execution<ClusterState>|
        at_init.satisfied_by(ex) implies #[trigger] tla_exists(diff_at_init).satisfied_by(ex) by {
            assert(tla_exists(|diff| lift_state(num_diff_pods_is(vrs, diff))).satisfied_by(ex));
            let diff = choose |diff| lift_state(#[trigger] num_diff_pods_is(vrs, diff)).satisfied_by(ex);
            assert(diff_at_init(diff).satisfied_by(ex));
        }
        always_implies_to_leads_to(spec, at_init, tla_exists(diff_at_init));
    });

    // The following shows exists |diff| (num_diff_pods_is(diff) /\ init) ~> current_state_matches(vrs)
    assert forall |diff| #[trigger] spec.entails(diff_at_init(diff).leads_to(lift_state(stronger_post))) by {
        lemma_from_diff_and_init_to_current_state_matches(vrs, spec, cluster, controller_id, diff);
    }
    leads_to_exists_intro(spec, diff_at_init, lift_state(stronger_post));

    // Chain everything together
    leads_to_trans_n!(
        spec,
        true_pred(),
        reconcile_idle,
        reconcile_scheduled,
        at_init,
        tla_exists(diff_at_init),
        lift_state(stronger_post)
    );

    // Further prove stability
    lemma_current_state_matches_is_stable(spec, vrs, true_pred(), cluster, controller_id);
}

proof fn lemma_from_reconcile_idle_to_scheduled(spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
    ensures
        spec.entails(lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) })
        .leads_to(lift_state(|s: ClusterState| {
            &&& !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
            &&& s.scheduled_reconciles(controller_id).contains_key(vrs.object_ref())
        }))),
{
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
        &&& !s.scheduled_reconciles(controller_id).contains_key(vrs.object_ref())
    };
    let post = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(vrs.object_ref())
    };
    let input = vrs.object_ref();
    let stronger_pre = |s| {
        &&& pre(s)
        &&& Cluster::desired_state_is(vrs)(s)
    };
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s_prime)
    };
    always_to_always_later(spec, lift_state(Cluster::desired_state_is(vrs)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        later(lift_state(Cluster::desired_state_is(vrs)))
    );
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(
        spec,
        controller_id,
        input,
        stronger_next,
        stronger_pre,
        post
    );
    temp_pred_equality(lift_state(pre).and(lift_state(Cluster::desired_state_is(vrs))), lift_state(stronger_pre));
    leads_to_by_borrowing_inv(spec, lift_state(pre), lift_state(post), lift_state(Cluster::desired_state_is(vrs)));
    entails_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to_combine(spec, lift_state(pre), lift_state(post), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(|s: ClusterState| {!s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())}));
}

proof fn lemma_from_scheduled_to_init_step(spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| 
            cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, vrs)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)))),
        cluster.controller_models[controller_id].reconcile_model 
            == Cluster::installed_reconcile_model::<VReplicaSetReconciler, VReplicaSetReconcileState, VReplicaSetView, VoidEReqView, VoidERespView>(),
    ensures
        spec.entails(lift_state(|s: ClusterState| {
            &&& !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
            &&& s.scheduled_reconciles(controller_id).contains_key(vrs.object_ref())
        }).leads_to(lift_state(
            no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init)
        ))),
{
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(vrs.object_ref())
    };
    let post = no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init);
    let input = (None, Some(vrs.object_ref()));
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime) 
        &&& Cluster::crash_disabled(controller_id)(s) 
        &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s) 
        &&& Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, vrs)(s) 
        &&& Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)(s)
    };

    VReplicaSetReconcileState::marshal_preserves_integrity();
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, vrs)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id))
    );
    cluster.lemma_pre_leads_to_post_by_controller(
        spec,
        controller_id,
        input,
        stronger_next,
        ControllerStep::RunScheduledReconcile,
        pre,
        post
    );
}

}
