use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_lemmas::*, liveness::{spec::*, terminate, resource_match::*}, predicate::*},
    trusted::{
        liveness_theorem::*, 
        rely_guarantee::*,
        spec_types::*, 
        step::*
    },
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*; // shortcut for steps
use crate::vdeployment_controller::proof::helper_invariants;
use crate::vreplicaset_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

proof fn eventually_stable_reconciliation_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        spec.entails(next_with_wf(cluster, controller_id)),
        // The vd type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vd controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        // No other controllers interfere with the vd controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures
        spec.entails(vd_eventually_stable_reconciliation()),
{
    assert forall |vd: VDeploymentView| #[trigger] spec.entails(vd_eventually_stable_reconciliation_per_cr(vd)) by {
        eventually_stable_reconciliation_holds_per_cr(spec, vd, cluster, controller_id);
    };
    spec_entails_tla_forall(spec, |vd: VDeploymentView| vd_eventually_stable_reconciliation_per_cr(vd));
    assert_by(
        tla_forall(|vd: VDeploymentView| vd_eventually_stable_reconciliation_per_cr(vd))
        == vd_eventually_stable_reconciliation(), {
            assert forall |ex: Execution<ClusterState>| 
                tla_forall(|vd: VDeploymentView| vd_eventually_stable_reconciliation_per_cr(vd)).satisfied_by(ex)
                implies #[trigger] vd_eventually_stable_reconciliation().satisfied_by(ex) by {
                assert((|vd: VDeploymentView| vd_eventually_stable_reconciliation_per_cr(vd)) 
                    =~= (|vd: VDeploymentView| Cluster::eventually_stable_reconciliation_per_cr(vd, |vd| current_state_matches(vd))));
                assert((|vd: VDeploymentView| Cluster::eventually_stable_reconciliation_per_cr(vd, |vd| current_state_matches(vd))) 
                    =~= (|vd: VDeploymentView| always(lift_state(Cluster::desired_state_is(vd))).leads_to(always(lift_state((|vd| current_state_matches(vd))(vd))))));
                assert(tla_forall(|vd: VDeploymentView| always(lift_state(Cluster::desired_state_is(vd))).leads_to(always(lift_state((|vd| current_state_matches(vd))(vd))))).satisfied_by(ex));
                assert(Cluster::eventually_stable_reconciliation(|vd| current_state_matches(vd)).satisfied_by(ex));
            }
            assert forall |ex: Execution<ClusterState>| 
                #[trigger] vd_eventually_stable_reconciliation().satisfied_by(ex)
                implies tla_forall(|vd: VDeploymentView| vd_eventually_stable_reconciliation_per_cr(vd)).satisfied_by(ex) by {
                assert(Cluster::eventually_stable_reconciliation(|vd| current_state_matches(vd)).satisfied_by(ex));
                assert(tla_forall(|vd: VDeploymentView| always(lift_state(Cluster::desired_state_is(vd))).leads_to(always(lift_state((|vd| current_state_matches(vd))(vd))))).satisfied_by(ex));
                assert((|vd: VDeploymentView| Cluster::eventually_stable_reconciliation_per_cr(vd, |vd| current_state_matches(vd))) 
                    =~= (|vd: VDeploymentView| always(lift_state(Cluster::desired_state_is(vd))).leads_to(always(lift_state((|vd| current_state_matches(vd))(vd))))));
                assert((|vd: VDeploymentView| vd_eventually_stable_reconciliation_per_cr(vd)) 
                    =~= (|vd: VDeploymentView| Cluster::eventually_stable_reconciliation_per_cr(vd, |vd| current_state_matches(vd))));
            }

            temp_pred_equality(
                tla_forall(|vd: VDeploymentView| vd_eventually_stable_reconciliation_per_cr(vd)),
                vd_eventually_stable_reconciliation()
            );
        }
    )
}

proof fn eventually_stable_reconciliation_holds_per_cr(spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        spec.entails(next_with_wf(cluster, controller_id)),
        // The vd type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vd controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        // No other controllers interfere with the vd controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures
        spec.entails(vd_eventually_stable_reconciliation_per_cr(vd)),
{
    // There are two specs we wish to deal with: one, `spec`, has `cluster.init()` true,
    // while the other spec, `stable_spec`, has it false.
    let stable_spec = stable_spec(cluster, controller_id);
    assumption_and_invariants_of_all_phases_is_stable(vd, cluster, controller_id);
    stable_spec_and_assumption_and_invariants_of_all_phases_is_stable(vd, cluster, controller_id);
    
    vd_rely_condition_equivalent_to_lifted_vd_rely_condition(
        stable_spec, cluster, controller_id
    );
    lemma_true_leads_to_always_current_state_matches(stable_spec, vd, cluster, controller_id);
    reveal_with_fuel(spec_before_phase_n, 7);

    spec_before_phase_n_entails_true_leads_to_current_state_matches(6, stable_spec, vd, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(5, stable_spec, vd, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(4, stable_spec, vd, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(3, stable_spec, vd, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(2, stable_spec, vd, cluster, controller_id);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(1, stable_spec, vd, cluster, controller_id);

    let assumption = always(lift_state(Cluster::desired_state_is(vd)));
    temp_pred_equality(
        stable_spec.and(spec_before_phase_n(1, vd, cluster, controller_id)),
        stable_spec.and(invariants(vd, cluster, controller_id))
            .and(assumption)
    );
    unpack_conditions_from_spec(stable_spec.and(invariants(vd, cluster, controller_id)), assumption, true_pred(), always(lift_state(current_state_matches(vd))));
    temp_pred_equality(true_pred().and(assumption), assumption);

    // Annoying non-automatic unpacking of the spec for one precondition.
    entails_trans(
        spec,
        next_with_wf(cluster, controller_id),
        always(lift_action(cluster.next()))
    );
    spec_entails_all_invariants(spec, vd, cluster, controller_id);
    simplify_predicate(spec, derived_invariants_since_beginning(vd, cluster, controller_id));

    spec_and_invariants_entails_stable_spec_and_invariants(spec, vd, cluster, controller_id);
    entails_trans(
        spec.and(derived_invariants_since_beginning(vd, cluster, controller_id)), 
        stable_spec.and(invariants(vd, cluster, controller_id)),
        always(lift_state(Cluster::desired_state_is(vd))).leads_to(always(lift_state(current_state_matches(vd))))
    );
}

proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(i: nat, spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int)
    requires
        1 <= i <= 6,
        valid(stable(spec.and(spec_before_phase_n(i, vd, cluster, controller_id)))),
        spec.and(spec_before_phase_n(i + 1, vd, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(current_state_matches(vd))))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures spec.and(spec_before_phase_n(i, vd, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(current_state_matches(vd))))),
{
    reveal_with_fuel(spec_before_phase_n, 7);
    temp_pred_equality(
        spec.and(spec_before_phase_n(i + 1, vd, cluster, controller_id)),
        spec.and(spec_before_phase_n(i, vd, cluster, controller_id))
            .and(invariants_since_phase_n(i, vd, cluster, controller_id))
    );
    spec_of_previous_phases_entails_eventually_new_invariants(spec, vd, cluster, controller_id, i);
    unpack_conditions_from_spec(spec.and(spec_before_phase_n(i, vd, cluster, controller_id)), invariants_since_phase_n(i, vd, cluster, controller_id), true_pred(), always(lift_state(current_state_matches(vd))));
    temp_pred_equality(
        true_pred().and(invariants_since_phase_n(i, vd, cluster, controller_id)),
        invariants_since_phase_n(i, vd, cluster, controller_id)
    );
    leads_to_trans(spec.and(spec_before_phase_n(i, vd, cluster, controller_id)), true_pred(), invariants_since_phase_n(i, vd, cluster, controller_id), always(lift_state(current_state_matches(vd))));
}

proof fn lemma_true_leads_to_always_current_state_matches(provided_spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int) 
    requires
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        provided_spec.entails(next_with_wf(cluster, controller_id)),
        // The vd type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vd controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        // No other controllers interfere with the vd controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> provided_spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures
        provided_spec.and(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(current_state_matches(vd))))),
{
    let spec = provided_spec.and(assumption_and_invariants_of_all_phases(vd, cluster, controller_id));
    // non-interference properties
    vd_rely_condition_equivalent_to_lifted_vd_rely_condition(provided_spec, cluster, controller_id);
    entails_trans(spec, provided_spec, always(lifted_vd_rely_condition(cluster, controller_id)));
    only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself_action(spec, cluster, controller_id);
    assert(spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))))) by {
        assume(false); // TODO
    }
    // true ~> reconcile_idle
    let reconcile_idle = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
    };
    assert(spec.entails(true_pred().leads_to(lift_state(reconcile_idle)))) by {
        always_tla_forall_apply(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())), vd);
        terminate::reconcile_eventually_terminates(spec, cluster, controller_id);
        use_tla_forall(spec, |key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))), vd.object_ref());
    }
    // reconcile_idle ~> reconcile_scheduled
    let reconcile_scheduled = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(vd.object_ref())
    };
    assert(spec.entails(lift_state(reconcile_idle).leads_to(lift_state(reconcile_scheduled)))) by {
        let input = vd.object_ref();
        let stronger_reconcile_idle = |s: ClusterState| {
            &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
            &&& !s.scheduled_reconciles(controller_id).contains_key(vd.object_ref())
        };
        let stronger_next = |s, s_prime| {
            &&& cluster.next()(s, s_prime)
            &&& Cluster::desired_state_is(vd)(s)
            &&& Cluster::desired_state_is(vd)(s_prime)
        };
        always_to_always_later(spec, lift_state(Cluster::desired_state_is(vd)));
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(Cluster::desired_state_is(vd)),
            later(lift_state(Cluster::desired_state_is(vd)))
        );
        cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(
            spec,
            controller_id,
            input,
            stronger_next,
            and!(stronger_reconcile_idle, Cluster::desired_state_is(vd)),
            reconcile_scheduled
        );
        temp_pred_equality(
            lift_state(stronger_reconcile_idle).and(lift_state(Cluster::desired_state_is(vd))),
            lift_state(and!(stronger_reconcile_idle, Cluster::desired_state_is(vd)))
        );
        leads_to_by_borrowing_inv(spec, lift_state(stronger_reconcile_idle), lift_state(reconcile_scheduled), lift_state(Cluster::desired_state_is(vd)));
        entails_implies_leads_to(spec, lift_state(reconcile_scheduled), lift_state(reconcile_scheduled));
        or_leads_to_combine(spec, lift_state(stronger_reconcile_idle), lift_state(reconcile_scheduled), lift_state(reconcile_scheduled));
        temp_pred_equality(lift_state(stronger_reconcile_idle).or(lift_state(reconcile_scheduled)), lift_state(reconcile_idle));
    }
    let init = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Init]),
        no_pending_req_in_cluster(vd, controller_id)
    );
    // reconcile_scheduled ~> init
    assert(spec.entails(lift_state(reconcile_scheduled).leads_to(lift_state(init)))) by {
        let input = (None, Some(vd.object_ref()));
        let stronger_next = |s, s_prime| {
            &&& cluster.next()(s, s_prime) 
            &&& Cluster::crash_disabled(controller_id)(s) 
            &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s) 
            &&& helper_invariants::cr_in_reconciles_has_the_same_spec_uid_name_and_namespace_as_vd(vd, controller_id)(s) 
            &&& Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)(s)
        };
        VDeploymentView::marshal_preserves_integrity();
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(Cluster::crash_disabled(controller_id)),
            lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
            lift_state(helper_invariants::cr_in_reconciles_has_the_same_spec_uid_name_and_namespace_as_vd(vd, controller_id)),
            lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id))
        );
        // TODO: fix
        assume(forall |s, s_prime| reconcile_scheduled(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) ==> init(s_prime));
        cluster.lemma_pre_leads_to_post_by_controller(
            spec,
            controller_id,
            input,
            stronger_next,
            ControllerStep::RunScheduledReconcile,
            reconcile_scheduled,
            init
        );
    }
    // init ~> done
    let done = and!(
        at_vd_step_with_vd(vd, controller_id, at_step![Done]),
        no_pending_req_in_cluster(vd, controller_id),
        current_state_matches(vd)
    );
    assert(spec.entails(lift_state(init).leads_to(lift_state(done)))) by {
        lemma_from_init_to_current_state_matches(vd, spec, cluster, controller_id);
    }
    // true ~> done
    leads_to_trans_n!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(reconcile_scheduled),
        lift_state(init),
        lift_state(done)
    );
    // true ~> []done
    assert(spec.entails(true_pred().leads_to(always(lift_state(done))))) by {
        lemma_current_state_matches_is_stable(spec, vd, true_pred(), cluster, controller_id);
    }
    // done |= ESR ==> []done |= []ESR ==> []done ~> []ESR
    entails_preserved_by_always(lift_state(done), lift_state(current_state_matches(vd)));
    entails_implies_leads_to(spec, always(lift_state(done)), always(lift_state(current_state_matches(vd))));
    leads_to_trans(spec, true_pred(), always(lift_state(done)), always(lift_state(current_state_matches(vd))));
}

}
