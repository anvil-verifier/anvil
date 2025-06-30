use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_lemmas::*, liveness::{spec::*, terminate}, predicate::*},
    trusted::{
        liveness_theorem::*, 
        rely_guarantee::*,
        spec_types::*, 
        step::*
    },
};
use vstd::prelude::*;

verus! {

proof fn eventually_stable_reconciliation_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        spec.entails(next_with_wf(cluster, controller_id)),
        // The vd type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
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
    reveal_with_fuel(spec_before_phase_n, 6);

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
        1 <= i <= 5,
        valid(stable(spec.and(spec_before_phase_n(i, vd, cluster, controller_id)))),
        spec.and(spec_before_phase_n(i + 1, vd, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(current_state_matches(vd))))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures spec.and(spec_before_phase_n(i, vd, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(current_state_matches(vd))))),
{
    reveal_with_fuel(spec_before_phase_n, 6);
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

// TODO: write in proof details.
#[verifier(external_body)]
proof fn lemma_true_leads_to_always_current_state_matches(provided_spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int) 
    requires
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        provided_spec.entails(next_with_wf(cluster, controller_id)),
        // The vd type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        // The vd controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        // No other controllers interfere with the vd controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> provided_spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures
        provided_spec.and(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)).entails(true_pred().leads_to(always(lift_state(current_state_matches(vd))))),
{}

}
