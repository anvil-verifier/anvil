use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*},
    proof::{liveness::spec::*},
    trusted::{liveness_theorem::*, spec_types::*},
};
use vstd::prelude::*;

verus! {

proof fn eventually_stable_reconciliation_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vrs controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        // The fairness condition of the controller.
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        // The fairness condition of the API server.
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        // The fairness condition of the built-in controllers.
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        // The fairness condition of scheduling controller reconcile.
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        // No other controllers interfere with the vrs controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
    ensures
        spec.entails(vrs_eventually_stable_reconciliation()),
{
    assert forall |vrs: VReplicaSetView| #[trigger] spec.entails(vrs_eventually_stable_reconciliation_per_cr(vrs)) by {
        eventually_stable_reconciliation_holds_per_cr(vrs, spec, cluster, controller_id);
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

proof fn eventually_stable_reconciliation_holds_per_cr(vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vrs controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        // The fairness condition of the controller.
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        // The fairness condition of the API server.
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        // The fairness condition of the built-in controllers.
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        // The fairness condition of scheduling controller reconcile.
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        // No other controllers interfere with the vrs controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
    ensures
        spec.entails(vrs_eventually_stable_reconciliation_per_cr(vrs)),
{
    assumption_and_invariants_of_all_phases_is_stable(vrs, cluster, controller_id);
    lemma_true_leads_to_always_current_state_matches(vrs, spec, cluster, controller_id);
    reveal_with_fuel(spec_before_phase_n, 8);
    // spec_before_phase_n_entails_true_leads_to_current_state_matches(5, vrs, cluster, controller_id);
    // spec_before_phase_n_entails_true_leads_to_current_state_matches(4, vrs, cluster, controller_id);
    // spec_before_phase_n_entails_true_leads_to_current_state_matches(3, vrs, cluster, controller_id);
    // spec_before_phase_n_entails_true_leads_to_current_state_matches(2, vrs, cluster, controller_id);
    // spec_before_phase_n_entails_true_leads_to_current_state_matches(1, vrs, cluster, controller_id);

    assume(false);
}

#[verifier(external_body)]
proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(i: nat, vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    requires
        1 <= i <= 5,
        valid(stable(spec_before_phase_n(i, vrs, cluster, controller_id))),
        spec_before_phase_n(i + 1, vrs, cluster, controller_id).entails(true_pred().leads_to(always(lift_state(current_state_matches(vrs)))))
    ensures spec_before_phase_n(i, vrs, cluster, controller_id).entails(true_pred().leads_to(always(lift_state(current_state_matches(vrs))))),
{
}

#[verifier(external_body)]
proof fn lemma_true_leads_to_always_current_state_matches(vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int) 
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vrs controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        // The fairness condition of the controller.
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        // The fairness condition of the API server.
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        // The fairness condition of the built-in controllers.
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        // The fairness condition of scheduling controller reconcile.
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        // No other controllers interfere with the vrs controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
    ensures
        assumption_and_invariants_of_all_phases(vrs, cluster, controller_id).entails(always(lift_state(current_state_matches(vrs)))),
{

}

}
