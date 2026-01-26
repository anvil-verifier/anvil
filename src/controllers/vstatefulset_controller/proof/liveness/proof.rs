#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::{
    spec::{api_server::{state_machine::*, types::*}, cluster::*, controller::types::*, message::*, esr::*,},
    proof::{controller_runtime_liveness::*, network::*},
};

use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, rely::*, spec_types::*, step::*, step::VStatefulSetReconcileStepView::*},
    proof::{predicate::*, helper_invariants, helper_lemmas::*, guarantee, liveness::{spec::*, terminate}},
};
use crate::reconciler::spec::io::*;
use vstd::{map::*, map_lib::*, math::*, prelude::*};

verus! {

pub proof fn spec_entails_always_cluster_invariants_since_reconciliation_holds_pre_cr(spec: TempPred<ClusterState>, vsts: VStatefulSetView, controller_id: int, cluster: Cluster)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        spec.entails(next_with_wf(cluster, controller_id)),
        // The vsts type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        // The vsts controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
        // No other controllers interfere with the vsts controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vsts_rely(other_id, cluster.installed_types)))),
    ensures
        spec.entails(always(lift_state(Cluster::desired_state_is(vsts))).leads_to(always(lift_state(vsts_cluster_invariants(vsts, cluster, controller_id))))),
{
    spec_entails_always_desired_state_is_leads_to_assumption_and_invariants_of_all_phases(spec, vsts, cluster, controller_id);
    
    vsts_rely_condition_equivalent_to_lifted_vsts_rely_condition(spec, cluster, controller_id);
    
    assert(spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))));

    always_tla_forall_apply(
        assumption_and_invariants_of_all_phases(vsts, cluster, controller_id),
        |vsts: VStatefulSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())),
        vsts
    );
    
    // First prove leads_to for vsts_cluster_invariants_without_rely
    combine_spec_entails_always_n!(
        assumption_and_invariants_of_all_phases(vsts, cluster, controller_id),
        lift_state(vsts_cluster_invariants_without_rely(vsts, cluster, controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::etcd_objects_have_unique_uids()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VStatefulSetView>(controller_id)),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())),
        lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)),
        lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()),
        lift_state(Cluster::desired_state_is(vsts)),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref())),
        lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id))
    );

    entails_implies_leads_to(
        spec,
        assumption_and_invariants_of_all_phases(vsts, cluster, controller_id),
        always(lift_state(vsts_cluster_invariants_without_rely(vsts, cluster, controller_id)))
    );

    leads_to_trans(
        spec,
        always(lift_state(Cluster::desired_state_is(vsts))),
        assumption_and_invariants_of_all_phases(vsts, cluster, controller_id),
        always(lift_state(vsts_cluster_invariants_without_rely(vsts, cluster, controller_id)))
    );

    let p = always(lift_state(Cluster::desired_state_is(vsts)));
    let q_without_rely = lift_state(vsts_cluster_invariants_without_rely(vsts, cluster, controller_id));
    let q_rely = lift_state(vsts_rely_conditions(cluster, controller_id));
    let q_full = lift_state(vsts_cluster_invariants(vsts, cluster, controller_id));

    leads_to_always_enhance(
        spec,
        q_rely,
        p,
        q_without_rely,
        q_full
    );
}

pub proof fn spec_entails_always_desired_state_is_leads_to_assumption_and_invariants_of_all_phases(spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(next_with_wf(cluster, controller_id)),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vsts_rely(other_id, cluster.installed_types)))),
    ensures
        spec.entails(always(lift_state(Cluster::desired_state_is(vsts))).leads_to(assumption_and_invariants_of_all_phases(vsts, cluster, controller_id))),
{
    assumption_and_invariants_of_all_phases_is_stable(vsts, cluster, controller_id);
    stable_spec_is_stable(cluster, controller_id);
    let stable_spec = stable_spec(cluster, controller_id);

    assert(stable_spec.and(invariants(vsts, cluster, controller_id)).entails(
        always(lift_state(Cluster::desired_state_is(vsts))).leads_to(assumption_and_invariants_of_all_phases(vsts, cluster, controller_id)))) by {
        assert(stable_spec.and(invariants(vsts, cluster, controller_id)).and(always(lift_state(Cluster::desired_state_is(vsts)))).entails(true_pred()
            .leads_to(assumption_and_invariants_of_all_phases(vsts, cluster, controller_id)))) by {
            // Show that spec_before_phase_n(4) entails assumption_and_invariants_of_all_phases
            assert(spec_before_phase_n(4, vsts, cluster, controller_id).entails(
                assumption_and_invariants_of_all_phases(vsts, cluster, controller_id))) by {
                reveal_with_fuel(spec_before_phase_n, 4);
                combine_spec_entails_n!(
                    spec_before_phase_n(4, vsts, cluster, controller_id),
                    assumption_and_invariants_of_all_phases(vsts, cluster, controller_id),
                    invariants(vsts, cluster, controller_id),
                    always(lift_state(Cluster::desired_state_is(vsts))),
                    invariants_since_phase_i(controller_id, vsts),
                    invariants_since_phase_ii(controller_id, vsts),
                    invariants_since_phase_iii(vsts, cluster, controller_id)
                );
            }

            // Show that stable_spec.and(spec_before_phase_n(4)) entails true_pred() ~> assumption_and_invariants_of_all_phases
            assert(stable_spec.and(spec_before_phase_n(4, vsts, cluster, controller_id)).entails(
                true_pred().leads_to(assumption_and_invariants_of_all_phases(vsts, cluster, controller_id)))) by {
                assert(stable_spec.and(always(spec_before_phase_n(4, vsts, cluster, controller_id))).entails(
                    true_pred().leads_to(assumption_and_invariants_of_all_phases(vsts, cluster, controller_id)))) by {
                    entails_implies_leads_to(
                        stable_spec,
                        spec_before_phase_n(4, vsts, cluster, controller_id),
                        assumption_and_invariants_of_all_phases(vsts, cluster, controller_id)
                    );
                    temp_pred_equality(
                        true_pred().and(spec_before_phase_n(4, vsts, cluster, controller_id)),
                        spec_before_phase_n(4, vsts, cluster, controller_id)
                    );
                    pack_conditions_to_spec(
                        stable_spec,
                        spec_before_phase_n(4, vsts, cluster, controller_id),
                        true_pred(),
                        assumption_and_invariants_of_all_phases(vsts, cluster, controller_id)
                    );
                }
                assert(always(spec_before_phase_n(4, vsts, cluster, controller_id)) == spec_before_phase_n(4, vsts, cluster, controller_id)) by {
                    assert(valid(stable(spec_before_phase_n(4, vsts, cluster, controller_id)))) by {
                        invariants_since_phase_iii_is_stable(vsts, cluster, controller_id);
                        stable_and_temp(
                            spec_before_phase_n(3, vsts, cluster, controller_id),
                            invariants_since_phase_n(3, vsts, cluster, controller_id)
                        );
                        temp_pred_equality(
                            spec_before_phase_n(3, vsts, cluster, controller_id).and(invariants_since_phase_n(3, vsts, cluster, controller_id)),
                            spec_before_phase_n(4, vsts, cluster, controller_id)
                        );
                    };
                    stable_to_always(spec_before_phase_n(4, vsts, cluster, controller_id));
                }
            };

            // Now chain through all the phases
            spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(3, stable_spec, vsts, cluster, controller_id);
            spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(2, stable_spec, vsts, cluster, controller_id);
            spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(1, stable_spec, vsts, cluster, controller_id);

            temp_pred_equality(
                stable_spec.and(invariants(vsts, cluster, controller_id)).and(always(lift_state(Cluster::desired_state_is(vsts)))),
                stable_spec.and(spec_before_phase_n(1, vsts, cluster, controller_id))
            );
        }
        stable_and_temp(
            stable_spec,
            invariants(vsts, cluster, controller_id)
        );
        unpack_conditions_from_spec(
            stable_spec.and(invariants(vsts, cluster, controller_id)),
            always(lift_state(Cluster::desired_state_is(vsts))),
            true_pred(),
            assumption_and_invariants_of_all_phases(vsts, cluster, controller_id)
        );
        temp_pred_equality(
            true_pred().and(always(lift_state(Cluster::desired_state_is(vsts)))),
            always(lift_state(Cluster::desired_state_is(vsts)))
        );
    }

    spec_and_invariants_entails_stable_spec_and_invariants(spec, vsts, cluster, controller_id);
    entails_trans(
        spec.and(derived_invariants_since_beginning(vsts, cluster, controller_id)),
        stable_spec.and(invariants(vsts, cluster, controller_id)),
        always(lift_state(Cluster::desired_state_is(vsts))).leads_to(assumption_and_invariants_of_all_phases(vsts, cluster, controller_id))
    );
    entails_trans(
        spec,
        next_with_wf(cluster, controller_id),
        always(lift_action(cluster.next()))
    );
    spec_entails_all_invariants(spec, vsts, cluster, controller_id);
    simplify_predicate(spec, derived_invariants_since_beginning(vsts, cluster, controller_id));
}

proof fn spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(i: nat, spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    requires
        1 <= i <= 3,
        valid(stable(spec)),
        valid(stable(spec_before_phase_n(i, vsts, cluster, controller_id))),
        spec.and(spec_before_phase_n(i + 1, vsts, cluster, controller_id)).entails(true_pred().leads_to(assumption_and_invariants_of_all_phases(vsts, cluster, controller_id))),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    ensures
        spec.and(spec_before_phase_n(i, vsts, cluster, controller_id)).entails(true_pred().leads_to(assumption_and_invariants_of_all_phases(vsts, cluster, controller_id))),
{
    stable_and_temp(spec, spec_before_phase_n(i, vsts, cluster, controller_id));
    reveal_with_fuel(spec_before_phase_n, 4);
    temp_pred_equality(
        spec.and(spec_before_phase_n(i + 1, vsts, cluster, controller_id)),
        spec.and(spec_before_phase_n(i, vsts, cluster, controller_id))
            .and(invariants_since_phase_n(i, vsts, cluster, controller_id))
    );
    spec_of_previous_phases_entails_eventually_new_invariants(spec, vsts, cluster, controller_id, i);
    unpack_conditions_from_spec(
        spec.and(spec_before_phase_n(i, vsts, cluster, controller_id)),
        invariants_since_phase_n(i, vsts, cluster, controller_id),
        true_pred(),
        assumption_and_invariants_of_all_phases(vsts, cluster, controller_id)
    );
    temp_pred_equality(
        true_pred().and(invariants_since_phase_n(i, vsts, cluster, controller_id)),
        invariants_since_phase_n(i, vsts, cluster, controller_id)
    );
    leads_to_trans(
        spec.and(spec_before_phase_n(i, vsts, cluster, controller_id)),
        true_pred(),
        invariants_since_phase_n(i, vsts, cluster, controller_id),
        assumption_and_invariants_of_all_phases(vsts, cluster, controller_id)
    );
}

pub proof fn spec_of_previous_phases_entails_eventually_new_invariants(provided_spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, i: nat)
    requires
        1 <= i <= 3,
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    ensures
        provided_spec.and(spec_before_phase_n(i, vsts, cluster, controller_id)).entails(true_pred().leads_to(invariants_since_phase_n(i, vsts, cluster, controller_id))),
{
    let spec = provided_spec.and(spec_before_phase_n(i, vsts, cluster, controller_id));

    reveal_with_fuel(spec_before_phase_n, 4);
    if i == 1 {
        cluster.lemma_true_leads_to_crash_always_disabled(spec, controller_id);
        cluster.lemma_true_leads_to_req_drop_always_disabled(spec);
        cluster.lemma_true_leads_to_pod_monkey_always_disabled(spec);
        leads_to_always_combine_n!(
            spec,
            true_pred(),
            lift_state(Cluster::crash_disabled(controller_id)),
            lift_state(Cluster::req_drop_disabled()),
            lift_state(Cluster::pod_monkey_disabled())
        );
    } else {
        reconcile_eventually_terminates(spec, cluster, controller_id);
        use_tla_forall(
            spec,
            |key: ObjectRef|
                true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))),
            vsts.object_ref()
        );

        if i == 2 {
            always_tla_forall_apply(spec, |vsts: VStatefulSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())), vsts);
            cluster.lemma_true_leads_to_always_no_pending_request_to_api_server_from_non_controllers(spec);
            cluster.lemma_true_leads_to_always_pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(spec, controller_id, vsts.object_ref());
            leads_to_always_combine_n!(
                spec,
                true_pred(),
                lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()),
                lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, vsts.object_ref()))
            );
        } else if i == 3 {
            always_tla_forall_apply(spec, |vsts: VStatefulSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())), vsts);
            always_tla_forall_apply(
                spec,
                |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                    controller_id,
                    vsts.object_ref(),
                    cluster.reconcile_model(controller_id).done
                )),
                vsts
            );
            always_tla_forall_apply(
                spec,
                |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                    controller_id,
                    vsts.object_ref(),
                    cluster.reconcile_model(controller_id).error
                )),
                vsts
            );
            cluster.lemma_true_leads_to_always_every_msg_from_key_is_pending_req_msg_of(spec, controller_id, vsts.object_ref());
        }
    }
}

pub proof fn spec_and_invariants_entails_stable_spec_and_invariants(spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(next_with_wf(cluster, controller_id)),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vsts_rely(other_id, cluster.installed_types)))),
    ensures
        spec.and(derived_invariants_since_beginning(vsts, cluster, controller_id))
            .entails(stable_spec(cluster, controller_id).and(invariants(vsts, cluster, controller_id))),
{
    let pre = spec.and(derived_invariants_since_beginning(vsts, cluster, controller_id));

    entails_and_different_temp(
        spec,
        derived_invariants_since_beginning(vsts, cluster, controller_id),
        stable_spec(cluster, controller_id),
        true_pred()
    );
    temp_pred_equality(
        stable_spec(cluster, controller_id).and(true_pred()),
        stable_spec(cluster, controller_id)
    );

    // Proof of invariants
    entails_and_different_temp(
        spec,
        derived_invariants_since_beginning(vsts, cluster, controller_id),
        next_with_wf(cluster, controller_id),
        true_pred()
    );
    temp_pred_equality(
        next_with_wf(cluster, controller_id).and(true_pred()),
        next_with_wf(cluster, controller_id)
    );
    entails_and_n!(
        pre,
        next_with_wf(cluster, controller_id),
        derived_invariants_since_beginning(vsts, cluster, controller_id)
    );

    entails_and_n!(
        pre,
        stable_spec(cluster, controller_id),
        invariants(vsts, cluster, controller_id)
    );
}

#[verifier(external_body)]
pub proof fn spec_entails_pending_request_invariants(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    ensures
        // no_pending_req_msg_at_reconcile_state invariants
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated]))))),
        // pending_req_in_flight_or_resp_in_flight_at_reconcile_state invariants
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned]))))),
        spec.entails(always(tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated]))))),
{

    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    helper_invariants::lemma_always_there_is_no_request_msg_to_external_from_controller(spec, cluster, controller_id);
    cluster.lemma_always_cr_states_are_unmarshallable::<VStatefulSetReconciler, VStatefulSetReconcileState, VStatefulSetView, VoidEReqView, VoidERespView>(spec, controller_id);
    VStatefulSetReconcileState::marshal_preserves_integrity();
    
    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![Init])))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![Init]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), cluster.reconcile_model(controller_id).done)))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done)));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), cluster.reconcile_model(controller_id).error)))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error)));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![GetPVC])))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![GetPVC]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![CreatePVC])))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![CreatePVC]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![SkipPVC])))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![SkipPVC]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![CreateNeeded])))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![CreateNeeded]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![UpdateNeeded])))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![UpdateNeeded]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![DeleteCondemned])))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![DeleteCondemned]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![DeleteOutdated])))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![DeleteOutdated]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![AfterListPod])))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![AfterListPod]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![AfterGetPVC])))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![AfterGetPVC]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![AfterCreatePVC])))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![AfterCreateNeeded])))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![AfterUpdateNeeded])))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![AfterDeleteCondemned])))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned])));

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vsts.object_ref(), at_step_or![AfterDeleteOutdated])))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated]);
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated])));
}

pub proof fn spec_entails_all_invariants(spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    ensures
        spec.entails(derived_invariants_since_beginning(vsts, cluster, controller_id)),
{
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_etcd_objects_have_unique_uids(spec);
    cluster.lemma_always_each_builtin_object_in_etcd_is_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>(spec);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(spec, controller_id);
    cluster.lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_every_ongoing_reconcile_has_lower_id_than_allocator(spec, controller_id);
    cluster.lemma_always_ongoing_reconciles_is_finite(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_have_correct_kind::<VStatefulSetView>(spec, controller_id);
    cluster.lemma_always_etcd_is_finite(spec);

    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, #[trigger] vsts.object_ref())))) by {
        cluster.lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, controller_id, vsts.object_ref());
    }
    spec_entails_always_tla_forall_equality(spec, |vsts: VStatefulSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())));

    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    helper_invariants::lemma_always_there_is_no_request_msg_to_external_from_controller(spec, cluster, controller_id);
    cluster.lemma_always_cr_states_are_unmarshallable::<VStatefulSetReconciler, VStatefulSetReconcileState, VStatefulSetView, VoidEReqView, VoidERespView>(spec, controller_id);
    VStatefulSetReconcileState::marshal_preserves_integrity();

    // Call the separated pending request invariants proof
    spec_entails_pending_request_invariants(spec, cluster, controller_id);

    // Prove every_in_flight_msg_has_no_replicas_and_has_unique_id
    cluster.lemma_always_every_in_flight_msg_has_no_replicas_and_has_unique_id(spec);

    guarantee::internal_guarantee_condition_holds_on_all_vsts(spec, cluster, controller_id);

    entails_always_and_n!(
        spec,
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::etcd_objects_have_unique_uids()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VStatefulSetView>(controller_id)),
        lift_state(Cluster::etcd_is_finite()),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref()))),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).done))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), cluster.reconcile_model(controller_id).error))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned]))),
        tla_forall(|vsts: VStatefulSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated]))),
        lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id))
    );
}

}
