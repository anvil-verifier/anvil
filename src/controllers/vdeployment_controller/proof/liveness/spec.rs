#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::{
    spec::{
        api_server::{state_machine::*, types::*},
        cluster::*,
        controller::types::*,
        message::*,
        esr::*,
    },
    proof::{controller_runtime_liveness::*, network::*},
};

use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    trusted::{
        liveness_theorem::*, 
        rely_guarantee::*,
        spec_types::*, 
        step::*,
        step::VDeploymentReconcileStepView::*,
    },
    proof::{helper_invariants::*, helper_lemmas::*, liveness::*, predicate::*},
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::reconciler::spec::io::*;
use vstd::{map::*, map_lib::*, math::*, prelude::*};

verus! {

pub open spec fn assumption_and_invariants_of_all_phases(vd: VDeploymentView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    invariants(vd, cluster, controller_id)
    .and(always(lift_state(desired_state_is(vd))))
    .and(invariants_since_phase_i(controller_id, vd))
    .and(invariants_since_phase_ii(controller_id, vd))
    .and(invariants_since_phase_iii(vd, cluster, controller_id))
    .and(invariants_since_phase_iv(vd, cluster, controller_id))
    .and(invariants_since_phase_v(vd, cluster, controller_id))
    .and(invariants_since_phase_vi(vd, cluster, controller_id))
}

pub proof fn assumption_and_invariants_of_all_phases_is_stable(vd: VDeploymentView, cluster: Cluster, controller_id: int)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(vd, cluster, controller_id))),
        valid(stable(invariants(vd, cluster, controller_id))),
        forall |i: nat| 0 <= i <= 6 ==> valid(stable(#[trigger] spec_before_phase_n(i, vd, cluster, controller_id))),
{
    reveal_with_fuel(spec_before_phase_n, 6);
    invariants_is_stable(vd, cluster, controller_id);
    always_p_is_stable(lift_state(desired_state_is(vd)));
    invariants_since_phase_i_is_stable(controller_id, vd);
    invariants_since_phase_ii_is_stable(controller_id, vd);
    invariants_since_phase_iii_is_stable(vd, cluster, controller_id);
    invariants_since_phase_iv_is_stable(vd, cluster, controller_id);
    invariants_since_phase_v_is_stable(vd, cluster, controller_id);
    invariants_since_phase_vi_is_stable(vd, cluster, controller_id);
    stable_and_n!(
        invariants(vd, cluster, controller_id),
        always(lift_state(desired_state_is(vd))),
        invariants_since_phase_i(controller_id, vd),
        invariants_since_phase_ii(controller_id, vd),
        invariants_since_phase_iii(vd, cluster, controller_id),
        invariants_since_phase_iv(vd, cluster, controller_id),
        invariants_since_phase_v(vd, cluster, controller_id),
        invariants_since_phase_vi(vd, cluster, controller_id)
    );
}

pub proof fn stable_spec_and_assumption_and_invariants_of_all_phases_is_stable(vd: VDeploymentView, cluster: Cluster, controller_id: int)
    requires
        valid(stable(assumption_and_invariants_of_all_phases(vd, cluster, controller_id))),
        valid(stable(invariants(vd, cluster, controller_id))),
        forall |i: nat| 0 <= i <= 6 ==> valid(stable(#[trigger] spec_before_phase_n(i, vd, cluster, controller_id))),
    ensures
        valid(stable(stable_spec(cluster, controller_id))),
        valid(stable(stable_spec(cluster, controller_id).and(assumption_and_invariants_of_all_phases(vd, cluster, controller_id)))),
        valid(stable(stable_spec(cluster, controller_id).and(invariants(vd, cluster, controller_id)))),
        forall |i: nat| 0 <= i <= 6 ==> valid(stable(#[trigger] stable_spec(cluster, controller_id).and(spec_before_phase_n(i, vd, cluster, controller_id)))),
{
    stable_spec_is_stable(cluster, controller_id);
    stable_and_n!(
        stable_spec(cluster, controller_id),
        assumption_and_invariants_of_all_phases(vd, cluster, controller_id)
    );
    stable_and_n!(
        stable_spec(cluster, controller_id),
        invariants(vd, cluster, controller_id)
    );
    assert forall |i: nat| 
        0 <= i <= 6
        && valid(stable(stable_spec(cluster, controller_id)))
        && forall |i: nat| 0 <= i <= 6 ==> valid(stable(#[trigger] spec_before_phase_n(i, vd, cluster, controller_id)))
        implies valid(stable(#[trigger] stable_spec(cluster, controller_id).and(spec_before_phase_n(i, vd, cluster, controller_id)))) by {
        stable_and_n!(
            stable_spec(cluster, controller_id),
            spec_before_phase_n(i, vd, cluster, controller_id)
        );
    }
}

pub open spec fn invariants_since_phase_n(n: nat, vd: VDeploymentView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    if n == 0 {
        invariants(vd, cluster, controller_id)
        .and(always(lift_state(desired_state_is(vd))))
    } else if n == 1 {
        invariants_since_phase_i(controller_id, vd)
    } else if n == 2 {
        invariants_since_phase_ii(controller_id, vd)
    } else if n == 3 {
        invariants_since_phase_iii(vd, cluster, controller_id)
    } else if n == 4 {
        invariants_since_phase_iv(vd, cluster, controller_id)
    } else if n == 5 {
        invariants_since_phase_v(vd, cluster, controller_id)
    } else if n == 6 {
        invariants_since_phase_vi(vd, cluster, controller_id)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(n: nat, vd: VDeploymentView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
    decreases n,
{
    if n == 1 {
        invariants(vd, cluster, controller_id).and(always(lift_state(desired_state_is(vd))))
    } else if 2 <= n <= 7 {
        spec_before_phase_n((n-1) as nat, vd, cluster, controller_id).and(invariants_since_phase_n((n-1) as nat, vd, cluster, controller_id))
    } else {
        true_pred()
    }
}

pub open spec fn invariants_since_phase_i(controller_id: int, vd: VDeploymentView) -> TempPred<ClusterState> {
    always(lift_state(Cluster::crash_disabled(controller_id)))
    .and(always(lift_state(Cluster::req_drop_disabled())))
    .and(always(lift_state(Cluster::pod_monkey_disabled())))
}

pub proof fn invariants_since_phase_i_is_stable(controller_id: int, vd: VDeploymentView)
    ensures valid(stable(invariants_since_phase_i(controller_id, vd))),
{
    stable_and_always_n!(
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled())
    );
}

pub open spec fn invariants_since_phase_ii(controller_id: int, vd: VDeploymentView) -> TempPred<ClusterState>
{
    always(lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()))
    .and(always(lift_state(vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id))))
    .and(always(lift_state(cr_in_schedule_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id))))
    .and(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, vd.object_ref()))))
}

pub proof fn invariants_since_phase_ii_is_stable(controller_id: int, vd: VDeploymentView)
    ensures valid(stable(invariants_since_phase_ii(controller_id, vd))),
{
    stable_and_always_n!(
        lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()),
        lift_state(vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id)),
        lift_state(cr_in_schedule_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, vd.object_ref()))
    );
}

pub open spec fn invariants_since_phase_iii(vd: VDeploymentView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)))
    .and(always(lift_state(cr_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id))))
    .and(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vd.object_ref()))))
}

pub proof fn invariants_since_phase_iii_is_stable(vd: VDeploymentView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_iii(vd, cluster, controller_id))),
{
    stable_and_always_n!(
        lift_state(vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)),
        lift_state(cr_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vd.object_ref()))
    );

}

pub open spec fn invariants_since_phase_iv(vd: VDeploymentView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(no_pending_interfering_update_request(vd, controller_id)))
}

pub proof fn invariants_since_phase_iv_is_stable(vd: VDeploymentView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_iv(vd, cluster, controller_id))),
{
    always_p_is_stable(lift_state(no_pending_interfering_update_request(vd, controller_id)));
}

pub open spec fn invariants_since_phase_v(vd: VDeploymentView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(garbage_collector_does_not_delete_vd_vrs_objects(vd)))
}

pub proof fn invariants_since_phase_v_is_stable(vd: VDeploymentView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_v(vd, cluster, controller_id))),
{
    always_p_is_stable(lift_state(garbage_collector_does_not_delete_vd_vrs_objects(vd)));
}

pub open spec fn invariants_since_phase_vi(vd: VDeploymentView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id)))
}

pub proof fn invariants_since_phase_vi_is_stable(vd: VDeploymentView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_vi(vd, cluster, controller_id))),
{
    always_p_is_stable(lift_state(no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id)));
}

pub proof fn spec_of_previous_phases_entails_eventually_new_invariants(provided_spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int, i: nat)
    requires 
        1 <= i <= 6,
        // The vd type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        // The vd controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        // No other controllers interfere with the vd controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> provided_spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures provided_spec.and(spec_before_phase_n(i, vd, cluster, controller_id)).entails(true_pred().leads_to(invariants_since_phase_n(i, vd, cluster, controller_id))),
{
    let spec = provided_spec.and(spec_before_phase_n(i, vd, cluster, controller_id));
    // assert non-interference property on combined spec.
    assert forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id) 
        && provided_spec.entails(always(lift_state(#[trigger] vd_rely(other_id))))
        implies spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))) by {
        if cluster.controller_models.remove(controller_id).contains_key(other_id) {
            assert(provided_spec.entails(always(lift_state(vd_rely(other_id)))));
            entails_and_different_temp(
                provided_spec,
                spec_before_phase_n(i, vd, cluster, controller_id),
                always(lift_state(vd_rely(other_id))),
                true_pred()
            );
            assert(spec.entails(always(lift_state(vd_rely(other_id))).and(true_pred())));
            temp_pred_equality(
                always(lift_state(vd_rely(other_id))).and(true_pred()),
                always(lift_state(vd_rely(other_id)))
            );
        }
    }

    reveal_with_fuel(spec_before_phase_n, 6);
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
        terminate::reconcile_eventually_terminates(spec, cluster, controller_id);
        use_tla_forall(
            spec,
            |key: ObjectRef|
                true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key))),
            vd.object_ref()
        );

        if i == 2 {
            use_tla_forall(
                spec, 
                |input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input)),
                vd.object_ref()
            );
            always_tla_forall_apply(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())), vd);
            lemma_eventually_always_no_pending_mutation_request_not_from_controller_on_vrs_objects(spec, cluster, controller_id);
            lemma_always_eventually_cr_in_schedule_has_the_same_spec_uid_name_namespace_and_labels_as_vd(spec, vd, cluster, controller_id);
            lemma_eventually_always_vd_in_schedule_does_not_have_deletion_timestamp(spec, vd, cluster, controller_id);
            cluster.lemma_true_leads_to_always_pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(spec, controller_id, vd.object_ref());
            leads_to_always_combine_n!(
                spec,
                true_pred(),
                lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()),
                lift_state(vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id)),
                lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, vd.object_ref()))
            );
        } else if i == 3 {
            always_tla_forall_apply(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())), vd);
            always_tla_forall_apply(
                spec,
                |vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                    controller_id,
                    vd.object_ref(),
                    cluster.reconcile_model(controller_id).done
                )),
                vd
            );
            always_tla_forall_apply(
                spec,
                |vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                    controller_id,
                    vd.object_ref(),
                    cluster.reconcile_model(controller_id).error
                )),
                vd
            );
            lemma_eventually_always_vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(spec, vd, cluster, controller_id);
            lemma_eventually_always_cr_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(spec, vd, cluster, controller_id);
            cluster.lemma_true_leads_to_always_every_msg_from_key_is_pending_req_msg_of(spec, controller_id, vd.object_ref());
            leads_to_always_combine_n!(
                spec,
                true_pred(),
                lift_state(vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)),
                lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vd.object_ref()))
            );
        } else if i == 4 {
            lemma_eventually_always_no_pending_interfering_update_request(spec, vd, cluster, controller_id);
        } else if i == 5 {
            always_tla_forall_apply(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())), vd);
            lemma_eventually_always_garbage_collector_does_not_delete_vd_vrs_objects(spec, vd, cluster, controller_id);
        } else if i == 6 {
            always_tla_forall_apply(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())), vd);
            lemma_eventually_always_no_other_pending_request_interferes_with_vd_reconcile(spec, vd, cluster, controller_id);
        }
    }
}

pub open spec fn stable_spec(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    next_with_wf(cluster, controller_id)
    .and(always(lifted_vd_rely_condition(cluster, controller_id)))
}

pub proof fn stable_spec_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(stable_spec(cluster, controller_id))),
{
    next_with_wf_is_stable(cluster, controller_id);
    always_p_is_stable(lifted_vd_rely_condition(cluster, controller_id));
    stable_and_n!(
        next_with_wf(cluster, controller_id),
        always(lifted_vd_rely_condition(cluster, controller_id))
    );
}

pub proof fn spec_and_invariants_entails_stable_spec_and_invariants(spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(next_with_wf(cluster, controller_id)),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures 
        spec.and(derived_invariants_since_beginning(vd, cluster, controller_id))
            .entails(stable_spec(cluster, controller_id).and(invariants(vd, cluster, controller_id))),
{
    let pre = spec.and(derived_invariants_since_beginning(vd, cluster, controller_id));

    // Proof of stable_spec
    vd_rely_condition_equivalent_to_lifted_vd_rely_condition(
        spec,
        cluster,
        controller_id
    );
    entails_and_n!(
        spec,
        next_with_wf(cluster, controller_id),
        always(lifted_vd_rely_condition(cluster, controller_id))
    );
    
    entails_and_different_temp(
        spec,
        derived_invariants_since_beginning(vd, cluster, controller_id),
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
        derived_invariants_since_beginning(vd, cluster, controller_id),
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
        derived_invariants_since_beginning(vd, cluster, controller_id)
    );
    
    entails_and_n!(
        pre,
        stable_spec(cluster, controller_id),
        invariants(vd, cluster, controller_id)
    );
}

pub open spec fn next_with_wf(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    always(lift_action(cluster.next()))
    .and(tla_forall(|input| cluster.api_server_next().weak_fairness(input)))
    .and(tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)))
    .and(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))))
    .and(tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))))
    .and(tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))))
    .and(cluster.disable_crash().weak_fairness(controller_id))
    .and(cluster.disable_req_drop().weak_fairness(()))
    .and(cluster.disable_pod_monkey().weak_fairness(()))
}

pub proof fn next_with_wf_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(next_with_wf(cluster, controller_id))),
{
    always_p_is_stable(lift_action(cluster.next()));
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.api_server_next());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.builtin_controllers_next());
    cluster.tla_forall_controller_next_weak_fairness_is_stable(controller_id);
    cluster.tla_forall_schedule_controller_reconcile_weak_fairness_is_stable(controller_id);
    cluster.tla_forall_external_next_weak_fairness_is_stable(controller_id);
    assert(valid(stable(cluster.disable_crash().weak_fairness(controller_id)))) by {
        let split_always = always(lift_state(cluster.disable_crash().pre(controller_id))).implies(eventually(lift_action(cluster.disable_crash().forward(controller_id))));
        always_p_is_stable::<ClusterState>(split_always);
    }
    Cluster::action_weak_fairness_is_stable(cluster.disable_req_drop());
    Cluster::action_weak_fairness_is_stable(cluster.disable_pod_monkey());
    stable_and_n!(
        always(lift_action(cluster.next())),
        tla_forall(|input| cluster.api_server_next().weak_fairness(input)),
        tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)),
        tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))),
        tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))),
        tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))),
        cluster.disable_crash().weak_fairness(controller_id),
        cluster.disable_req_drop().weak_fairness(()),
        cluster.disable_pod_monkey().weak_fairness(())
    );
}

// This predicate combines all the possible actions (next), weak fairness and invariants that hold throughout the execution.
// We name it invariants here because these predicates are never violated, thus they can all be seen as some kind of invariants.
//
// The final goal of our proof is to show init /\ invariants |= []desired_state_is(vd) ~> []current_state_matches(vd).
// init /\ invariants is equivalent to init /\ next /\ weak_fairness, so we get cluster_spec() |= []desired_state_is(vd) ~> []current_state_matches(vd).
pub open spec fn invariants(vd: VDeploymentView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    next_with_wf(cluster, controller_id).and(derived_invariants_since_beginning(vd, cluster, controller_id))
}

pub proof fn invariants_is_stable(vd: VDeploymentView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants(vd, cluster, controller_id))),
{
    next_with_wf_is_stable(cluster, controller_id);
    derived_invariants_since_beginning_is_stable(vd, cluster, controller_id);
    stable_and_n!(
        next_with_wf(cluster, controller_id),
        derived_invariants_since_beginning(vd, cluster, controller_id)
    );
}

pub open spec fn derived_invariants_since_beginning(vd: VDeploymentView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    .and(always(lift_state(Cluster::etcd_objects_have_unique_uids())))
    .and(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>())))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id))))
    .and(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())))
    .and(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())))
    .and(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id))))
    .and(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
    .and(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id))))
    .and(always(lift_state(Cluster::etcd_is_finite())))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())))))
    .and(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
    .and(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))))
    .and(always(lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![Init])))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterEnsureNewVRS])))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).done)))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).error)))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterListVRS])))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterCreateNewVRS])))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleNewVRS])))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleDownOldVRS])))))
    .and(always(tla_forall(|vd: VDeploymentView| lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd)))))
    .and(always(lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id))))
    .and(always(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id))))
}

pub proof fn derived_invariants_since_beginning_is_stable(vd: VDeploymentView, cluster: Cluster, controller_id: int)
    ensures valid(stable(derived_invariants_since_beginning(vd, cluster, controller_id))),
{
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_unique_id()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_p_is_stable(lift_state(Cluster::etcd_objects_have_unique_uids()));
    always_p_is_stable(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()));
    always_p_is_stable(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)));
    always_p_is_stable(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()));
    always_p_is_stable(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)));
    always_p_is_stable(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)));
    always_p_is_stable(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id)));
    always_p_is_stable(lift_state(Cluster::etcd_is_finite()));
    always_p_is_stable(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref()))));
    always_p_is_stable(lift_state(Cluster::there_is_the_controller_state(controller_id)));
    always_p_is_stable(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)));
    always_p_is_stable(lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)));
    always_p_is_stable(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![Init]))));
    always_p_is_stable(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterEnsureNewVRS]))));
    always_p_is_stable(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).done))));
    always_p_is_stable(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).error))));
    always_p_is_stable(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterListVRS]))));
    always_p_is_stable(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterCreateNewVRS]))));
    always_p_is_stable(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleNewVRS]))));
    always_p_is_stable(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleDownOldVRS]))));
    always_p_is_stable(tla_forall(|vd: VDeploymentView| lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd))));
    always_p_is_stable(lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)));
    always_p_is_stable(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)));
    stable_and_n!(
        always(lift_state(Cluster::every_in_flight_msg_has_unique_id())),
        always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())),
        always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))),
        always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        always(lift_state(Cluster::etcd_objects_have_unique_uids())),
        always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())),
        always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>())),
        always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id))),
        always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())),
        always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())),
        always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())),
        always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id))),
        always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))),
        always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))),
        always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))),
        always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))),
        always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id))),
        always(lift_state(Cluster::etcd_is_finite())),
        always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())))),
        always(lift_state(Cluster::there_is_the_controller_state(controller_id))),
        always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))),
        always(lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id))),
        always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![Init])))),
        always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterEnsureNewVRS])))),
        always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).done)))),
        always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).error)))),
        always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterListVRS])))),
        always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterCreateNewVRS])))),
        always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleNewVRS])))),
        always(tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleDownOldVRS])))),
        always(tla_forall(|vd: VDeploymentView| lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd)))),
        always(lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id))),
        always(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)))
    );
}

pub proof fn spec_entails_all_invariants(spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    ensures spec.entails(derived_invariants_since_beginning(vd, cluster, controller_id)),
{
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_etcd_objects_have_unique_uids(spec);
    cluster.lemma_always_each_builtin_object_in_etcd_is_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VDeploymentView>(spec);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_no_replicas_and_has_unique_id(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(spec, controller_id);
    cluster.lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_every_ongoing_reconcile_has_lower_id_than_allocator(spec, controller_id);
    cluster.lemma_always_ongoing_reconciles_is_finite(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(spec, controller_id);
    cluster.lemma_always_etcd_is_finite(spec);

    assert forall |vd: VDeploymentView| spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, #[trigger] vd.object_ref())))) by {
        cluster.lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, controller_id, vd.object_ref());
    }
    spec_entails_always_tla_forall(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())));

    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    lemma_always_there_is_no_request_msg_to_external_from_controller(spec, cluster, controller_id);
    cluster.lemma_always_cr_states_are_unmarshallable::<VDeploymentReconciler, VDeploymentReconcileState, VDeploymentView, VoidEReqView, VoidERespView>(spec, controller_id);
    VDeploymentReconcileState::marshal_preserves_integrity();

    assert forall |vd: VDeploymentView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vd.object_ref(), at_step_or![Init])))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vd.object_ref(), at_step_or![Init]);
    }
    spec_entails_always_tla_forall(spec, |vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![Init])));

    assert forall |vd: VDeploymentView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vd.object_ref(), at_step_or![AfterEnsureNewVRS])))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vd.object_ref(), at_step_or![AfterEnsureNewVRS]);
    }
    spec_entails_always_tla_forall(spec, |vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterEnsureNewVRS])));

    assert forall |vd: VDeploymentView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vd.object_ref(), cluster.reconcile_model(controller_id).done)))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).done);
    }
    spec_entails_always_tla_forall(spec, |vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).done)));

    assert forall |vd: VDeploymentView| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] vd.object_ref(), cluster.reconcile_model(controller_id).error)))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).error);
    }
    spec_entails_always_tla_forall(spec, |vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).error)));

    assert forall |vd: VDeploymentView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vd.object_ref(), at_step_or![AfterListVRS])))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vd.object_ref(), at_step_or![AfterListVRS]);
    }
    spec_entails_always_tla_forall(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterListVRS])));

    assert forall |vd: VDeploymentView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vd.object_ref(), at_step_or![AfterCreateNewVRS])))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vd.object_ref(), at_step_or![AfterCreateNewVRS]);
    }
    spec_entails_always_tla_forall(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterCreateNewVRS])));

    assert forall |vd: VDeploymentView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vd.object_ref(), at_step_or![AfterScaleNewVRS])))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vd.object_ref(), at_step_or![AfterScaleNewVRS]);
    }
    spec_entails_always_tla_forall(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleNewVRS])));

    assert forall |vd: VDeploymentView| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] vd.object_ref(), at_step_or![AfterScaleDownOldVRS])))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, vd.object_ref(), at_step_or![AfterScaleDownOldVRS]);
    }
    spec_entails_always_tla_forall(spec, |vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleDownOldVRS])));

    assert forall |vd: VDeploymentView| spec.entails(always(lift_state(#[trigger] vd_reconcile_request_only_interferes_with_itself(controller_id, vd)))) by {
        lemma_always_vd_reconcile_request_only_interferes_with_itself(
            spec, cluster, controller_id, vd
        );
    }
    spec_entails_always_tla_forall(
        spec, |vd: VDeploymentView| lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd))
    );
    lemma_always_vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(spec, cluster, controller_id);
    lemma_always_every_msg_from_vd_controller_carries_vd_key(spec, cluster, controller_id);

    entails_always_and_n!(
        spec,
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::etcd_objects_have_unique_uids()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id)),
        lift_state(Cluster::etcd_is_finite()),
        tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref()))),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)),
        tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![Init]))),
        tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterEnsureNewVRS]))),
        tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).done))),
        tla_forall(|vd: VDeploymentView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), cluster.reconcile_model(controller_id).error))),
        tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterListVRS]))),
        tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterCreateNewVRS]))),
        tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleNewVRS]))),
        tla_forall(|vd: VDeploymentView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step_or![AfterScaleDownOldVRS]))),
        tla_forall(|vd: VDeploymentView| lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd))),
        lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)),
        lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id))
    );
}
}