// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    model::reconciler::*,
    proof::{helper_invariants, liveness::terminate, predicate::*, resource::*, guarantee},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub open spec fn assumption_and_invariants_of_all_phases(controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    invariants(controller_id, cluster, rabbitmq)
    .and(always(lift_state(Cluster::desired_state_is(rabbitmq))))
    .and(invariants_since_phase_i(controller_id, rabbitmq))
    .and(invariants_since_phase_ii(controller_id, rabbitmq))
    .and(invariants_since_phase_iii(controller_id, rabbitmq))
    .and(invariants_since_phase_iv(rabbitmq))
    .and(invariants_since_phase_v(rabbitmq))
    .and(invariants_since_phase_vi(controller_id, rabbitmq))
    .and(invariants_since_phase_vii(controller_id, rabbitmq))
    .and(invariants_since_phase_viii(controller_id, rabbitmq))
}

pub proof fn assumption_and_invariants_of_all_phases_is_stable(controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq))),
        valid(stable(invariants(controller_id, cluster, rabbitmq))),
        forall |i: nat|  1 <= i <= 8 ==> valid(stable(#[trigger] spec_before_phase_n(controller_id, i, cluster, rabbitmq))),
{
    reveal_with_fuel(spec_before_phase_n, 9);
    invariants_is_stable(controller_id, cluster, rabbitmq);
    always_p_is_stable(lift_state(Cluster::desired_state_is(rabbitmq)));
    invariants_since_phase_i_is_stable(controller_id, rabbitmq);
    invariants_since_phase_ii_is_stable(controller_id, rabbitmq);
    invariants_since_phase_iii_is_stable(controller_id, rabbitmq);
    invariants_since_phase_iv_is_stable(rabbitmq);
    invariants_since_phase_v_is_stable(rabbitmq);
    invariants_since_phase_vi_is_stable(controller_id, rabbitmq);
    invariants_since_phase_vii_is_stable(controller_id, rabbitmq);
    invariants_since_phase_viii_is_stable(controller_id, rabbitmq);
    stable_and_n!(
        invariants(controller_id, cluster, rabbitmq), always(lift_state(Cluster::desired_state_is(rabbitmq))),
        invariants_since_phase_i(controller_id, rabbitmq), invariants_since_phase_ii(controller_id, rabbitmq), invariants_since_phase_iii(controller_id, rabbitmq),
        invariants_since_phase_iv(rabbitmq), invariants_since_phase_v(rabbitmq), invariants_since_phase_vi(controller_id, rabbitmq),
        invariants_since_phase_vii(controller_id, rabbitmq), invariants_since_phase_viii(controller_id, rabbitmq)
    );
}

pub proof fn stable_spec_and_assumption_and_invariants_of_all_phases_is_stable(controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView)
    requires
        valid(stable(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq))),
        valid(stable(invariants(controller_id, cluster, rabbitmq))),
        forall |i: nat| 1 <= i <= 8 ==> valid(stable(#[trigger] spec_before_phase_n(controller_id, i, cluster, rabbitmq))),
    ensures
        valid(stable(stable_spec(cluster, controller_id))),
        valid(stable(stable_spec(cluster, controller_id).and(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)))),
        valid(stable(stable_spec(cluster, controller_id).and(invariants(controller_id, cluster, rabbitmq)))),
        forall |i: nat| 1 <= i <= 8 ==> valid(stable(#[trigger] stable_spec(cluster, controller_id).and(spec_before_phase_n(controller_id, i, cluster, rabbitmq)))),
{
    stable_spec_is_stable(cluster, controller_id);
    stable_and_n!(
        stable_spec(cluster, controller_id),
        assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)
    );
    stable_and_n!(
        stable_spec(cluster, controller_id),
        invariants(controller_id, cluster, rabbitmq)
    );
    assert forall |i: nat|
        1 <= i <= 8
        && valid(stable(stable_spec(cluster, controller_id)))
        && forall |i: nat| 1 <= i <= 8 ==> valid(stable(#[trigger] spec_before_phase_n(controller_id, i, cluster, rabbitmq)))
        implies valid(stable(#[trigger] stable_spec(cluster, controller_id).and(spec_before_phase_n(controller_id, i, cluster, rabbitmq)))) by {
        stable_and_n!(
            stable_spec(cluster, controller_id),
            spec_before_phase_n(controller_id, i, cluster, rabbitmq)
        );
    }
}

pub open spec fn invariants_since_phase_n(controller_id: int, n: nat, cluster: Cluster, rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    if n == 0 {
        invariants(controller_id, cluster, rabbitmq).and(always(lift_state(Cluster::desired_state_is(rabbitmq))))
    } else if n == 1 {
        invariants_since_phase_i(controller_id, rabbitmq)
    } else if n == 2 {
        invariants_since_phase_ii(controller_id, rabbitmq)
    } else if n == 3 {
        invariants_since_phase_iii(controller_id, rabbitmq)
    } else if n == 4 {
        invariants_since_phase_iv(rabbitmq)
    } else if n == 5 {
        invariants_since_phase_v(rabbitmq)
    } else if n == 6 {
        invariants_since_phase_vi(controller_id, rabbitmq)
    } else if n == 7 {
        invariants_since_phase_vii(controller_id, rabbitmq)
    } else if n == 8 {
        invariants_since_phase_viii(controller_id, rabbitmq)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(controller_id: int, n: nat, cluster: Cluster, rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState>
    decreases n,
{
    if n == 1 {
        invariants(controller_id, cluster, rabbitmq).and(always(lift_state(Cluster::desired_state_is(rabbitmq))))
    } else if 2 <= n <= 9 {
        spec_before_phase_n(controller_id, (n-1) as nat, cluster, rabbitmq).and(invariants_since_phase_n(controller_id, (n-1) as nat, cluster, rabbitmq))
    } else {
        true_pred()
    }
}

#[verifier(rlimit(100))]
pub proof fn spec_of_previous_phases_entails_eventually_new_invariants(provided_spec: TempPred<ClusterState>, controller_id: int, cluster: Cluster, i: nat, rabbitmq: RabbitmqClusterView)
    requires
        1 <= i <= 8,
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        provided_spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures provided_spec.and(spec_before_phase_n(controller_id, i, cluster, rabbitmq)).entails(true_pred().leads_to(invariants_since_phase_n(controller_id, i, cluster, rabbitmq))),
{
    let spec = provided_spec.and(spec_before_phase_n(controller_id, i, cluster, rabbitmq));
    // Assert that the combined spec also entails the rely condition.
    entails_and_different_temp(
        provided_spec,
        spec_before_phase_n(controller_id, i, cluster, rabbitmq),
        always(lift_state(rmq_rely_conditions(cluster, controller_id))),
        true_pred()
    );
    temp_pred_equality(
        always(lift_state(rmq_rely_conditions(cluster, controller_id))).and(true_pred()),
        always(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );

    reveal_with_fuel(spec_before_phase_n, 9);
    if i == 1 {
        cluster.lemma_true_leads_to_crash_always_disabled(spec, controller_id);
        cluster.lemma_true_leads_to_pod_monkey_always_disabled(spec);
        cluster.lemma_true_leads_to_req_drop_always_disabled(spec);
        cluster.lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, controller_id, rabbitmq);
        leads_to_always_combine_n!(
            spec,
            true_pred(),
            lift_state(Cluster::crash_disabled(controller_id)),
            lift_state(Cluster::pod_monkey_disabled()),
            lift_state(Cluster::req_drop_disabled()),
            lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, rabbitmq))
        );
    } else {
        entails_trans_n!(spec,
            derived_invariants_since_beginning(controller_id, cluster, rabbitmq),
            always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
        );
        entails_trans(spec,
            derived_invariants_since_beginning(controller_id, cluster, rabbitmq),
            always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))
        );
        terminate::reconcile_eventually_terminates_forall_key(spec, cluster, controller_id);
        // Extract single-key termination for rabbitmq.object_ref() from the forall-key version
        let reconcile_idle = |key: ObjectRef|
            true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(key)));
        tla_forall_apply::<ClusterState, ObjectRef>(reconcile_idle, rabbitmq.object_ref());
        entails_trans(spec, tla_forall(reconcile_idle), reconcile_idle(rabbitmq.object_ref()));
        if i == 2 {
            cluster.lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, controller_id, rabbitmq);
            cluster.lemma_true_leads_to_always_no_pending_request_to_api_server_from_non_controllers(spec);
            // Extract single-key pending_req_of_key_is_unique for the xor lemma
            always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)), rabbitmq.object_ref());
            cluster.lemma_true_leads_to_always_pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(spec, controller_id, rabbitmq.object_ref());
            leads_to_always_combine_n!(
                spec, true_pred(),
                lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)),
                lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()),
                lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, rabbitmq.object_ref()))
            );
        } else if i == 3 {
            helper_invariants::lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step_forall(controller_id, cluster, spec, rabbitmq);
            helper_invariants::lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr_forall(controller_id, cluster, spec, rabbitmq);
            let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq));
            let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq));
            // Prove every_msg_from_key_is_pending_req_msg_of using the cluster-level liveness lemma.
            // Extract single-key no_pending_req for Done and Error from forall-key versions in derived_invariants_since_beginning.
            always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                controller_id, key, cluster.reconcile_model(controller_id).done)), rabbitmq.object_ref());
            always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
                controller_id, key, cluster.reconcile_model(controller_id).error)), rabbitmq.object_ref());
            always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)), rabbitmq.object_ref());
            cluster.lemma_true_leads_to_always_every_msg_from_key_is_pending_req_msg_of(spec, controller_id, rabbitmq.object_ref());
            leads_to_always_combine_n!(
                spec, true_pred(), tla_forall(a_to_p_1), tla_forall(a_to_p_2),
                lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, rabbitmq.object_ref()))
            );
        } else if i == 4 {
            helper_invariants::lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr_forall(controller_id, cluster, spec, rabbitmq);
        } else if i == 5 {
            helper_invariants::lemma_eventually_always_no_delete_resource_request_msg_in_flight_forall(controller_id, cluster, spec, rabbitmq);
        } else if i >= 6 {
            always_tla_forall_apply(spec, |sub_resource: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)), SubResource::ServerConfigMap);
            always_tla_forall_apply(spec, |sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)), SubResource::ServerConfigMap);
            always_tla_forall_apply(spec, |sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)), SubResource::ServerConfigMap);
            always_tla_forall_apply(spec, |sub_resource: SubResource| lift_state(helper_invariants::no_interfering_non_delete_requests_in_flight(sub_resource, controller_id, rabbitmq)), SubResource::ServerConfigMap);
            always_tla_forall_apply(spec, |sub_resource: SubResource| lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)), SubResource::ServerConfigMap);
            if i == 6 {
                helper_invariants::lemma_eventually_always_every_resource_get_then_update_request_implies_at_after_update_resource_step_forall(controller_id, cluster, spec, rabbitmq);
                helper_invariants::lemma_eventually_always_object_in_response_at_after_create_resource_step_is_same_as_etcd_forall(controller_id, cluster, spec, rabbitmq);
                let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq));
                leads_to_always_combine_n!(
                    spec, true_pred(),
                    tla_forall(a_to_p_1), lift_state(helper_invariants::object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq))
                );
            } else if i == 7 {
                always_tla_forall_apply(spec, |sub_resource: SubResource| lift_state(helper_invariants::every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)), SubResource::ServerConfigMap);
                helper_invariants::lemma_eventually_always_object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, cluster, spec, rabbitmq);
            } else {
                helper_invariants::lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated_forall(controller_id, cluster, spec, rabbitmq);
            }
        }
    }
}

pub open spec fn stable_spec(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    next_with_wf(cluster, controller_id)
    .and(always(lift_state(rmq_rely_conditions(cluster, controller_id))))
}

pub proof fn stable_spec_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(stable_spec(cluster, controller_id))),
{
    next_with_wf_is_stable(cluster, controller_id);
    always_p_is_stable(lift_state(rmq_rely_conditions(cluster, controller_id)));
    stable_and_n!(
        next_with_wf(cluster, controller_id),
        always(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );
}

pub proof fn spec_and_invariants_entails_stable_spec_and_invariants(spec: TempPred<ClusterState>, controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(next_with_wf(cluster, controller_id)),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures
        spec.and(derived_invariants_since_beginning(controller_id, cluster, rabbitmq))
            .entails(stable_spec(cluster, controller_id).and(invariants(controller_id, cluster, rabbitmq))),
{
    let pre = spec.and(derived_invariants_since_beginning(controller_id, cluster, rabbitmq));

    // Proof of stable_spec
    entails_and_n!(
        spec,
        next_with_wf(cluster, controller_id),
        always(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );

    entails_and_different_temp(
        spec,
        derived_invariants_since_beginning(controller_id, cluster, rabbitmq),
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
        derived_invariants_since_beginning(controller_id, cluster, rabbitmq),
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
        derived_invariants_since_beginning(controller_id, cluster, rabbitmq)
    );

    entails_and_n!(
        pre,
        stable_spec(cluster, controller_id),
        invariants(controller_id, cluster, rabbitmq)
    );
}

// Next and all the wf conditions.
pub open spec fn next_with_wf(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    always(lift_action(cluster.next()))
    .and(tla_forall(|input| cluster.api_server_next().weak_fairness(input)))
    .and(tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)))
    .and(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))))
    .and(tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))))
    .and(tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))))
    .and(cluster.disable_crash().weak_fairness(controller_id))
    .and(cluster.disable_pod_monkey().weak_fairness(()))
    .and(cluster.disable_req_drop().weak_fairness(()))
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
        cluster.disable_pod_monkey().weak_fairness(()),
        cluster.disable_req_drop().weak_fairness(())
    );
}

// This predicate combines all the possible actions (next), weak fairness and invariants that hold throughout the execution.
// We name it invariants here because these predicates are never violated, thus they can all be seen as some kind of invariants.
//
// The final goal of our proof is to show init /\ invariants |= []desired_state_is(cr) ~> []current_state_matches(cr).
// init /\ invariants is equivalent to init /\ next /\ weak_fairness, so we get spec |= []desired_state_is(cr) ~> []current_state_matches(cr).
pub open spec fn invariants(controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    next_with_wf(cluster, controller_id)
    .and(derived_invariants_since_beginning(controller_id, cluster, rabbitmq))
}

pub proof fn invariants_is_stable(controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants(controller_id, cluster, rabbitmq))),
{
    next_with_wf_is_stable(cluster, controller_id);
    derived_invariants_since_beginning_is_stable(controller_id, cluster, rabbitmq);
    stable_and_n!(
        next_with_wf(cluster, controller_id),
        derived_invariants_since_beginning(controller_id, cluster, rabbitmq)
    );
}

// The safety invariants that are required to prove liveness.
pub open spec fn derived_invariants_since_beginning(controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(lift_state(rmq_guarantee(controller_id))) // guarantee is an invariant as well
    .and(always(lift_state(Cluster::every_in_flight_msg_has_unique_id())))
    .and(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id))))
    .and(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
    .and(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref()))))
    .and(always(lift_state(Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd())))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    .and(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>())))
    .and(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))))
    .and(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_interfering_non_delete_requests_in_flight(res, controller_id, rabbitmq)))))
    .and(always(lift_state(Cluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref()))))
    .and(always(lift_state(Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref()))))
    .and(always(lift_state(Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref()))))
    .and(always(tla_forall(|res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(controller_id, res, rabbitmq)))))
    .and(always(tla_forall(|res: SubResource| lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, rabbitmq).key)))))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)))))
    .and(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
    .and(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id))))
    .and(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())))
    .and(always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id))))
    // Additional invariants needed by cluster_invariants_since_reconciliation
    .and(always(lift_state(Cluster::etcd_objects_have_unique_uids())))
    .and(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>())))
    .and(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())))
    .and(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<RabbitmqClusterView>(controller_id))))
    .and(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
    .and(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(controller_id))))
    .and(always(lift_state(Cluster::etcd_is_finite())))
    .and(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())))
    .and(always(lift_state(helper_invariants::sts_in_etcd_with_rmq_key_match_rmq_selector(rabbitmq))))
    // Forall-key versions needed by reconcile_eventually_terminates_forall_key
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, key, at_step_closure(RabbitmqReconcileStep::Init))))))
    .and(always(tla_forall(|step: (ObjectRef, ActionKind, SubResource)| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, step.0, at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.1, step.2)))))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, key, cluster.reconcile_model(controller_id).done)))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, key, cluster.reconcile_model(controller_id).error)))))
}

pub proof fn derived_invariants_since_beginning_is_stable(controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView)
    ensures valid(stable(derived_invariants_since_beginning(controller_id, cluster, rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq));
    let a_to_p_3 = |res: SubResource| lift_state(helper_invariants::no_interfering_non_delete_requests_in_flight(res, controller_id, rabbitmq));
    let a_to_p_4 = |res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(controller_id, res, rabbitmq));
    let a_to_p_5 = |res: SubResource| lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, rabbitmq).key));
    let a_to_p_6 = |sub_resource: SubResource| lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq));
    let a_to_p_key_unique = |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key));
    let a_to_p_no_pending = |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, key, at_step_closure(RabbitmqReconcileStep::Init)));
    let a_to_p_pending_in_flight = |step: (ObjectRef, ActionKind, SubResource)| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, step.0, at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.1, step.2))));
    let a_to_p_no_pending_done = |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, key, cluster.reconcile_model(controller_id).done));
    let a_to_p_no_pending_error = |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, key, cluster.reconcile_model(controller_id).error));
    always_p_is_stable(lift_state(Cluster::there_is_the_controller_state(controller_id)));
    always_p_is_stable(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)));
    stable_and_always_n!(
        lift_state(rmq_guarantee(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())),
        lift_state(Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        tla_forall(a_to_p_1),
        tla_forall(a_to_p_3),
        lift_state(Cluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())),
        lift_state(Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())),
        lift_state(Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())),
        tla_forall(a_to_p_4),
        tla_forall(a_to_p_5),
        tla_forall(a_to_p_6),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::etcd_objects_have_unique_uids()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()),
        lift_state(helper_invariants::sts_in_etcd_with_rmq_key_match_rmq_selector(rabbitmq)),
        tla_forall(a_to_p_key_unique),
        tla_forall(a_to_p_no_pending),
        tla_forall(a_to_p_pending_in_flight),
        tla_forall(a_to_p_no_pending_done),
        tla_forall(a_to_p_no_pending_error)
    );
}

// The first notable phase comes when crash and k8s busy are always disabled and the object in schedule always has the same
// spec and uid as the cr we provide.
//
// Note that don't try to find any connections between those invariants -- they are put together because they don't have to
// wait for another of them to first be satisfied.
pub open spec fn invariants_since_phase_i(controller_id: int, rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(lift_state(Cluster::crash_disabled(controller_id)))
    .and(always(lift_state(Cluster::pod_monkey_disabled())))
    .and(always(lift_state(Cluster::req_drop_disabled())))
    .and(always(lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, rabbitmq))))
}

pub proof fn invariants_since_phase_i_is_stable(controller_id: int, rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_i(controller_id, rabbitmq))),
{
    stable_and_always_n!(
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as(controller_id, rabbitmq))
    );
}

// For now, phase II only contains one invariant, which is the object in reconcile has the same spec and uid as rabbitmq.
//
// It is alone because it relies on the invariant the_object_in_schedule_has_spec_and_uid_as (in phase I) and every invariant
// in phase III relies on it.
pub open spec fn invariants_since_phase_ii(controller_id: int, rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))
    .and(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())))
    .and(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, rabbitmq.object_ref()))))
}


pub proof fn invariants_since_phase_ii_is_stable(controller_id: int, rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_ii(controller_id, rabbitmq))),
{
    always_p_is_stable(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)));
    always_p_is_stable(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()));
    always_p_is_stable(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, rabbitmq.object_ref())));
    stable_and_always_n!(
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)),
        lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, rabbitmq.object_ref()))
    );
}

pub open spec fn invariants_since_phase_iii(controller_id: int, rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq))))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)))))
    .and(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, rabbitmq.object_ref()))))
}

pub proof fn invariants_since_phase_iii_is_stable(controller_id: int, rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_iii(controller_id, rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq));
    let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq));
    stable_and_always_n!(
        tla_forall(a_to_p_1), tla_forall(a_to_p_2),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, rabbitmq.object_ref()))
    );
}

// Invariants since this phase ensure that certain objects only have owner references that point to current cr.
// To have these invariants, we first need the invariant that evert create/update request make/change the object in the
// expected way.
pub open spec fn invariants_since_phase_iv(rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))
}

pub proof fn invariants_since_phase_iv_is_stable(rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_iv(rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq));
    always_p_is_stable(tla_forall(a_to_p_1));
}

// Invariants since phase V rely on the invariants since phase IV. When the objects starts to always have owner reference
// pointing to current cr, it will never be recycled by the garbage collector. Plus, the reconciler itself never tries to
// delete this object, so we can have the invariants saying that no delete request messages will be in flight.
pub open spec fn invariants_since_phase_v(rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq))))
}

pub proof fn invariants_since_phase_v_is_stable(rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_v(rabbitmq))),
{
    always_p_is_stable(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq))));
}

pub open spec fn invariants_since_phase_vi(controller_id: int, rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq))))
    .and(always(lift_state(helper_invariants::object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq))))
}

pub proof fn invariants_since_phase_vi_is_stable(controller_id: int, rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_vi(controller_id, rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq));
    stable_and_always_n!(
        tla_forall(a_to_p_1),
        lift_state(helper_invariants::object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(helper_invariants::object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq))
    );
}

pub open spec fn invariants_since_phase_vii(controller_id: int, rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(lift_state(helper_invariants::object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)))
}

pub proof fn invariants_since_phase_vii_is_stable(controller_id: int, rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_vii(controller_id, rabbitmq))),
{
    always_p_is_stable(lift_state(helper_invariants::object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)));
}

pub open spec fn invariants_since_phase_viii(controller_id: int, rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq)))
}

pub proof fn invariants_since_phase_viii_is_stable(controller_id: int, rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_viii(controller_id, rabbitmq))),
{
    always_p_is_stable(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq)));
}

#[verifier(spinoff_prover)]
pub proof fn sm_spec_entails_all_invariants(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(derived_invariants_since_beginning(controller_id, cluster, rabbitmq)),
{
    guarantee::guarantee_condition_holds(spec, cluster, controller_id);
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_cr_states_are_unmarshallable::<RabbitmqReconciler, RabbitmqReconcileState, RabbitmqClusterView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec, controller_id, rabbitmq.object_ref());
    cluster.lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    cluster.lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);

    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq));
    assert_by(spec.entails(always(tla_forall(a_to_p_1))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_1(sub_resource))) by {
            helper_invariants::lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(controller_id, cluster, spec, sub_resource, rabbitmq);
        }
        spec_entails_always_tla_forall_equality(spec, a_to_p_1);
    });
    RabbitmqReconcileState::marshal_preserves_integrity();

    let a_to_p_3 = |res: SubResource| lift_state(helper_invariants::no_interfering_non_delete_requests_in_flight(res, controller_id, rabbitmq));
    assert_by(spec.entails(always(tla_forall(a_to_p_3))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_3(sub_resource))) by {
            helper_invariants::lemma_always_no_interfering_non_delete_requests_in_flight(controller_id, cluster, spec, sub_resource, rabbitmq);
        }
        spec_entails_always_tla_forall_equality(spec, a_to_p_3);
    });
    cluster.lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(spec, controller_id, rabbitmq.object_ref());
    cluster.lemma_always_key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(spec, controller_id, rabbitmq.object_ref());
    cluster.lemma_always_key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(spec, controller_id, rabbitmq.object_ref());
    let a_to_p_4 = |res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(controller_id, res, rabbitmq));
    assert_by(spec.entails(always(tla_forall(a_to_p_4))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_4(sub_resource))) by {
            helper_invariants::lemma_always_response_at_after_get_resource_step_is_resource_get_response(controller_id, cluster, spec, sub_resource, rabbitmq);
        }
        spec_entails_always_tla_forall_equality(spec, a_to_p_4);
    });
    let a_to_p_5 = |res: SubResource| lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, rabbitmq).key));
    assert_by(spec.entails(always(tla_forall(a_to_p_5))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_5(sub_resource))) by {
            cluster.lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, get_request(sub_resource, rabbitmq).key);
        }
        spec_entails_always_tla_forall_equality(spec, a_to_p_5);
    });
    let a_to_p_6 = |sub_resource: SubResource| lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq));
    assert_by(spec.entails(always(tla_forall(a_to_p_6))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_6(sub_resource))) by {
            helper_invariants::lemma_always_no_create_resource_request_msg_without_name_in_flight(cluster, controller_id, spec, sub_resource, rabbitmq);
        }
        spec_entails_always_tla_forall_equality(spec, a_to_p_6);
    });
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    helper_invariants::lemma_always_there_is_no_request_msg_to_external_from_controller(controller_id, cluster, spec);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    cluster.lemma_always_every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(spec, controller_id);
    // Additional invariants needed by cluster_invariants_since_reconciliation
    cluster.lemma_always_etcd_objects_have_unique_uids(spec);
    cluster.lemma_always_each_builtin_object_in_etcd_is_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_cr_objects_in_schedule_satisfy_state_validation::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_every_ongoing_reconcile_has_lower_id_than_allocator(spec, controller_id);
    cluster.lemma_always_ongoing_reconciles_is_finite(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_etcd_is_finite(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_every_in_flight_msg_has_no_replicas_and_has_unique_id(spec);
    helper_invariants::lemma_always_sts_in_etcd_with_rmq_key_match_rmq_selector(controller_id, cluster, spec, rabbitmq);

    // Forall-key versions needed by reconcile_eventually_terminates_forall_key
    let a_to_p_key_unique = |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key));
    assert_by(spec.entails(always(tla_forall(a_to_p_key_unique))), {
        assert forall |key: ObjectRef| spec.entails(always(#[trigger] a_to_p_key_unique(key))) by {
            cluster.lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, controller_id, key);
        }
        spec_entails_always_tla_forall_equality(spec, a_to_p_key_unique);
    });
    let a_to_p_no_pending = |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, key, at_step_closure(RabbitmqReconcileStep::Init)));
    assert_by(spec.entails(always(tla_forall(a_to_p_no_pending))), {
        assert forall |key: ObjectRef| spec.entails(always(#[trigger] a_to_p_no_pending(key))) by {
            sm_spec_entails_no_pending_msg_at_init(cluster, spec, controller_id, key);
        }
        spec_entails_always_tla_forall_equality(spec, a_to_p_no_pending);
    });
    let a_to_p_pending_in_flight = |step: (ObjectRef, ActionKind, SubResource)| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, step.0, at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.1, step.2))));
    assert_by(spec.entails(always(tla_forall(a_to_p_pending_in_flight))), {
        assert forall |step: (ObjectRef, ActionKind, SubResource)| spec.entails(always(#[trigger] a_to_p_pending_in_flight(step))) by {
            sm_spec_entails_pending_req_in_flight_at_after_k_request_step(cluster, spec, controller_id, step.0, step.1, step.2);
        }
        spec_entails_always_tla_forall_equality(spec, a_to_p_pending_in_flight);
    });
    let a_to_p_no_pending_done = |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, key, cluster.reconcile_model(controller_id).done));
    assert_by(spec.entails(always(tla_forall(a_to_p_no_pending_done))), {
        assert forall |key: ObjectRef| spec.entails(always(#[trigger] a_to_p_no_pending_done(key))) by {
            sm_spec_entails_no_pending_msg_at_done(cluster, spec, controller_id, key);
        }
        spec_entails_always_tla_forall_equality(spec, a_to_p_no_pending_done);
    });
    let a_to_p_no_pending_error = |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, key, cluster.reconcile_model(controller_id).error));
    assert_by(spec.entails(always(tla_forall(a_to_p_no_pending_error))), {
        assert forall |key: ObjectRef| spec.entails(always(#[trigger] a_to_p_no_pending_error(key))) by {
            sm_spec_entails_no_pending_msg_at_error(cluster, spec, controller_id, key);
        }
        spec_entails_always_tla_forall_equality(spec, a_to_p_no_pending_error);
    });
    entails_always_and_n!(
        spec,
        lift_state(rmq_guarantee(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())),
        lift_state(Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        tla_forall(a_to_p_1),
        tla_forall(a_to_p_3),
        lift_state(Cluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())),
        lift_state(Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())),
        lift_state(Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())),
        tla_forall(a_to_p_4),
        tla_forall(a_to_p_5),
        tla_forall(a_to_p_6),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::etcd_objects_have_unique_uids()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()),
        lift_state(helper_invariants::sts_in_etcd_with_rmq_key_match_rmq_selector(rabbitmq)),
        tla_forall(a_to_p_key_unique),
        tla_forall(a_to_p_no_pending),
        tla_forall(a_to_p_pending_in_flight),
        tla_forall(a_to_p_no_pending_done),
        tla_forall(a_to_p_no_pending_error)
    );
}

#[verifier(spinoff_prover)]
pub proof fn sm_spec_entails_no_pending_msg_at_init(
    cluster: Cluster, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef
)
requires
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
ensures
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_step_closure(RabbitmqReconcileStep::Init))))),
{
    cluster.lemma_always_cr_states_are_unmarshallable::<RabbitmqReconciler, RabbitmqReconcileState, RabbitmqClusterView, VoidEReqView, VoidERespView>(spec, controller_id);
    RabbitmqReconcileState::marshal_preserves_integrity();
    cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, key, at_step_closure(RabbitmqReconcileStep::Init));
}

#[verifier(spinoff_prover)]
pub proof fn sm_spec_entails_pending_req_in_flight_at_after_k_request_step(
    cluster: Cluster, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef, action: ActionKind, sub_resource: SubResource
)
requires
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
ensures
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, key, at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(action, sub_resource)))))),
{
    RabbitmqReconcileState::marshal_preserves_integrity();
    RabbitmqClusterView::marshal_preserves_integrity();
    cluster.lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, controller_id, key);
    cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        spec, controller_id, key,
        at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(action, sub_resource))
    );
}

#[verifier(spinoff_prover)]
pub proof fn sm_spec_entails_no_pending_msg_at_done(
    cluster: Cluster, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef
)
requires
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
ensures
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, key, cluster.reconcile_model(controller_id).done)))),
{
    RabbitmqReconcileState::marshal_preserves_integrity();
    cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, key, cluster.reconcile_model(controller_id).done);
}

#[verifier(spinoff_prover)]
pub proof fn sm_spec_entails_no_pending_msg_at_error(
    cluster: Cluster, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef
)
requires
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
ensures
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, key, cluster.reconcile_model(controller_id).error)))),
{
    RabbitmqReconcileState::marshal_preserves_integrity();
    cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, key, cluster.reconcile_model(controller_id).error);
}

pub proof fn spec_entails_always_desired_state_is_leads_to_assumption_and_invariants_of_all_phases(spec: TempPred<ClusterState>, controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(next_with_wf(cluster, controller_id)),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq))),
{
    assumption_and_invariants_of_all_phases_is_stable(controller_id, cluster, rabbitmq);
    stable_spec_is_stable(cluster, controller_id);
    let stable_spec = stable_spec(cluster, controller_id);

    assert(stable_spec.and(invariants(controller_id, cluster, rabbitmq)).entails(
        always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)))) by {
        assert(stable_spec.and(invariants(controller_id, cluster, rabbitmq)).and(always(lift_state(Cluster::desired_state_is(rabbitmq)))).entails(true_pred()
            .leads_to(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)))) by {
            // Show that spec_before_phase_n(9) entails assumption_and_invariants_of_all_phases
            assert(spec_before_phase_n(controller_id, 9, cluster, rabbitmq).entails(
                assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq))) by {
                reveal_with_fuel(spec_before_phase_n, 9);
                combine_spec_entails_n!(
                    spec_before_phase_n(controller_id, 9, cluster, rabbitmq),
                    assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq),
                    invariants(controller_id, cluster, rabbitmq),
                    always(lift_state(Cluster::desired_state_is(rabbitmq))),
                    invariants_since_phase_i(controller_id, rabbitmq),
                    invariants_since_phase_ii(controller_id, rabbitmq),
                    invariants_since_phase_iii(controller_id, rabbitmq),
                    invariants_since_phase_iv(rabbitmq),
                    invariants_since_phase_v(rabbitmq),
                    invariants_since_phase_vi(controller_id, rabbitmq),
                    invariants_since_phase_vii(controller_id, rabbitmq),
                    invariants_since_phase_viii(controller_id, rabbitmq)
                );
            }

            // Show that stable_spec.and(spec_before_phase_n(9)) entails true ~> assumption_and_invariants_of_all_phases
            assert(stable_spec.and(spec_before_phase_n(controller_id, 9, cluster, rabbitmq)).entails(
                true_pred().leads_to(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)))) by {
                assert(stable_spec.and(always(spec_before_phase_n(controller_id, 9, cluster, rabbitmq))).entails(
                    true_pred().leads_to(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)))) by {
                    entails_implies_leads_to(
                        stable_spec,
                        spec_before_phase_n(controller_id, 9, cluster, rabbitmq),
                        assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)
                    );
                    temp_pred_equality(
                        true_pred().and(spec_before_phase_n(controller_id, 9, cluster, rabbitmq)),
                        spec_before_phase_n(controller_id, 9, cluster, rabbitmq)
                    );
                    pack_conditions_to_spec(
                        stable_spec,
                        spec_before_phase_n(controller_id, 9, cluster, rabbitmq),
                        true_pred(),
                        assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)
                    );
                }
                assert(always(spec_before_phase_n(controller_id, 9, cluster, rabbitmq)) == spec_before_phase_n(controller_id, 9, cluster, rabbitmq)) by {
                    assert(valid(stable(spec_before_phase_n(controller_id, 9, cluster, rabbitmq)))) by {
                        invariants_since_phase_viii_is_stable(controller_id, rabbitmq);
                        stable_and_temp(
                            spec_before_phase_n(controller_id, 8, cluster, rabbitmq),
                            invariants_since_phase_n(controller_id, 8, cluster, rabbitmq)
                        );
                        temp_pred_equality(
                            spec_before_phase_n(controller_id, 8, cluster, rabbitmq).and(invariants_since_phase_n(controller_id, 8, cluster, rabbitmq)),
                            spec_before_phase_n(controller_id, 9, cluster, rabbitmq)
                        );
                    };
                    stable_to_always(spec_before_phase_n(controller_id, 9, cluster, rabbitmq));
                }
            };

            // Chain through all the phases
            spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(8, stable_spec, controller_id, cluster, rabbitmq);
            spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(7, stable_spec, controller_id, cluster, rabbitmq);
            spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(6, stable_spec, controller_id, cluster, rabbitmq);
            spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(5, stable_spec, controller_id, cluster, rabbitmq);
            spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(4, stable_spec, controller_id, cluster, rabbitmq);
            spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(3, stable_spec, controller_id, cluster, rabbitmq);
            spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(2, stable_spec, controller_id, cluster, rabbitmq);
            spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(1, stable_spec, controller_id, cluster, rabbitmq);

            temp_pred_equality(
                stable_spec.and(invariants(controller_id, cluster, rabbitmq)).and(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
                stable_spec.and(spec_before_phase_n(controller_id, 1, cluster, rabbitmq))
            );
        }
        stable_and_temp(
            stable_spec,
            invariants(controller_id, cluster, rabbitmq)
        );
        unpack_conditions_from_spec(
            stable_spec.and(invariants(controller_id, cluster, rabbitmq)),
            always(lift_state(Cluster::desired_state_is(rabbitmq))),
            true_pred(),
            assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)
        );
        temp_pred_equality(
            true_pred().and(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
            always(lift_state(Cluster::desired_state_is(rabbitmq)))
        );
    }

    spec_and_invariants_entails_stable_spec_and_invariants(spec, controller_id, cluster, rabbitmq);
    entails_trans(
        spec.and(derived_invariants_since_beginning(controller_id, cluster, rabbitmq)),
        stable_spec.and(invariants(controller_id, cluster, rabbitmq)),
        always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq))
    );
    entails_trans(
        spec,
        next_with_wf(cluster, controller_id),
        always(lift_action(cluster.next()))
    );
    sm_spec_entails_all_invariants(controller_id, cluster, spec, rabbitmq);
    simplify_predicate(spec, derived_invariants_since_beginning(controller_id, cluster, rabbitmq));
}

proof fn spec_before_phase_n_entails_true_leads_to_assumption_and_invariants_of_all_phases(i: nat, spec: TempPred<ClusterState>, controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView)
    requires
        1 <= i <= 8,
        valid(stable(spec)),
        valid(stable(spec_before_phase_n(controller_id, i, cluster, rabbitmq))),
        spec.and(spec_before_phase_n(controller_id, i + 1, cluster, rabbitmq)).entails(true_pred().leads_to(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures
        spec.and(spec_before_phase_n(controller_id, i, cluster, rabbitmq)).entails(true_pred().leads_to(assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq))),
{
    stable_and_temp(spec, spec_before_phase_n(controller_id, i, cluster, rabbitmq));
    reveal_with_fuel(spec_before_phase_n, 9);
    temp_pred_equality(
        spec.and(spec_before_phase_n(controller_id, i + 1, cluster, rabbitmq)),
        spec.and(spec_before_phase_n(controller_id, i, cluster, rabbitmq))
            .and(invariants_since_phase_n(controller_id, i, cluster, rabbitmq))
    );
    spec_of_previous_phases_entails_eventually_new_invariants(spec, controller_id, cluster, i, rabbitmq);
    unpack_conditions_from_spec(
        spec.and(spec_before_phase_n(controller_id, i, cluster, rabbitmq)),
        invariants_since_phase_n(controller_id, i, cluster, rabbitmq),
        true_pred(),
        assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)
    );
    temp_pred_equality(
        true_pred().and(invariants_since_phase_n(controller_id, i, cluster, rabbitmq)),
        invariants_since_phase_n(controller_id, i, cluster, rabbitmq)
    );
    leads_to_trans(
        spec.and(spec_before_phase_n(controller_id, i, cluster, rabbitmq)),
        true_pred(),
        invariants_since_phase_n(controller_id, i, cluster, rabbitmq),
        assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq)
    );
}

}
