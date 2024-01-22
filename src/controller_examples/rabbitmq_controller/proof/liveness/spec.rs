// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    model::reconciler::*,
    proof::{helper_invariants, liveness::terminate, predicate::*, resource::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub open spec fn assumption_and_invariants_of_all_phases(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    invariants(rabbitmq)
    .and(always(lift_state(desired_state_is(rabbitmq))))
    .and(invariants_since_phase_i(rabbitmq))
    .and(invariants_since_phase_ii(rabbitmq))
    .and(invariants_since_phase_iii(rabbitmq))
    .and(invariants_since_phase_iv(rabbitmq))
    .and(invariants_since_phase_v(rabbitmq))
    .and(invariants_since_phase_vi(rabbitmq))
    .and(invariants_since_phase_vii(rabbitmq))
}

pub open spec fn invariants_since_phase_n(n: nat, rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    if n == 0 {
        invariants(rabbitmq).and(always(lift_state(desired_state_is(rabbitmq))))
    } else if n == 1 {
        invariants_since_phase_i(rabbitmq)
    } else if n == 2 {
        invariants_since_phase_ii(rabbitmq)
    } else if n == 3 {
        invariants_since_phase_iii(rabbitmq)
    } else if n == 4 {
        invariants_since_phase_iv(rabbitmq)
    } else if n == 5 {
        invariants_since_phase_v(rabbitmq)
    } else if n == 6 {
        invariants_since_phase_vi(rabbitmq)
    } else if n == 7 {
        invariants_since_phase_vii(rabbitmq)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(n: nat, rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster>
    decreases n,
{
    if n == 1 {
        invariants(rabbitmq).and(always(lift_state(desired_state_is(rabbitmq))))
    } else if 2 <= n <= 8 {
        spec_before_phase_n((n-1) as nat, rabbitmq).and(invariants_since_phase_n((n-1) as nat, rabbitmq))
    } else {
        true_pred()
    }
}

pub proof fn spec_of_previous_phases_entails_eventually_new_invariants(i: nat, rabbitmq: RabbitmqClusterView)
    requires 1 <= i <= 7,
    ensures spec_before_phase_n(i, rabbitmq).entails(true_pred().leads_to(invariants_since_phase_n(i, rabbitmq))),
{
    let spec = spec_before_phase_n(i, rabbitmq);
    reveal_with_fuel(spec_before_phase_n, 8);
    if i == 1 {
        RMQCluster::lemma_true_leads_to_crash_always_disabled(spec);
        RMQCluster::lemma_true_leads_to_busy_always_disabled(spec);
        RMQCluster::lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, rabbitmq);
        leads_to_always_combine_n!(
            spec,
            true_pred(),
            lift_state(RMQCluster::crash_disabled()),
            lift_state(RMQCluster::busy_disabled()),
            lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq))
        );
    } else {
        terminate::reconcile_eventually_terminates(spec, rabbitmq);
        if i == 2 {
            RMQCluster::lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, rabbitmq);
        } else if i == 3 {
            helper_invariants::lemma_always_rabbitmq_is_well_formed(spec, rabbitmq);
            helper_invariants::lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step_forall(spec, rabbitmq);
            helper_invariants::lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr_forall(spec, rabbitmq);
            let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq));
            let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, rabbitmq));
            leads_to_always_combine_n!(
                spec, true_pred(), tla_forall(a_to_p_1), tla_forall(a_to_p_2)
            );
        } else if i == 4 {
            helper_invariants::lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr_forall(spec, rabbitmq);
        } else if i == 5 {
            helper_invariants::lemma_eventually_always_no_delete_resource_request_msg_in_flight_forall(spec, rabbitmq);
        } else if i == 6 {
            helper_invariants::lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step_forall(spec, rabbitmq);
            helper_invariants::lemma_eventually_always_object_in_response_at_after_create_resource_step_is_same_as_etcd_forall(spec, rabbitmq);
            helper_invariants::lemma_eventually_always_object_in_response_at_after_update_resource_step_is_same_as_etcd_forall(spec, rabbitmq);
            let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq));
            leads_to_always_combine_n!(
                spec, true_pred(),
                tla_forall(a_to_p_1), lift_state(helper_invariants::object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ServerConfigMap, rabbitmq)), lift_state(helper_invariants::object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ServerConfigMap, rabbitmq))
            );
        } else if i == 7 {
            helper_invariants::lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated_forall(spec, rabbitmq);
        }
    }
}

pub proof fn assumption_and_invariants_of_all_phases_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(rabbitmq))),
        valid(stable(invariants(rabbitmq))),
        forall |i: nat|  1 <= i <= 8 ==> valid(stable(#[trigger] spec_before_phase_n(i, rabbitmq))),
{
    reveal_with_fuel(spec_before_phase_n, 8);
    invariants_is_stable(rabbitmq);
    always_p_is_stable(lift_state(desired_state_is(rabbitmq)));
    invariants_since_phase_i_is_stable(rabbitmq);
    invariants_since_phase_ii_is_stable(rabbitmq);
    invariants_since_phase_iii_is_stable(rabbitmq);
    invariants_since_phase_iv_is_stable(rabbitmq);
    invariants_since_phase_v_is_stable(rabbitmq);
    invariants_since_phase_vi_is_stable(rabbitmq);
    invariants_since_phase_vii_is_stable(rabbitmq);
    stable_and_n!(
        invariants(rabbitmq), always(lift_state(desired_state_is(rabbitmq))),
        invariants_since_phase_i(rabbitmq), invariants_since_phase_ii(rabbitmq), invariants_since_phase_iii(rabbitmq),
        invariants_since_phase_iv(rabbitmq), invariants_since_phase_v(rabbitmq), invariants_since_phase_vi(rabbitmq),
        invariants_since_phase_vii(rabbitmq)
    );
}

// Next and all the wf conditions.
pub open spec fn next_with_wf() -> TempPred<RMQCluster> {
    always(lift_action(RMQCluster::next()))
    .and(tla_forall(|input| RMQCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::external_api_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::schedule_controller_reconcile().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::builtin_controllers_next().weak_fairness(input)))
    .and(RMQCluster::disable_crash().weak_fairness(()))
    .and(RMQCluster::disable_transient_failure().weak_fairness(()))
}

pub proof fn next_with_wf_is_stable()
    ensures valid(stable(next_with_wf())),
{
    always_p_is_stable(lift_action(RMQCluster::next()));
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::kubernetes_api_next());
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::external_api_next());
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::controller_next());
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::schedule_controller_reconcile());
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::builtin_controllers_next());
    RMQCluster::action_weak_fairness_is_stable(RMQCluster::disable_crash());
    RMQCluster::action_weak_fairness_is_stable(RMQCluster::disable_transient_failure());
    stable_and_n!(
        always(lift_action(RMQCluster::next())),
        tla_forall(|input| RMQCluster::kubernetes_api_next().weak_fairness(input)),
        tla_forall(|input| RMQCluster::external_api_next().weak_fairness(input)),
        tla_forall(|input| RMQCluster::controller_next().weak_fairness(input)),
        tla_forall(|input| RMQCluster::schedule_controller_reconcile().weak_fairness(input)),
        tla_forall(|input| RMQCluster::builtin_controllers_next().weak_fairness(input)),
        RMQCluster::disable_crash().weak_fairness(()),
        RMQCluster::disable_transient_failure().weak_fairness(())
    );
}

/// This predicate combines all the possible actions (next), weak fairness and invariants that hold throughout the execution.
/// We name it invariants here because these predicates are never violated, thus they can all be seen as some kind of invariants.
///
/// The final goal of our proof is to show init /\ invariants |= []desired_state_is(cr) ~> []current_state_matches(cr).
/// init /\ invariants is equivalent to init /\ next /\ weak_fairness, so we get cluster_spec() |= []desired_state_is(cr) ~> []current_state_matches(cr).
pub open spec fn invariants(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    next_with_wf().and(derived_invariants_since_beginning(rabbitmq))
}

pub proof fn invariants_is_stable(rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants(rabbitmq))),
{
    next_with_wf_is_stable();
    derived_invariants_since_beginning_is_stable(rabbitmq);
    stable_and_n!(
        next_with_wf(),
        derived_invariants_since_beginning(rabbitmq)
    );
}

// The safety invariants that are required to prove liveness.
pub open spec fn derived_invariants_since_beginning(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(RMQCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::object_in_ok_get_response_has_smaller_rv_than_etcd())))
    .and(always(lift_state(RMQCluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(RMQCluster::each_scheduled_object_has_consistent_key_and_valid_metadata())))
    .and(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))))
    .and(always(lift_state(RMQCluster::no_pending_req_msg_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init)))))
    .and(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1)))))))
    .and(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq)))))
    .and(always(lift_state(helper_invariants::no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(rabbitmq))))
    .and(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(rabbitmq.object_ref()))))
    .and(always(tla_forall(|res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, rabbitmq)))))
    .and(always(tla_forall(|res: SubResource| lift_state(RMQCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, rabbitmq).key)))))
    .and(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq))))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))))
}

pub proof fn derived_invariants_since_beginning_is_stable(rabbitmq: RabbitmqClusterView)
    ensures valid(stable(derived_invariants_since_beginning(rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq));
    let a_to_p_2 = |step: (ActionKind, SubResource)| lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1))));
    let a_to_p_3 = |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq));
    let a_to_p_4 = |res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, rabbitmq));
    let a_to_p_5 = |res: SubResource| lift_state(RMQCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, rabbitmq).key));
    let a_to_p_6 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq));
    stable_and_always_n!(
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(rabbitmq.object_ref())),
        lift_state(RMQCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(RMQCluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())),
        lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        tla_forall(a_to_p_1),
        lift_state(RMQCluster::no_pending_req_msg_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init))),
        tla_forall(a_to_p_2),
        tla_forall(a_to_p_3),
        lift_state(helper_invariants::no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(rabbitmq)),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(rabbitmq.object_ref())),
        lift_state(RMQCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(rabbitmq.object_ref())),
        tla_forall(a_to_p_4),
        tla_forall(a_to_p_5),
        lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)),
        tla_forall(a_to_p_6)
    );
}

/// The first notable phase comes when crash and k8s busy are always disabled and the object in schedule always has the same
/// spec and uid as the cr we provide.
///
/// Note that don't try to find any connections between those invariants -- they are put together because they don't have to
/// wait for another of them to first be satisfied.
pub open spec fn invariants_since_phase_i(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_state(RMQCluster::crash_disabled()))
    .and(always(lift_state(RMQCluster::busy_disabled())))
    .and(always(lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq))))
}

pub proof fn invariants_since_phase_i_is_stable(rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_i(rabbitmq))),
{
    stable_and_always_n!(
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::the_object_in_schedule_has_spec_and_uid_as(rabbitmq))
    );
}

/// For now, phase II only contains one invariant, which is the object in reconcile has the same spec and uid as rabbitmq.
///
/// It is alone because it relies on the invariant the_object_in_schedule_has_spec_and_uid_as (in phase I) and every invariant
/// in phase III relies on it.
pub open spec fn invariants_since_phase_ii(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)))
}


pub proof fn invariants_since_phase_ii_is_stable(rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_ii(rabbitmq))),
{
    always_p_is_stable(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)));
}

pub open spec fn invariants_since_phase_iii(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq))))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, rabbitmq)))))
}

pub proof fn invariants_since_phase_iii_is_stable(rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_iii(rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq));
    let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, rabbitmq));
    stable_and_always_n!(tla_forall(a_to_p_1), tla_forall(a_to_p_2));
}

/// Invariants since this phase ensure that certain objects only have owner references that point to current cr.
/// To have these invariants, we first need the invariant that evert create/update request make/change the object in the
/// expected way.
pub open spec fn invariants_since_phase_iv(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))
}

pub proof fn invariants_since_phase_iv_is_stable(rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_iv(rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq));
    always_p_is_stable(tla_forall(a_to_p_1));
}

/// Invariants since phase V rely on the invariants since phase IV. When the objects starts to always have owner reference
/// pointing to current cr, it will never be recycled by the garbage collector. Plus, the reconciler itself never tries to
/// delete this object, so we can have the invariants saying that no delete request messages will be in flight.
pub open spec fn invariants_since_phase_v(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq))))
}

pub proof fn invariants_since_phase_v_is_stable(rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_v(rabbitmq))),
{
    always_p_is_stable(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq))));
}

pub open spec fn invariants_since_phase_vi(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq))))
    .and(always(lift_state(helper_invariants::object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ServerConfigMap, rabbitmq))))
    .and(always(lift_state(helper_invariants::object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ServerConfigMap, rabbitmq))))
}

pub proof fn invariants_since_phase_vi_is_stable(rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_vi(rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq));
    stable_and_always_n!(
        tla_forall(a_to_p_1),
        lift_state(helper_invariants::object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(helper_invariants::object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ServerConfigMap, rabbitmq))
    );
}

pub open spec fn invariants_since_phase_vii(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))
}

pub proof fn invariants_since_phase_vii_is_stable(rabbitmq: RabbitmqClusterView)
    ensures valid(stable(invariants_since_phase_vii(rabbitmq))),
{
    always_p_is_stable(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)));
}

pub proof fn lemma_always_for_all_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(RMQCluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())))),
    ensures
        spec.entails(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1))))))),
{
    // TODO (xudong): investigate the performance of this lemma
    // Somehow the reasoning inside the assert forall block below is very slow (takes more than 8 seconds!)
    // I suspect it is related to the precondition of lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state
    let a_to_p = |step: (ActionKind, SubResource)| lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1))));
    assert_by(spec.entails(always(tla_forall(a_to_p))), {
        assert forall |step: (ActionKind, SubResource)| spec.entails(always(#[trigger] a_to_p(step))) by {
            RMQCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1))
            );
        }
        spec_entails_always_tla_forall(spec, a_to_p);
    });
}

pub proof fn sm_spec_entails_all_invariants(rabbitmq: RabbitmqClusterView)
    ensures cluster_spec().entails(derived_invariants_since_beginning(rabbitmq)),
{
    let spec = cluster_spec();
    // Adding two assertions to make the verification faster because all the lemmas below require the two preconditions.
    // And then the verifier doesn't have to infer it every time applying those lemmas.
    assert(spec.entails(lift_state(RMQCluster::init())));
    assert(spec.entails(always(lift_action(RMQCluster::next()))));
    RMQCluster::lemma_always_every_in_flight_msg_has_unique_id(spec);
    RMQCluster::lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec, rabbitmq.object_ref());
    RMQCluster::lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    RMQCluster::lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, rabbitmq.object_ref());
    RMQCluster::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    RMQCluster::lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec);
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq));
    assert_by(spec.entails(always(tla_forall(a_to_p_1))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_1(sub_resource))) by {
            helper_invariants::lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec, sub_resource, rabbitmq);
        }
        spec_entails_always_tla_forall(spec, a_to_p_1);
    });
    RMQCluster::lemma_always_no_pending_req_msg_at_reconcile_state(spec, rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init));

    // Different from other a_to_p_x, we encapsulate a_to_p_2 inside the lemma below because we find its reasoning is
    // surprisingly slow in this context. Encapsulating the reasoning reduces the verification time of this function
    // from more than 40 seconds to 2 seconds.
    let a_to_p_2 = |step: (ActionKind, SubResource)| lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1))));
    lemma_always_for_all_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, rabbitmq);

    let a_to_p_3 = |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq));
    assert_by(spec.entails(always(tla_forall(a_to_p_3))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_3(sub_resource))) by {
            helper_invariants::lemma_always_no_update_status_request_msg_in_flight_of_except_stateful_set(spec, sub_resource, rabbitmq);
        }
        spec_entails_always_tla_forall(spec, a_to_p_3);
    });
    helper_invariants::lemma_always_no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(spec, rabbitmq);
    helper_invariants::lemma_always_the_object_in_reconcile_satisfies_state_validation(spec, rabbitmq.object_ref());
    RMQCluster::lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(spec, rabbitmq.object_ref());
    RMQCluster::lemma_always_key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(spec, rabbitmq.object_ref());
    RMQCluster::lemma_always_key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(spec, rabbitmq.object_ref());
    let a_to_p_4 = |res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, rabbitmq));
    assert_by(spec.entails(always(tla_forall(a_to_p_4))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_4(sub_resource))) by {
            helper_invariants::lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, sub_resource, rabbitmq);
        }
        spec_entails_always_tla_forall(spec, a_to_p_4);
    });
    let a_to_p_5 = |res: SubResource| lift_state(RMQCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, rabbitmq).key));
    assert_by(spec.entails(always(tla_forall(a_to_p_5))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_5(sub_resource))) by {
            RMQCluster::lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, get_request(sub_resource, rabbitmq).key);
        }
        spec_entails_always_tla_forall(spec, a_to_p_5);
    });
    helper_invariants::lemma_always_stateful_set_in_etcd_satisfies_unchangeable(spec, rabbitmq);
    let a_to_p_6 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq));
    assert_by(spec.entails(always(tla_forall(a_to_p_6))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_6(sub_resource))) by {
            helper_invariants::lemma_always_object_in_etcd_satisfies_unchangeable(spec, sub_resource, rabbitmq);
        }
        spec_entails_always_tla_forall(spec, a_to_p_6);
    });

    entails_always_and_n!(
        spec,
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(rabbitmq.object_ref())),
        lift_state(RMQCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(RMQCluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())),
        lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        tla_forall(a_to_p_1),
        lift_state(RMQCluster::no_pending_req_msg_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init))),
        tla_forall(a_to_p_2),
        tla_forall(a_to_p_3),
        lift_state(helper_invariants::no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(rabbitmq)),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(rabbitmq.object_ref())),
        lift_state(RMQCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(rabbitmq.object_ref())),
        tla_forall(a_to_p_4),
        tla_forall(a_to_p_5),
        lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)),
        tla_forall(a_to_p_6)
    );
}

}
