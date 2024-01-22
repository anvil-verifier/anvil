// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::{
    model::reconciler::*,
    proof::{helper_invariants, liveness::terminate, predicate::*, resource::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, daemon_set::*, dynamic::*, owner_reference::*,
    resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub open spec fn assumption_and_invariants_of_all_phases(fb: FluentBitView) -> TempPred<FBCluster> {
    invariants(fb)
    .and(always(lift_state(desired_state_is(fb))))
    .and(invariants_since_phase_i(fb))
    .and(invariants_since_phase_ii(fb))
    .and(invariants_since_phase_iii(fb))
    .and(invariants_since_phase_iv(fb))
    .and(invariants_since_phase_v(fb))
    .and(invariants_since_phase_vi(fb))
    .and(invariants_since_phase_vii(fb))
}

pub open spec fn invariants_since_phase_n(n: nat, fb: FluentBitView) -> TempPred<FBCluster> {
    if n == 0 {
        invariants(fb).and(always(lift_state(desired_state_is(fb))))
    } else if n == 1 {
        invariants_since_phase_i(fb)
    } else if n == 2 {
        invariants_since_phase_ii(fb)
    } else if n == 3 {
        invariants_since_phase_iii(fb)
    } else if n == 4 {
        invariants_since_phase_iv(fb)
    } else if n == 5 {
        invariants_since_phase_v(fb)
    } else if n == 6 {
        invariants_since_phase_vi(fb)
    } else if n == 7 {
        invariants_since_phase_vii(fb)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(n: nat, fb: FluentBitView) -> TempPred<FBCluster>
    decreases n,
{
    if n == 1 {
        invariants(fb).and(always(lift_state(desired_state_is(fb))))
    } else if 2 <= n <= 8 {
        spec_before_phase_n((n-1) as nat, fb).and(invariants_since_phase_n((n-1) as nat, fb))
    } else {
        true_pred()
    }
}

pub proof fn spec_of_previous_phases_entails_eventually_new_invariants(i: nat, fb: FluentBitView)
    requires 1 <= i <= 7,
    ensures spec_before_phase_n(i, fb).entails(true_pred().leads_to(invariants_since_phase_n(i, fb))),
{
    let spec = spec_before_phase_n(i, fb);
    reveal_with_fuel(spec_before_phase_n, 8);
    implies_preserved_by_always_temp(lift_state(desired_state_is(fb)), lift_state(FBCluster::desired_state_is(fb)));
    valid_implies_trans(spec, always(lift_state(desired_state_is(fb))), always(lift_state(FBCluster::desired_state_is(fb))));
    if i == 1 {
        FBCluster::lemma_true_leads_to_crash_always_disabled(spec);
        FBCluster::lemma_true_leads_to_busy_always_disabled(spec);
        FBCluster::lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, fb);
        leads_to_always_combine_n!(
            spec,
            true_pred(),
            lift_state(FBCluster::crash_disabled()),
            lift_state(FBCluster::busy_disabled()),
            lift_state(FBCluster::the_object_in_schedule_has_spec_and_uid_as(fb))
        );
    } else {
        terminate::reconcile_eventually_terminates(spec, fb);
        if i == 2 {
            FBCluster::lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, fb);
        } else if i == 3 {
            helper_invariants::lemma_always_fb_is_well_formed(spec, fb);
            helper_invariants::lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step_forall(spec, fb);
            helper_invariants::lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr_forall(spec, fb);
            let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb));
            let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb));
            leads_to_always_combine_n!(
                spec, true_pred(), tla_forall(a_to_p_1), tla_forall(a_to_p_2)
            );
        } else if i == 4 {
            helper_invariants::lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr_forall(spec, fb);
        } else if i == 5 {
            helper_invariants::lemma_eventually_always_no_delete_resource_request_msg_in_flight_forall(spec, fb);
        } else if i == 6 {
            helper_invariants::lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step_forall(spec, fb);
        } else if i == 7 {
            always_tla_forall_apply(spec, |sub_resource: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb)), SubResource::DaemonSet);
            always_tla_forall_apply(spec, |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb)), SubResource::DaemonSet);
            always_tla_forall_apply(spec, |sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fb)), SubResource::DaemonSet);
            always_tla_forall_apply(spec, |sub_resource: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fb)), SubResource::DaemonSet);
            helper_invariants::lemma_eventually_always_daemon_set_not_exists_or_matches_or_no_more_status_update(spec, fb);
        }
    }
}

pub proof fn assumption_and_invariants_of_all_phases_is_stable(fb: FluentBitView)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(fb))),
        valid(stable(invariants(fb))),
        forall |i: nat|  1 <= i <= 7 ==> valid(stable(#[trigger] spec_before_phase_n(i, fb))),
{
    reveal_with_fuel(spec_before_phase_n, 7);
    invariants_is_stable(fb);
    always_p_is_stable(lift_state(desired_state_is(fb)));
    invariants_since_phase_i_is_stable(fb);
    invariants_since_phase_ii_is_stable(fb);
    invariants_since_phase_iii_is_stable(fb);
    invariants_since_phase_iv_is_stable(fb);
    invariants_since_phase_v_is_stable(fb);
    invariants_since_phase_vi_is_stable(fb);
    invariants_since_phase_vii_is_stable(fb);
    stable_and_n!(
        invariants(fb), always(lift_state(desired_state_is(fb))),
        invariants_since_phase_i(fb), invariants_since_phase_ii(fb), invariants_since_phase_iii(fb),
        invariants_since_phase_iv(fb), invariants_since_phase_v(fb), invariants_since_phase_vi(fb),
        invariants_since_phase_vii(fb)
    );
}

// Next and all the wf conditions.
pub open spec fn next_with_wf() -> TempPred<FBCluster> {
    always(lift_action(FBCluster::next()))
    .and(tla_forall(|input| FBCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| FBCluster::external_api_next().weak_fairness(input)))
    .and(tla_forall(|input| FBCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| FBCluster::schedule_controller_reconcile().weak_fairness(input)))
    .and(tla_forall(|input| FBCluster::builtin_controllers_next().weak_fairness(input)))
    .and(FBCluster::disable_crash().weak_fairness(()))
    .and(FBCluster::disable_transient_failure().weak_fairness(()))
}

pub proof fn next_with_wf_is_stable()
    ensures valid(stable(next_with_wf())),
{
    always_p_is_stable(lift_action(FBCluster::next()));
    FBCluster::tla_forall_action_weak_fairness_is_stable(FBCluster::kubernetes_api_next());
    FBCluster::tla_forall_action_weak_fairness_is_stable(FBCluster::external_api_next());
    FBCluster::tla_forall_action_weak_fairness_is_stable(FBCluster::controller_next());
    FBCluster::tla_forall_action_weak_fairness_is_stable(FBCluster::schedule_controller_reconcile());
    FBCluster::tla_forall_action_weak_fairness_is_stable(FBCluster::builtin_controllers_next());
    FBCluster::action_weak_fairness_is_stable(FBCluster::disable_crash());
    FBCluster::action_weak_fairness_is_stable(FBCluster::disable_transient_failure());
    stable_and_n!(
        always(lift_action(FBCluster::next())),
        tla_forall(|input| FBCluster::kubernetes_api_next().weak_fairness(input)),
        tla_forall(|input| FBCluster::external_api_next().weak_fairness(input)),
        tla_forall(|input| FBCluster::controller_next().weak_fairness(input)),
        tla_forall(|input| FBCluster::schedule_controller_reconcile().weak_fairness(input)),
        tla_forall(|input| FBCluster::builtin_controllers_next().weak_fairness(input)),
        FBCluster::disable_crash().weak_fairness(()),
        FBCluster::disable_transient_failure().weak_fairness(())
    );
}

/// This predicate combines all the possible actions (next), weak fairness and invariants that hold throughout the execution.
/// We name it invariants here because these predicates are never violated, thus they can all be seen as some kind of invariants.
///
/// The final goal of our proof is to show init /\ invariants |= []desired_state_is(cr) ~> []current_state_matches(cr).
/// init /\ invariants is equivalent to init /\ next /\ weak_fairness, so we get cluster_spec() |= []desired_state_is(cr) ~> []current_state_matches(cr).
pub open spec fn invariants(fb: FluentBitView) -> TempPred<FBCluster> {
    next_with_wf().and(derived_invariants_since_beginning(fb))
}

pub proof fn invariants_is_stable(fb: FluentBitView)
    ensures valid(stable(invariants(fb))),
{
    next_with_wf_is_stable();
    derived_invariants_since_beginning_is_stable(fb);
    stable_and_n!(
        next_with_wf(),
        derived_invariants_since_beginning(fb)
    );
}

// The safety invariants that are required to prove liveness.
pub open spec fn derived_invariants_since_beginning(fb: FluentBitView) -> TempPred<FBCluster> {
    always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(FBCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(fb.object_ref()))))
    .and(always(lift_state(FBCluster::object_in_ok_get_response_has_smaller_rv_than_etcd())))
    .and(always(lift_state(FBCluster::pending_req_of_key_is_unique_with_unique_id(fb.object_ref()))))
    .and(always(lift_state(FBCluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(FBCluster::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(FBCluster::each_scheduled_object_has_consistent_key_and_valid_metadata())))
    .and(always(lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fb)))))
    .and(always(lift_state(FBCluster::no_pending_req_msg_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::Init)))))
    .and(always(lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterGetSecret)))))
    .and(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(step.0, step.1)))))))
    .and(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_daemon_set(res, fb)))))
    .and(always(lift_state(helper_invariants::no_update_status_request_msg_not_from_bc_in_flight_of_daemon_set(fb))))
    .and(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fb.object_ref()))))
    .and(always(lift_state(FBCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(fb.object_ref()))))
    .and(always(lift_state(FBCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(fb.object_ref()))))
    .and(always(lift_state(FBCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(fb.object_ref()))))
    .and(always(tla_forall(|res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, fb)))))
    .and(always(tla_forall(|res: SubResource| lift_state(FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, fb).key)))))
    .and(always(lift_state(helper_invariants::daemon_set_in_etcd_satisfies_unchangeable(fb))))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fb)))))
}

pub proof fn derived_invariants_since_beginning_is_stable(fb: FluentBitView)
    ensures valid(stable(derived_invariants_since_beginning(fb))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fb));
    let a_to_p_2 = |step: (ActionKind, SubResource)| lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(step.0, step.1))));
    let a_to_p_3 = |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_daemon_set(res, fb));
    let a_to_p_4 = |res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, fb));
    let a_to_p_5 = |res: SubResource| lift_state(FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, fb).key));
    let a_to_p_6 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fb));
    stable_and_always_n!(
        lift_state(FBCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(fb.object_ref())),
        lift_state(FBCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(FBCluster::pending_req_of_key_is_unique_with_unique_id(fb.object_ref())),
        lift_state(FBCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed()),
        lift_state(FBCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        tla_forall(a_to_p_1),
        lift_state(FBCluster::no_pending_req_msg_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::Init))),
        lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterGetSecret))),
        tla_forall(a_to_p_2),
        tla_forall(a_to_p_3),
        lift_state(helper_invariants::no_update_status_request_msg_not_from_bc_in_flight_of_daemon_set(fb)),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fb.object_ref())),
        lift_state(FBCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(fb.object_ref())),
        lift_state(FBCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(fb.object_ref())),
        lift_state(FBCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(fb.object_ref())),
        tla_forall(a_to_p_4),
        tla_forall(a_to_p_5),
        lift_state(helper_invariants::daemon_set_in_etcd_satisfies_unchangeable(fb)),
        tla_forall(a_to_p_6)
    );
}

/// The first notable phase comes when crash and k8s busy are always disabled and the object in schedule always has the same
/// spec and uid as the cr we provide.
///
/// Note that don't try to find any connections between those invariants -- they are put together because they don't have to
/// wait for another of them to first be satisfied.
pub open spec fn invariants_since_phase_i(fb: FluentBitView) -> TempPred<FBCluster> {
    always(lift_state(FBCluster::crash_disabled()))
    .and(always(lift_state(FBCluster::busy_disabled())))
    .and(always(lift_state(FBCluster::the_object_in_schedule_has_spec_and_uid_as(fb))))
}

pub proof fn invariants_since_phase_i_is_stable(fb: FluentBitView)
    ensures valid(stable(invariants_since_phase_i(fb))),
{
    stable_and_always_n!(
        lift_state(FBCluster::crash_disabled()),
        lift_state(FBCluster::busy_disabled()),
        lift_state(FBCluster::the_object_in_schedule_has_spec_and_uid_as(fb))
    );
}

/// For now, phase II only contains one invariant, which is the object in reconcile has the same spec and uid as fb.
///
/// It is alone because it relies on the invariant the_object_in_schedule_has_spec_and_uid_as (in phase I) and every invariant
/// in phase III relies on it.
pub open spec fn invariants_since_phase_ii(fb: FluentBitView) -> TempPred<FBCluster> {
    always(lift_state(FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)))
}

pub proof fn invariants_since_phase_ii_is_stable(fb: FluentBitView)
    ensures valid(stable(invariants_since_phase_ii(fb))),
{
    always_p_is_stable(lift_state(FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)));
}

pub open spec fn invariants_since_phase_iii(fb: FluentBitView) -> TempPred<FBCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb))))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb)))))
}

pub proof fn invariants_since_phase_iii_is_stable(fb: FluentBitView)
    ensures valid(stable(invariants_since_phase_iii(fb))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb));
    let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb));
    stable_and_always_n!(tla_forall(a_to_p_1), tla_forall(a_to_p_2));
}

/// Invariants since this phase ensure that certain objects only have owner references that point to current cr.
/// To have these invariants, we first need the invariant that evert create/update request make/change the object in the
/// expected way.
pub open spec fn invariants_since_phase_iv(fb: FluentBitView) -> TempPred<FBCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb))))
}

pub proof fn invariants_since_phase_iv_is_stable(fb: FluentBitView)
    ensures valid(stable(invariants_since_phase_iv(fb))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb));
    always_p_is_stable(tla_forall(a_to_p_1));
}

/// Invariants since phase V rely on the invariants since phase IV. When the objects starts to always have owner reference
/// pointing to current cr, it will never be recycled by the garbage collector. Plus, the reconciler itself never tries to
/// delete this object, so we can have the invariants saying that no delete request messages will be in flight.
pub open spec fn invariants_since_phase_v(fb: FluentBitView) -> TempPred<FBCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fb))))
}

pub proof fn invariants_since_phase_v_is_stable(fb: FluentBitView)
    ensures valid(stable(invariants_since_phase_v(fb))),
{
    always_p_is_stable(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fb))));
}

pub open spec fn invariants_since_phase_vi(fb: FluentBitView) -> TempPred<FBCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fb))))
}

pub proof fn invariants_since_phase_vi_is_stable(fb: FluentBitView)
    ensures valid(stable(invariants_since_phase_vi(fb))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fb));
    always_p_is_stable(tla_forall(a_to_p_1));
}

pub open spec fn invariants_since_phase_vii(fb: FluentBitView) -> TempPred<FBCluster> {
    always(lift_state(helper_invariants::daemon_set_not_exists_or_matches_or_no_more_status_update(fb)))
}

pub proof fn invariants_since_phase_vii_is_stable(fb: FluentBitView)
    ensures valid(stable(invariants_since_phase_vii(fb))),
{
    always_p_is_stable(lift_state(helper_invariants::daemon_set_not_exists_or_matches_or_no_more_status_update(fb)));
}

pub proof fn lemma_always_for_all_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(always(lift_state(FBCluster::pending_req_of_key_is_unique_with_unique_id(fb.object_ref())))),
    ensures
        spec.entails(always(lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterGetSecret))))),
        spec.entails(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(step.0, step.1))))))),
{

    FBCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterGetSecret));

    let a_to_p = |step: (ActionKind, SubResource)| lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(step.0, step.1))));
    assert_by(spec.entails(always(tla_forall(a_to_p))), {
        assert forall |step: (ActionKind, SubResource)| spec.entails(always(#[trigger] a_to_p(step))) by {
            FBCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                spec, fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(step.0, step.1))
            );
        }
        spec_entails_always_tla_forall(spec, a_to_p);
    });
}

pub proof fn sm_spec_entails_all_invariants(fb: FluentBitView)
    ensures cluster_spec().entails(derived_invariants_since_beginning(fb)),
{
    let spec = cluster_spec();
    // Adding two assertions to make the verification faster because all the lemmas below require the two preconditions.
    // And then the verifier doesn't have to infer it every time applying those lemmas.
    assert(spec.entails(lift_state(FBCluster::init())));
    assert(spec.entails(always(lift_action(FBCluster::next()))));
    FBCluster::lemma_always_every_in_flight_msg_has_unique_id(spec);
    FBCluster::lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec, fb.object_ref());
    FBCluster::lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    FBCluster::lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, fb.object_ref());
    FBCluster::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    FBCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    FBCluster::lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec);
    FBCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fb));
    assert_by(spec.entails(always(tla_forall(a_to_p_1))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_1(sub_resource))) by {
            helper_invariants::lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec, sub_resource, fb);
        }
        spec_entails_always_tla_forall(spec, a_to_p_1);
    });
    FBCluster::lemma_always_no_pending_req_msg_at_reconcile_state(spec, fb.object_ref(), at_step_closure(FluentBitReconcileStep::Init));

    let a_to_p_2 = |step: (ActionKind, SubResource)| lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterKRequestStep(step.0, step.1))));
    lemma_always_for_all_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, fb);

    let a_to_p_3 = |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_daemon_set(res, fb));
    assert_by(spec.entails(always(tla_forall(a_to_p_3))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_3(sub_resource))) by {
            helper_invariants::lemma_always_no_update_status_request_msg_in_flight_of_except_daemon_set(spec, sub_resource, fb);
        }
        spec_entails_always_tla_forall(spec, a_to_p_3);
    });
    helper_invariants::lemma_always_no_update_status_request_msg_not_from_bc_in_flight_of_daemon_set(spec, fb);
    helper_invariants::lemma_always_the_object_in_reconcile_satisfies_state_validation(spec, fb.object_ref());
    FBCluster::lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(spec, fb.object_ref());
    FBCluster::lemma_always_key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(spec, fb.object_ref());
    FBCluster::lemma_always_key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(spec, fb.object_ref());
    let a_to_p_4 = |res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, fb));
    assert_by(spec.entails(always(tla_forall(a_to_p_4))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_4(sub_resource))) by {
            helper_invariants::lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, sub_resource, fb);
        }
        spec_entails_always_tla_forall(spec, a_to_p_4);
    });
    let a_to_p_5 = |res: SubResource| lift_state(FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, fb).key));
    assert_by(spec.entails(always(tla_forall(a_to_p_5))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_5(sub_resource))) by {
            FBCluster::lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, get_request(sub_resource, fb).key);
        }
        spec_entails_always_tla_forall(spec, a_to_p_5);
    });
    helper_invariants::lemma_always_daemon_set_in_etcd_satisfies_unchangeable(spec, fb);
    let a_to_p_6 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fb));
    assert_by(spec.entails(always(tla_forall(a_to_p_6))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_6(sub_resource))) by {
            helper_invariants::lemma_always_object_in_etcd_satisfies_unchangeable(spec, sub_resource, fb);
        }
        spec_entails_always_tla_forall(spec, a_to_p_6);
    });

    entails_always_and_n!(
        spec,
        lift_state(FBCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(fb.object_ref())),
        lift_state(FBCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(FBCluster::pending_req_of_key_is_unique_with_unique_id(fb.object_ref())),
        lift_state(FBCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed()),
        lift_state(FBCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        tla_forall(a_to_p_1),
        lift_state(FBCluster::no_pending_req_msg_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::Init))),
        lift_state(FBCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fb.object_ref(), at_step_closure(FluentBitReconcileStep::AfterGetSecret))),
        tla_forall(a_to_p_2),
        tla_forall(a_to_p_3),
        lift_state(helper_invariants::no_update_status_request_msg_not_from_bc_in_flight_of_daemon_set(fb)),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fb.object_ref())),
        lift_state(FBCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(fb.object_ref())),
        lift_state(FBCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(fb.object_ref())),
        lift_state(FBCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(fb.object_ref())),
        tla_forall(a_to_p_4),
        tla_forall(a_to_p_5),
        lift_state(helper_invariants::daemon_set_in_etcd_satisfies_unchangeable(fb)),
        tla_forall(a_to_p_6)
    );
}

}
