// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit_config::{
    model::reconciler::*,
    proof::{helper_invariants, liveness::terminate, predicate::*, resource::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
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
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub open spec fn assumption_and_invariants_of_all_phases(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    invariants(fbc)
    .and(always(lift_state(desired_state_is(fbc))))
    .and(invariants_since_phase_i(fbc))
    .and(invariants_since_phase_ii(fbc))
    .and(invariants_since_phase_iii(fbc))
    .and(invariants_since_phase_iv(fbc))
    .and(invariants_since_phase_v(fbc))
    .and(invariants_since_phase_vi(fbc))
}

pub open spec fn invariants_since_phase_n(n: nat, fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    if n == 0 {
        invariants(fbc).and(always(lift_state(desired_state_is(fbc))))
    } else if n == 1 {
        invariants_since_phase_i(fbc)
    } else if n == 2 {
        invariants_since_phase_ii(fbc)
    } else if n == 3 {
        invariants_since_phase_iii(fbc)
    } else if n == 4 {
        invariants_since_phase_iv(fbc)
    } else if n == 5 {
        invariants_since_phase_v(fbc)
    } else if n == 6 {
        invariants_since_phase_vi(fbc)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(n: nat, fbc: FluentBitConfigView) -> TempPred<FBCCluster>
    decreases n,
{
    if n == 1 {
        invariants(fbc).and(always(lift_state(desired_state_is(fbc))))
    } else if 2 <= n <= 7 {
        spec_before_phase_n((n-1) as nat, fbc).and(invariants_since_phase_n((n-1) as nat, fbc))
    } else {
        true_pred()
    }
}

pub proof fn spec_of_previous_phases_entails_eventually_new_invariants(i: nat, fbc: FluentBitConfigView)
    requires 1 <= i <= 6,
    ensures spec_before_phase_n(i, fbc).entails(true_pred().leads_to(invariants_since_phase_n(i, fbc))),
{
    let spec = spec_before_phase_n(i, fbc);
    reveal_with_fuel(spec_before_phase_n, 8);
    if i == 1 {
        FBCCluster::lemma_true_leads_to_crash_always_disabled(spec);
        FBCCluster::lemma_true_leads_to_busy_always_disabled(spec);
        FBCCluster::lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, fbc);
        leads_to_always_combine_n!(
            spec,
            true_pred(),
            lift_state(FBCCluster::crash_disabled()),
            lift_state(FBCCluster::busy_disabled()),
            lift_state(FBCCluster::the_object_in_schedule_has_spec_and_uid_as(fbc))
        );
    } else {
        terminate::reconcile_eventually_terminates(spec, fbc);
        if i == 2 {
            FBCCluster::lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, fbc);
        } else if i == 3 {
            helper_invariants::lemma_always_fbc_is_well_formed(spec, fbc);
            helper_invariants::lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step_forall(spec, fbc);
            helper_invariants::lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr_forall(spec, fbc);
            let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc));
            let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fbc));
            leads_to_always_combine_n!(
                spec, true_pred(), tla_forall(a_to_p_1), tla_forall(a_to_p_2)
            );
        } else if i == 4 {
            helper_invariants::lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr_forall(spec, fbc);
        } else if i == 5 {
            helper_invariants::lemma_eventually_always_no_delete_resource_request_msg_in_flight_forall(spec, fbc);
        } else if i == 6 {
            helper_invariants::lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step_forall(spec, fbc);
        }
    }
}

pub proof fn assumption_and_invariants_of_all_phases_is_stable(fbc: FluentBitConfigView)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(fbc))),
        valid(stable(invariants(fbc))),
        forall |i: nat|  1 <= i <= 6 ==> valid(stable(#[trigger] spec_before_phase_n(i, fbc))),
{
    reveal_with_fuel(spec_before_phase_n, 6);
    invariants_is_stable(fbc);
    always_p_is_stable(lift_state(desired_state_is(fbc)));
    invariants_since_phase_i_is_stable(fbc);
    invariants_since_phase_ii_is_stable(fbc);
    invariants_since_phase_iii_is_stable(fbc);
    invariants_since_phase_iv_is_stable(fbc);
    invariants_since_phase_v_is_stable(fbc);
    invariants_since_phase_vi_is_stable(fbc);
    stable_and_n!(
        invariants(fbc), always(lift_state(desired_state_is(fbc))),
        invariants_since_phase_i(fbc), invariants_since_phase_ii(fbc), invariants_since_phase_iii(fbc),
        invariants_since_phase_iv(fbc), invariants_since_phase_v(fbc), invariants_since_phase_vi(fbc)
    );
}

// Next and all the wf conditions.
pub open spec fn next_with_wf() -> TempPred<FBCCluster> {
    always(lift_action(FBCCluster::next()))
    .and(tla_forall(|input| FBCCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| FBCCluster::external_api_next().weak_fairness(input)))
    .and(tla_forall(|input| FBCCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| FBCCluster::schedule_controller_reconcile().weak_fairness(input)))
    .and(tla_forall(|input| FBCCluster::builtin_controllers_next().weak_fairness(input)))
    .and(FBCCluster::disable_crash().weak_fairness(()))
    .and(FBCCluster::disable_transient_failure().weak_fairness(()))
}

pub proof fn next_with_wf_is_stable()
    ensures valid(stable(next_with_wf())),
{
    always_p_is_stable(lift_action(FBCCluster::next()));
    FBCCluster::tla_forall_action_weak_fairness_is_stable(FBCCluster::kubernetes_api_next());
    FBCCluster::tla_forall_action_weak_fairness_is_stable(FBCCluster::external_api_next());
    FBCCluster::tla_forall_action_weak_fairness_is_stable(FBCCluster::controller_next());
    FBCCluster::tla_forall_action_weak_fairness_is_stable(FBCCluster::schedule_controller_reconcile());
    FBCCluster::tla_forall_action_weak_fairness_is_stable(FBCCluster::builtin_controllers_next());
    FBCCluster::action_weak_fairness_is_stable(FBCCluster::disable_crash());
    FBCCluster::action_weak_fairness_is_stable(FBCCluster::disable_transient_failure());
    stable_and_n!(
        always(lift_action(FBCCluster::next())),
        tla_forall(|input| FBCCluster::kubernetes_api_next().weak_fairness(input)),
        tla_forall(|input| FBCCluster::external_api_next().weak_fairness(input)),
        tla_forall(|input| FBCCluster::controller_next().weak_fairness(input)),
        tla_forall(|input| FBCCluster::schedule_controller_reconcile().weak_fairness(input)),
        tla_forall(|input| FBCCluster::builtin_controllers_next().weak_fairness(input)),
        FBCCluster::disable_crash().weak_fairness(()),
        FBCCluster::disable_transient_failure().weak_fairness(())
    );
}

/// This predicate combines all the possible actions (next), weak fairness and invariants that hold throughout the execution.
/// We name it invariants here because these predicates are never violated, thus they can all be seen as some kind of invariants.
///
/// The final goal of our proof is to show init /\ invariants |= []desired_state_is(cr) ~> []current_state_matches(cr).
/// init /\ invariants is equivalent to init /\ next /\ weak_fairness, so we get cluster_spec() |= []desired_state_is(cr) ~> []current_state_matches(cr).
pub open spec fn invariants(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    next_with_wf().and(derived_invariants_since_beginning(fbc))
}

pub proof fn invariants_is_stable(fbc: FluentBitConfigView)
    ensures valid(stable(invariants(fbc))),
{
    next_with_wf_is_stable();
    derived_invariants_since_beginning_is_stable(fbc);
    stable_and_n!(
        next_with_wf(),
        derived_invariants_since_beginning(fbc)
    );
}

// The safety invariants that are required to prove liveness.
pub open spec fn derived_invariants_since_beginning(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(FBCCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(fbc.object_ref()))))
    .and(always(lift_state(FBCCluster::object_in_ok_get_response_has_smaller_rv_than_etcd())))
    .and(always(lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref()))))
    .and(always(lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(FBCCluster::each_scheduled_object_has_consistent_key_and_valid_metadata())))
    .and(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)))))
    .and(always(lift_state(FBCCluster::no_pending_req_msg_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::Init)))))
    .and(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1)))))))
    .and(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight(res, fbc)))))
    .and(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref()))))
    .and(always(lift_state(FBCCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(fbc.object_ref()))))
    .and(always(lift_state(FBCCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(fbc.object_ref()))))
    .and(always(lift_state(FBCCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(fbc.object_ref()))))
    .and(always(tla_forall(|res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, fbc)))))
    .and(always(tla_forall(|res: SubResource| lift_state(FBCCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, fbc).key)))))
}

pub proof fn derived_invariants_since_beginning_is_stable(fbc: FluentBitConfigView)
    ensures valid(stable(derived_invariants_since_beginning(fbc))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc));
    let a_to_p_2 = |step: (ActionKind, SubResource)| lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1))));
    let a_to_p_3 = |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight(res, fbc));
    let a_to_p_4 = |res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, fbc));
    let a_to_p_5 = |res: SubResource| lift_state(FBCCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, fbc).key));
    stable_and_always_n!(
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(fbc.object_ref())),
        lift_state(FBCCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())),
        lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed()),
        lift_state(FBCCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        tla_forall(a_to_p_1),
        lift_state(FBCCluster::no_pending_req_msg_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::Init))),
        tla_forall(a_to_p_2),
        tla_forall(a_to_p_3),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref())),
        lift_state(FBCCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(fbc.object_ref())),
        lift_state(FBCCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(fbc.object_ref())),
        lift_state(FBCCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(fbc.object_ref())),
        tla_forall(a_to_p_4),
        tla_forall(a_to_p_5)
    );
}

/// The first notable phase comes when crash and k8s busy are always disabled and the object in schedule always has the same
/// spec and uid as the cr we provide.
///
/// Note that don't try to find any connections between those invariants -- they are put together because they don't have to
/// wait for another of them to first be satisfied.
pub open spec fn invariants_since_phase_i(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    always(lift_state(FBCCluster::crash_disabled()))
    .and(always(lift_state(FBCCluster::busy_disabled())))
    .and(always(lift_state(FBCCluster::the_object_in_schedule_has_spec_and_uid_as(fbc))))
}

pub proof fn invariants_since_phase_i_is_stable(fbc: FluentBitConfigView)
    ensures valid(stable(invariants_since_phase_i(fbc))),
{
    stable_and_always_n!(
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::the_object_in_schedule_has_spec_and_uid_as(fbc))
    );
}

/// For now, phase II only contains one invariant, which is the object in reconcile has the same spec and uid as fbc.
///
/// It is alone because it relies on the invariant the_object_in_schedule_has_spec_and_uid_as (in phase I) and every invariant
/// in phase III relies on it.
pub open spec fn invariants_since_phase_ii(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    always(lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)))
}

pub proof fn invariants_since_phase_ii_is_stable(fbc: FluentBitConfigView)
    ensures valid(stable(invariants_since_phase_ii(fbc))),
{
    always_p_is_stable(lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)));
}

pub open spec fn invariants_since_phase_iii(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc))))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fbc)))))
}

pub proof fn invariants_since_phase_iii_is_stable(fbc: FluentBitConfigView)
    ensures valid(stable(invariants_since_phase_iii(fbc))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc));
    let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fbc));
    stable_and_always_n!(tla_forall(a_to_p_1), tla_forall(a_to_p_2));
}

/// Invariants since this phase ensure that certain objects only have owner references that point to current cr.
/// To have these invariants, we first need the invariant that evert create/update request make/change the object in the
/// expected way.
pub open spec fn invariants_since_phase_iv(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc))))
}

pub proof fn invariants_since_phase_iv_is_stable(fbc: FluentBitConfigView)
    ensures valid(stable(invariants_since_phase_iv(fbc))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc));
    always_p_is_stable(tla_forall(a_to_p_1));
}

/// Invariants since phase V rely on the invariants since phase IV. When the objects starts to always have owner reference
/// pointing to current cr, it will never be recycled by the garbage collector. Plus, the reconciler itself never tries to
/// delete this object, so we can have the invariants saying that no delete request messages will be in flight.
pub open spec fn invariants_since_phase_v(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc))))
}

pub proof fn invariants_since_phase_v_is_stable(fbc: FluentBitConfigView)
    ensures valid(stable(invariants_since_phase_v(fbc))),
{
    always_p_is_stable(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc))));
}

pub open spec fn invariants_since_phase_vi(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc))))
}

pub proof fn invariants_since_phase_vi_is_stable(fbc: FluentBitConfigView)
    ensures valid(stable(invariants_since_phase_vi(fbc))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc));
    always_p_is_stable(tla_forall(a_to_p_1));
}

pub proof fn lemma_always_for_all_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(lift_state(FBCCluster::init())),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(always(lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())))),
    ensures spec.entails(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1))))))),
{
    let a_to_p = |step: (ActionKind, SubResource)| lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1))));
    assert_by(spec.entails(always(tla_forall(a_to_p))), {
        assert forall |step: (ActionKind, SubResource)| spec.entails(always(#[trigger] a_to_p(step))) by {
            FBCCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                spec, fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1))
            );
        }
        spec_entails_always_tla_forall(spec, a_to_p);
    });
}

pub proof fn sm_spec_entails_all_invariants(fbc: FluentBitConfigView)
    ensures cluster_spec().entails(derived_invariants_since_beginning(fbc)),
{
    let spec = cluster_spec();
    // Adding two assertions to make the verification faster because all the lemmas below require the two preconditions.
    // And then the verifier doesn't have to infer it every time applying those lemmas.
    assert(spec.entails(lift_state(FBCCluster::init())));
    assert(spec.entails(always(lift_action(FBCCluster::next()))));
    FBCCluster::lemma_always_every_in_flight_msg_has_unique_id(spec);
    FBCCluster::lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec, fbc.object_ref());
    FBCCluster::lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    FBCCluster::lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, fbc.object_ref());
    FBCCluster::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    FBCCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    FBCCluster::lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec);
    FBCCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc));
    assert_by(spec.entails(always(tla_forall(a_to_p_1))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_1(sub_resource))) by {
            helper_invariants::lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec, sub_resource, fbc);
        }
        spec_entails_always_tla_forall(spec, a_to_p_1);
    });
    FBCCluster::lemma_always_no_pending_req_msg_at_reconcile_state(spec, fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::Init));

    let a_to_p_2 = |step: (ActionKind, SubResource)| lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1))));
    lemma_always_for_all_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, fbc);

    let a_to_p_3 = |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight(res, fbc));
    assert_by(spec.entails(always(tla_forall(a_to_p_3))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_3(sub_resource))) by {
            helper_invariants::lemma_always_no_update_status_request_msg_in_flight(spec, sub_resource, fbc);
        }
        spec_entails_always_tla_forall(spec, a_to_p_3);
    });
    helper_invariants::lemma_always_the_object_in_reconcile_satisfies_state_validation(spec, fbc.object_ref());
    FBCCluster::lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(spec, fbc.object_ref());
    FBCCluster::lemma_always_key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(spec, fbc.object_ref());
    FBCCluster::lemma_always_key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(spec, fbc.object_ref());
    let a_to_p_4 = |res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, fbc));
    assert_by(spec.entails(always(tla_forall(a_to_p_4))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_4(sub_resource))) by {
            helper_invariants::lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, sub_resource, fbc);
        }
        spec_entails_always_tla_forall(spec, a_to_p_4);
    });
    let a_to_p_5 = |res: SubResource| lift_state(FBCCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, fbc).key));
    assert_by(spec.entails(always(tla_forall(a_to_p_5))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_5(sub_resource))) by {
            FBCCluster::lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, get_request(sub_resource, fbc).key);
        }
        spec_entails_always_tla_forall(spec, a_to_p_5);
    });

    entails_always_and_n!(
        spec,
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(fbc.object_ref())),
        lift_state(FBCCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())),
        lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed()),
        lift_state(FBCCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        tla_forall(a_to_p_1),
        lift_state(FBCCluster::no_pending_req_msg_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::Init))),
        tla_forall(a_to_p_2),
        tla_forall(a_to_p_3),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref())),
        lift_state(FBCCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(fbc.object_ref())),
        lift_state(FBCCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(fbc.object_ref())),
        lift_state(FBCCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(fbc.object_ref())),
        tla_forall(a_to_p_4),
        tla_forall(a_to_p_5)
    );
}

}
