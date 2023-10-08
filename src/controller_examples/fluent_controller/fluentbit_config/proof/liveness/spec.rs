// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit_config::{
    common::*,
    proof::{helper_invariants, predicate::*, resource::*},
    spec::{reconciler::*, types::*},
};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub open spec fn desired_state_is(fbc: FluentBitConfigView) -> StatePred<FBCCluster>
    recommends
        fbc.well_formed(),
{
    |s: FBCCluster| FBCCluster::desired_state_is(fbc)(s)
}

pub open spec fn assumption_and_invariants_of_all_phases(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    invariants(fbc)
    .and(always(lift_state(desired_state_is(fbc))))
    .and(invariants_since_phase_i(fbc))
    .and(invariants_since_phase_ii(fbc))
    .and(invariants_since_phase_iii(fbc))
    .and(invariants_since_phase_iv(fbc))
    .and(invariants_since_phase_v(fbc))
}

pub proof fn assumption_and_invariants_of_all_phases_is_stable(fbc: FluentBitConfigView)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(fbc))),
{
    invariants_is_stable(fbc);
    always_p_is_stable(lift_state(desired_state_is(fbc)));
    invariants_since_phase_i_is_stable(fbc);
    invariants_since_phase_ii_is_stable(fbc);
    invariants_since_phase_iii_is_stable(fbc);
    invariants_since_phase_iv_is_stable(fbc);
    invariants_since_phase_v_is_stable(fbc);
    stable_and_n!(
        invariants(fbc), always(lift_state(desired_state_is(fbc))),
        invariants_since_phase_i(fbc), invariants_since_phase_ii(fbc), invariants_since_phase_iii(fbc),
        invariants_since_phase_iv(fbc), invariants_since_phase_v(fbc)
    );
}

// Next and all the wf conditions.
pub open spec fn next_with_wf() -> TempPred<FBCCluster> {
    always(lift_action(FBCCluster::next()))
    .and(tla_forall(|input| FBCCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| FBCCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| FBCCluster::schedule_controller_reconcile().weak_fairness(input)))
    .and(tla_forall(|input| FBCCluster::builtin_controllers_next().weak_fairness(input)))
    .and(FBCCluster::disable_crash().weak_fairness(()))
    .and(FBCCluster::disable_transient_failure().weak_fairness(()))
}

pub proof fn next_with_wf_is_stable()
    ensures
        valid(stable(next_with_wf())),
{
    always_p_is_stable(lift_action(FBCCluster::next()));
    FBCCluster::tla_forall_action_weak_fairness_is_stable(FBCCluster::kubernetes_api_next());
    FBCCluster::tla_forall_action_weak_fairness_is_stable(FBCCluster::controller_next());
    FBCCluster::tla_forall_action_weak_fairness_is_stable(FBCCluster::schedule_controller_reconcile());
    FBCCluster::tla_forall_action_weak_fairness_is_stable(FBCCluster::builtin_controllers_next());
    FBCCluster::action_weak_fairness_is_stable(FBCCluster::disable_crash());
    FBCCluster::action_weak_fairness_is_stable(FBCCluster::disable_transient_failure());
    stable_and_n!(
        always(lift_action(FBCCluster::next())),
        tla_forall(|input| FBCCluster::kubernetes_api_next().weak_fairness(input)),
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
    next_with_wf()
    .and(derived_invariants_since_beginning(fbc))
}

pub proof fn invariants_is_stable(fbc: FluentBitConfigView)
    ensures
        valid(stable(invariants(fbc))),
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
    .and(always(lift_state(FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref()))))
    .and(always(lift_state(FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref()))))
    .and(always(lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(FBCCluster::each_scheduled_object_has_consistent_key_and_valid_metadata())))
    .and(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())))
    .and(tla_forall(|sub_resource: SubResource| always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc)))))
    .and(always(lift_state(FBCCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::Init)))))
    .and(tla_forall(|step: (ActionKind, SubResource)| always(lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1)))))))
    .and(tla_forall(|res: SubResource| always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(res, fbc).key)))))
}

pub proof fn derived_invariants_since_beginning_is_stable(fbc: FluentBitConfigView)
    ensures
        valid(stable(derived_invariants_since_beginning(fbc))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc));
    tla_forall_always_equality_variant::<FBCCluster, SubResource>(
        |sub_resource: SubResource| always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc))), a_to_p_1
    );
    let a_to_p_2 = |step: (ActionKind, SubResource)| lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1))));
    tla_forall_always_equality_variant::<FBCCluster, (ActionKind, SubResource)>(
        |step: (ActionKind, SubResource)| always(lift_state(FBCCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::AfterKRequestStep(step.0, step.1))))), a_to_p_2
    );
    let a_to_p_3 = |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(res, fbc).key));
    tla_forall_always_equality_variant::<FBCCluster, SubResource>(
        |res: SubResource| always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(res, fbc).key))), a_to_p_3
    );
    stable_and_always_n!(
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())),
        lift_state(FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())),
        lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed()),
        lift_state(FBCCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        tla_forall(a_to_p_1),
        lift_state(FBCCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(fbc.object_ref(), at_step_closure(FluentBitConfigReconcileStep::Init))),
        tla_forall(a_to_p_2),
        tla_forall(a_to_p_3)
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
    ensures
        valid(stable(invariants_since_phase_i(fbc))),
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
    .and(always(lift_state(helper_invariants::triggering_cr_satisfies_state_validation())))
}

pub proof fn invariants_since_phase_ii_is_stable(fbc: FluentBitConfigView)
    ensures
        valid(stable(invariants_since_phase_ii(fbc))),
{
    stable_and_always_n!(
        lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)),
        lift_state(helper_invariants::triggering_cr_satisfies_state_validation())
    );
}

/// After we know that the spec and uid of object in reconcile, we can obtain the following invariants about messages. This is
/// because the create and update request messages are derived from the custom resource object in reconcile (i.e, triggering_cr).
pub open spec fn invariants_since_phase_iii(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    tla_forall(|sub_resource: SubResource| always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc))))
    .and(tla_forall(|sub_resource: SubResource| always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))))
}

pub proof fn invariants_since_phase_iii_is_stable(fbc: FluentBitConfigView)
    ensures
        valid(stable(invariants_since_phase_iii(fbc))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc));
    tla_forall_always_equality_variant::<FBCCluster, SubResource>(
        |sub_resource: SubResource| always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc))), a_to_p_1
    );
    let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc));
    tla_forall_always_equality_variant::<FBCCluster, SubResource>(
        |sub_resource: SubResource| always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc))), a_to_p_2
    );
    stable_and_always_n!(tla_forall(a_to_p_1), tla_forall(a_to_p_2));
}

// TODO: create/update request only point to current cr

/// Invariants since this phase ensure that certain objects only have owner references that point to current cr.
/// To have these invariants, we first need the invariant that evert create/update request make/change the object in the
/// expected way.
pub open spec fn invariants_since_phase_iv(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    tla_forall(|sub_resource: SubResource| always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, fbc).key, fbc))))
}

pub proof fn invariants_since_phase_iv_is_stable(fbc: FluentBitConfigView)
    ensures
        valid(stable(invariants_since_phase_iv(fbc))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, fbc).key, fbc));
    tla_forall_always_equality_variant::<FBCCluster, SubResource>(
        |sub_resource: SubResource| always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, fbc).key, fbc))), a_to_p_1
    );
    always_p_is_stable(tla_forall(a_to_p_1));
}

/// Invariants since phase V rely on the invariants since phase IV. When the objects starts to always have owner reference
/// pointing to current cr, it will never be recycled by the garbage collector. Plus, the reconciler itself never tries to
/// delete this object, so we can have the invariants saying that no delete request messages will be in flight.
pub open spec fn invariants_since_phase_v(fbc: FluentBitConfigView) -> TempPred<FBCCluster> {
    tla_forall(|sub_resource: SubResource| always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc))))
    .and(tla_forall(|sub_resource: SubResource| always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))))
}

pub proof fn invariants_since_phase_v_is_stable(fbc: FluentBitConfigView)
    ensures
        valid(stable(invariants_since_phase_v(fbc))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc));
    tla_forall_always_equality_variant::<FBCCluster, SubResource>(
        |sub_resource: SubResource| always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc))), a_to_p_1
    );
    let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key));
    tla_forall_always_equality_variant::<FBCCluster, SubResource>(
        |sub_resource: SubResource| always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key))), a_to_p_2
    );
    stable_and_always_n!(tla_forall(a_to_p_1), tla_forall(a_to_p_2));
}

}
