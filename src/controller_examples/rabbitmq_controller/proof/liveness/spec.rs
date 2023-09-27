// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
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
use crate::rabbitmq_controller::{
    common::*,
    proof::{helper_invariants, predicate::*, resource::*},
    spec::{reconciler::*, types::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

spec fn assumption_and_invariants_of_all_phases(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    invariants(rabbitmq)
    .and(always(lift_state(RMQCluster::desired_state_is(rabbitmq))))
    .and(invariants_since_phase_i(rabbitmq))
    .and(invariants_since_phase_ii(rabbitmq))
    .and(invariants_since_phase_iii(rabbitmq))
    .and(invariants_since_phase_iv(rabbitmq))
    .and(invariants_since_phase_v(rabbitmq))
}

// Next and all the wf conditions.
spec fn next_with_wf() -> TempPred<RMQCluster> {
    always(lift_action(RMQCluster::next()))
    .and(tla_forall(|input| RMQCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::schedule_controller_reconcile().weak_fairness(input)))
    .and(tla_forall(|input| RMQCluster::builtin_controllers_next().weak_fairness(input)))
    .and(RMQCluster::disable_crash().weak_fairness(()))
    .and(RMQCluster::disable_busy().weak_fairness(()))
}

proof fn next_with_wf_is_stable()
    ensures
        valid(stable(next_with_wf())),
{
    always_p_is_stable(lift_action(RMQCluster::next()));
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::kubernetes_api_next());
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::controller_next());
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::schedule_controller_reconcile());
    RMQCluster::tla_forall_action_weak_fairness_is_stable(RMQCluster::builtin_controllers_next());
    RMQCluster::action_weak_fairness_is_stable(RMQCluster::disable_crash());
    RMQCluster::action_weak_fairness_is_stable(RMQCluster::disable_busy());
    stable_and_n!(
        always(lift_action(RMQCluster::next())),
        tla_forall(|input| RMQCluster::kubernetes_api_next().weak_fairness(input)),
        tla_forall(|input| RMQCluster::controller_next().weak_fairness(input)),
        tla_forall(|input| RMQCluster::schedule_controller_reconcile().weak_fairness(input)),
        tla_forall(|input| RMQCluster::builtin_controllers_next().weak_fairness(input)),
        RMQCluster::disable_crash().weak_fairness(()),
        RMQCluster::disable_busy().weak_fairness(())
    );
}

/// This predicate combines all the possible actions (next), weak fairness and invariants that hold throughout the execution.
/// We name it invariants here because these predicates are never violated, thus they can all be seen as some kind of invariants.
///
/// The final goal of our proof is to show init /\ invariants |= []desired_state_is(cr) ~> []current_state_matches(cr).
/// init /\ invariants is equivalent to init /\ next /\ weak_fairness, so we get cluster_spec() |= []desired_state_is(cr) ~> []current_state_matches(cr).
spec fn invariants(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    next_with_wf()
    .and(derived_invariants_since_beginning(rabbitmq))
}

proof fn invariants_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(invariants(rabbitmq))),
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
    .and(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref()))))
    .and(always(lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(RMQCluster::each_scheduled_object_has_consistent_key_and_valid_metadata())))
    .and(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())))
    .and(tla_forall(|sub_resource: SubResource| always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq)))))
    .and(always(lift_state(RMQCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init)))))
    .and(tla_forall(|step: (ActionKind, SubResource)| always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1)))))))
}

pub proof fn derived_invariants_since_beginning_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(derived_invariants_since_beginning(rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq));
    tla_forall_always_equality_variant::<RMQCluster, SubResource>(
        |sub_resource: SubResource| always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq))), a_to_p_1
    );
    let a_to_p_2 = |step: (ActionKind, SubResource)| lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1))));
    tla_forall_always_equality_variant::<RMQCluster, (ActionKind, SubResource)>(
        |step: (ActionKind, SubResource)| always(lift_state(RMQCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::AfterKRequestStep(step.0, step.1))))), a_to_p_2
    );
    stable_and_always_n!(
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
        lift_state(RMQCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        tla_forall(a_to_p_1),
        lift_state(RMQCluster::no_pending_req_msg_or_external_api_input_at_reconcile_state(rabbitmq.object_ref(), at_step_closure(RabbitmqReconcileStep::Init))),
        tla_forall(a_to_p_2)
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
    ensures
        valid(stable(invariants_since_phase_i(rabbitmq))),
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
    ensures
        valid(stable(invariants_since_phase_ii(rabbitmq))),
{
    always_p_is_stable(lift_state(RMQCluster::the_object_in_reconcile_has_spec_and_uid_as(rabbitmq)));
}

/// After we know that the spec and uid of object in reconcile, we can obtain the following invariants about messages. This is
/// because the create and update request messages are derived from the custom resource object in reconcile (i.e, triggering_cr).
pub open spec fn invariants_since_phase_iii(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    tla_forall(|sub_resource: SubResource| always(lift_state(helper_invariants::every_resource_object_in_create_request_does_the_make_method(sub_resource, rabbitmq))))
    .and(tla_forall(|sub_resource: SubResource| always(lift_state(helper_invariants::every_resource_object_in_update_request_does_the_update_method(sub_resource, rabbitmq)))))
}

pub proof fn invariants_since_phase_iii_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(invariants_since_phase_iii(rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_object_in_create_request_does_the_make_method(sub_resource, rabbitmq));
    tla_forall_always_equality_variant::<RMQCluster, SubResource>(
        |sub_resource: SubResource| always(lift_state(helper_invariants::every_resource_object_in_create_request_does_the_make_method(sub_resource, rabbitmq))), a_to_p_1
    );
    let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_object_in_update_request_does_the_update_method(sub_resource, rabbitmq));
    tla_forall_always_equality_variant::<RMQCluster, SubResource>(
        |sub_resource: SubResource| always(lift_state(helper_invariants::every_resource_object_in_update_request_does_the_update_method(sub_resource, rabbitmq))), a_to_p_2
    );
    stable_and_always_n!(tla_forall(a_to_p_1), tla_forall(a_to_p_2));
}

/// Invariants since this phase ensure that certain objects only have owner references that point to current cr.
/// To have these invariants, we first need the invariant that evert create/update request make/change the object in the
/// expected way.
spec fn invariants_since_phase_iv(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    tla_forall(|sub_resource: SubResource| always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, rabbitmq).key, rabbitmq))))
}

proof fn invariants_since_phase_iv_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(invariants_since_phase_iv(rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, rabbitmq).key, rabbitmq));
    tla_forall_always_equality_variant::<RMQCluster, SubResource>(
        |sub_resource: SubResource| always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, rabbitmq).key, rabbitmq))), a_to_p_1
    );
    always_p_is_stable(tla_forall(a_to_p_1));
}

/// Invariants since phase V rely on the invariants since phase IV. When the objects starts to always have owner reference
/// pointing to current cr, it will never be recycled by the garbage collector. Plus, the reconciler itself never tries to
/// delete this object, so we can have the invariants saying that no delete request messages will be in flight.
spec fn invariants_since_phase_v(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    tla_forall(|sub_resource: SubResource| always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key))))
}

proof fn invariants_since_phase_v_is_stable(rabbitmq: RabbitmqClusterView)
    ensures
        valid(stable(invariants_since_phase_v(rabbitmq))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key));
    tla_forall_always_equality_variant::<RMQCluster, SubResource>(
        |sub_resource: SubResource| always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key))), a_to_p_1
    );
    always_p_is_stable(tla_forall(a_to_p_1));
}

}
