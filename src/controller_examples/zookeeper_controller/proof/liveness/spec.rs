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
use crate::temporal_logic::{defs::*, rules::*};
use crate::zookeeper_controller::{
    model::reconciler::*,
    proof::{helper_invariants, liveness::terminate, predicate::*, resource::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use vstd::prelude::*;

verus! {

pub open spec fn assumption_and_invariants_of_all_phases(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    invariants(zookeeper)
    .and(always(lift_state(desired_state_is(zookeeper))))
    .and(invariants_since_phase_i(zookeeper))
    .and(invariants_since_phase_ii(zookeeper))
    .and(invariants_since_phase_iii(zookeeper))
    .and(invariants_since_phase_iv(zookeeper))
    .and(invariants_since_phase_v(zookeeper))
    .and(invariants_since_phase_vi(zookeeper))
    .and(invariants_since_phase_vii(zookeeper))
}

pub open spec fn invariants_since_phase_n(n: nat, zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    if n == 0 {
        invariants(zookeeper).and(always(lift_state(desired_state_is(zookeeper))))
    } else if n == 1 {
        invariants_since_phase_i(zookeeper)
    } else if n == 2 {
        invariants_since_phase_ii(zookeeper)
    } else if n == 3 {
        invariants_since_phase_iii(zookeeper)
    } else if n == 4 {
        invariants_since_phase_iv(zookeeper)
    } else if n == 5 {
        invariants_since_phase_v(zookeeper)
    } else if n == 6 {
        invariants_since_phase_vi(zookeeper)
    } else if n == 7 {
        invariants_since_phase_vii(zookeeper)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(n: nat, zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster>
    decreases n,
{
    if n == 1 {
        invariants(zookeeper).and(always(lift_state(desired_state_is(zookeeper))))
    } else if 2 <= n <= 8 {
        spec_before_phase_n((n-1) as nat, zookeeper).and(invariants_since_phase_n((n-1) as nat, zookeeper))
    } else {
        true_pred()
    }
}

pub proof fn spec_of_previous_phases_entails_eventually_new_invariants(i: nat, zookeeper: ZookeeperClusterView)
    requires 1 <= i <= 7,
    ensures spec_before_phase_n(i, zookeeper).entails(true_pred().leads_to(invariants_since_phase_n(i, zookeeper))),
{
    let spec = spec_before_phase_n(i, zookeeper);
    reveal_with_fuel(spec_before_phase_n, 8);
    if i == 1 {
        ZKCluster::lemma_true_leads_to_crash_always_disabled(spec);
        ZKCluster::lemma_true_leads_to_busy_always_disabled(spec);
        ZKCluster::lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, zookeeper);
        leads_to_always_combine_n!(
            spec,
            true_pred(),
            lift_state(ZKCluster::crash_disabled()),
            lift_state(ZKCluster::busy_disabled()),
            lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zookeeper))
        );
    } else {
        terminate::reconcile_eventually_terminates(spec, zookeeper);
        if i == 2 {
            ZKCluster::lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as(spec, zookeeper);
        } else if i == 3 {
            helper_invariants::lemma_always_zookeeper_is_well_formed(spec, zookeeper);
            helper_invariants::lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step_forall(spec, zookeeper);
            helper_invariants::lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr_forall(spec, zookeeper);
            let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper));
            let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper));
            helper_invariants::lemma_eventually_always_every_zk_set_data_request_implies_at_after_update_zk_node_step(spec, zookeeper);
            helper_invariants::lemma_eventually_always_every_zk_create_node_request_implies_at_after_create_zk_node_step(spec, zookeeper);
            leads_to_always_combine_n!(
                spec, true_pred(), tla_forall(a_to_p_1), tla_forall(a_to_p_2),
                lift_state(helper_invariants::every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper)),
                lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper))
            );
        } else if i == 4 {
            helper_invariants::lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr_forall(spec, zookeeper);
        } else if i == 5 {
            helper_invariants::lemma_eventually_always_no_delete_resource_request_msg_in_flight_forall(spec, zookeeper);
        } else if i == 6 {
            helper_invariants::lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step_forall(spec, zookeeper);
            helper_invariants::lemma_eventually_always_object_in_response_at_after_create_resource_step_is_same_as_etcd_forall(spec, zookeeper);
            helper_invariants::lemma_eventually_always_object_in_response_at_after_update_resource_step_is_same_as_etcd_forall(spec, zookeeper);
            let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper));
            leads_to_always_combine_n!(
                spec, true_pred(),
                tla_forall(a_to_p_1), lift_state(helper_invariants::object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper)), lift_state(helper_invariants::object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper))
            );
        } else if i == 7 {
            helper_invariants::lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated_forall(spec, zookeeper);
        }
    }
}

pub proof fn assumption_and_invariants_of_all_phases_is_stable(zookeeper: ZookeeperClusterView)
    ensures
        valid(stable(assumption_and_invariants_of_all_phases(zookeeper))),
        valid(stable(invariants(zookeeper))),
        forall |i: nat|  1 <= i <= 8 ==> valid(stable(#[trigger] spec_before_phase_n(i, zookeeper))),
{
    reveal_with_fuel(spec_before_phase_n, 8);
    invariants_is_stable(zookeeper);
    always_p_is_stable(lift_state(desired_state_is(zookeeper)));
    invariants_since_phase_i_is_stable(zookeeper);
    invariants_since_phase_ii_is_stable(zookeeper);
    invariants_since_phase_iii_is_stable(zookeeper);
    invariants_since_phase_iv_is_stable(zookeeper);
    invariants_since_phase_v_is_stable(zookeeper);
    invariants_since_phase_vi_is_stable(zookeeper);
    invariants_since_phase_vii_is_stable(zookeeper);
    stable_and_n!(
        invariants(zookeeper), always(lift_state(desired_state_is(zookeeper))),
        invariants_since_phase_i(zookeeper), invariants_since_phase_ii(zookeeper), invariants_since_phase_iii(zookeeper),
        invariants_since_phase_iv(zookeeper), invariants_since_phase_v(zookeeper), invariants_since_phase_vi(zookeeper),
        invariants_since_phase_vii(zookeeper)
    );
}

// Next and all the wf conditions.
pub open spec fn next_with_wf() -> TempPred<ZKCluster> {
    always(lift_action(ZKCluster::next()))
    .and(tla_forall(|input| ZKCluster::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| ZKCluster::external_api_next().weak_fairness(input)))
    .and(tla_forall(|input| ZKCluster::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| ZKCluster::schedule_controller_reconcile().weak_fairness(input)))
    .and(tla_forall(|input| ZKCluster::builtin_controllers_next().weak_fairness(input)))
    .and(ZKCluster::disable_crash().weak_fairness(()))
    .and(ZKCluster::disable_transient_failure().weak_fairness(()))
}

pub proof fn next_with_wf_is_stable()
    ensures valid(stable(next_with_wf())),
{
    always_p_is_stable(lift_action(ZKCluster::next()));
    ZKCluster::tla_forall_action_weak_fairness_is_stable(ZKCluster::kubernetes_api_next());
    ZKCluster::tla_forall_action_weak_fairness_is_stable(ZKCluster::external_api_next());
    ZKCluster::tla_forall_action_weak_fairness_is_stable(ZKCluster::controller_next());
    ZKCluster::tla_forall_action_weak_fairness_is_stable(ZKCluster::schedule_controller_reconcile());
    ZKCluster::tla_forall_action_weak_fairness_is_stable(ZKCluster::builtin_controllers_next());
    ZKCluster::action_weak_fairness_is_stable(ZKCluster::disable_crash());
    ZKCluster::action_weak_fairness_is_stable(ZKCluster::disable_transient_failure());
    stable_and_n!(
        always(lift_action(ZKCluster::next())),
        tla_forall(|input| ZKCluster::kubernetes_api_next().weak_fairness(input)),
        tla_forall(|input| ZKCluster::external_api_next().weak_fairness(input)),
        tla_forall(|input| ZKCluster::controller_next().weak_fairness(input)),
        tla_forall(|input| ZKCluster::schedule_controller_reconcile().weak_fairness(input)),
        tla_forall(|input| ZKCluster::builtin_controllers_next().weak_fairness(input)),
        ZKCluster::disable_crash().weak_fairness(()),
        ZKCluster::disable_transient_failure().weak_fairness(())
    );
}

/// This predicate combines all the possible actions (next), weak fairness and invariants that hold throughout the execution.
/// We name it invariants here because these predicates are never violated, thus they can all be seen as some kind of invariants.
///
/// The final goal of our proof is to show init /\ invariants |= []desired_state_is(cr) ~> []current_state_matches(cr).
/// init /\ invariants is equivalent to init /\ next /\ weak_fairness, so we get cluster_spec() |= []desired_state_is(cr) ~> []current_state_matches(cr).
pub open spec fn invariants(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    next_with_wf().and(derived_invariants_since_beginning(zookeeper))
}

pub proof fn invariants_is_stable(zookeeper: ZookeeperClusterView)
    ensures valid(stable(invariants(zookeeper))),
{
    next_with_wf_is_stable();
    derived_invariants_since_beginning_is_stable(zookeeper);
    stable_and_n!(
        next_with_wf(),
        derived_invariants_since_beginning(zookeeper)
    );
}

// The safety invariants that are required to prove liveness.
pub open spec fn derived_invariants_since_beginning(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(ZKCluster::object_in_ok_get_response_has_smaller_rv_than_etcd())))
    .and(always(lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref()))))
    .and(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref()))))
    .and(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())))
    .and(always(lift_state(ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata())))
    .and(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)))))
    .and(always(lift_state(ZKCluster::no_pending_req_msg_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::Init)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsStatefulSet)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsZKNode)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKParentNode)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKNode)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateZKNode)))))
    .and(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateStatus)))))
    .and(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(step.0, step.1)))))))
    .and(always(tla_forall(|res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper)))))
    .and(always(lift_state(helper_invariants::no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(zookeeper))))
    .and(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref()))))
    .and(always(lift_state(ZKCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref()))))
    .and(always(lift_state(ZKCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref()))))
    .and(always(lift_state(ZKCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref()))))
    .and(always(tla_forall(|res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, zookeeper)))))
    .and(always(tla_forall(|res: SubResource| lift_state(ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, zookeeper).key)))))
    .and(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(zookeeper))))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)))))
}

pub proof fn derived_invariants_since_beginning_is_stable(zookeeper: ZookeeperClusterView)
    ensures valid(stable(derived_invariants_since_beginning(zookeeper))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper));
    let a_to_p_2 = |step: (ActionKind, SubResource)| lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(step.0, step.1))));
    let a_to_p_3 = |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper));
    let a_to_p_4 = |res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, zookeeper));
    let a_to_p_5 = |res: SubResource| lift_state(ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, zookeeper).key));
    let a_to_p_6 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper));
    stable_and_always_n!(
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        tla_forall(a_to_p_1),
        lift_state(ZKCluster::no_pending_req_msg_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::Init))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsStatefulSet))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsZKNode))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKParentNode))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKNode))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateZKNode))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateStatus))),
        tla_forall(a_to_p_2),
        tla_forall(a_to_p_3),
        lift_state(helper_invariants::no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(zookeeper)),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())),
        lift_state(ZKCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref())),
        lift_state(ZKCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref())),
        lift_state(ZKCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref())),
        tla_forall(a_to_p_4),
        tla_forall(a_to_p_5),
        lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(zookeeper)),
        tla_forall(a_to_p_6)
    );
}

/// The first notable phase comes when crash and k8s busy are always disabled and the object in schedule always has the same
/// spec and uid as the cr we provide.
///
/// Note that don't try to find any connections between those invariants -- they are put together because they don't have to
/// wait for another of them to first be satisfied.
pub open spec fn invariants_since_phase_i(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(lift_state(ZKCluster::crash_disabled()))
    .and(always(lift_state(ZKCluster::busy_disabled())))
    .and(always(lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zookeeper))))
}

pub proof fn invariants_since_phase_i_is_stable(zookeeper: ZookeeperClusterView)
    ensures valid(stable(invariants_since_phase_i(zookeeper))),
{
    stable_and_always_n!(
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::the_object_in_schedule_has_spec_and_uid_as(zookeeper))
    );
}

/// For now, phase II only contains one invariant, which is the object in reconcile has the same spec and uid as zookeeper.
///
/// It is alone because it relies on the invariant the_object_in_schedule_has_spec_and_uid_as (in phase I) and every invariant
/// in phase III relies on it.
pub open spec fn invariants_since_phase_ii(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)))
}


pub proof fn invariants_since_phase_ii_is_stable(zookeeper: ZookeeperClusterView)
    ensures valid(stable(invariants_since_phase_ii(zookeeper))),
{
    always_p_is_stable(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)));
}

pub open spec fn invariants_since_phase_iii(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper))))
    .and(always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper)))))
    .and(always(lift_state(helper_invariants::every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper))))
    .and(always(lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper))))
}

pub proof fn invariants_since_phase_iii_is_stable(zookeeper: ZookeeperClusterView)
    ensures valid(stable(invariants_since_phase_iii(zookeeper))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper));
    let a_to_p_2 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper));
    stable_and_always_n!(tla_forall(a_to_p_1), tla_forall(a_to_p_2),
        lift_state(helper_invariants::every_zk_set_data_request_implies_at_after_update_zk_node_step(zookeeper)),
        lift_state(helper_invariants::every_zk_create_node_request_implies_at_after_create_zk_node_step(zookeeper))
    );
}

/// Invariants since this phase ensure that certain objects only have owner references that point to current cr.
/// To have these invariants, we first need the invariant that evert create/update request make/change the object in the
/// expected way.
pub open spec fn invariants_since_phase_iv(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper))))
}

pub proof fn invariants_since_phase_iv_is_stable(zookeeper: ZookeeperClusterView)
    ensures valid(stable(invariants_since_phase_iv(zookeeper))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper));
    always_p_is_stable(tla_forall(a_to_p_1));
}

/// Invariants since phase V rely on the invariants since phase IV. When the objects starts to always have owner reference
/// pointing to current cr, it will never be recycled by the garbage collector. Plus, the reconciler itself never tries to
/// delete this object, so we can have the invariants saying that no delete request messages will be in flight.
pub open spec fn invariants_since_phase_v(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper))))
}

pub proof fn invariants_since_phase_v_is_stable(zookeeper: ZookeeperClusterView)
    ensures valid(stable(invariants_since_phase_v(zookeeper))),
{
    always_p_is_stable(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper))));
}

pub open spec fn invariants_since_phase_vi(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(tla_forall(|sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper))))
    .and(always(lift_state(helper_invariants::object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper))))
    .and(always(lift_state(helper_invariants::object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper))))
}

pub proof fn invariants_since_phase_vi_is_stable(zookeeper: ZookeeperClusterView)
    ensures valid(stable(invariants_since_phase_vi(zookeeper))),
{
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper));
    stable_and_always_n!(
        tla_forall(a_to_p_1),
        lift_state(helper_invariants::object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper)),
        lift_state(helper_invariants::object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper))
    );
}

pub open spec fn invariants_since_phase_vii(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))
}

pub proof fn invariants_since_phase_vii_is_stable(zookeeper: ZookeeperClusterView)
    ensures valid(stable(invariants_since_phase_vii(zookeeper))),
{
    always_p_is_stable(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)));
}

pub proof fn lemma_always_for_all_sub_resource_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
    ensures spec.entails(always(tla_forall(|step: (ActionKind, SubResource)| lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(step.0, step.1))))))),
{
    // TODO (xudong): investigate the performance of this lemma
    // Somehow the reasoning inside the assert forall block below is very slow (takes more than 8 seconds!)
    // I suspect it is related to the precondition of lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state
    let a_to_p = |step: (ActionKind, SubResource)| lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(step.0, step.1))));
    assert_by(spec.entails(always(tla_forall(a_to_p))), {
        assert forall |step: (ActionKind, SubResource)| spec.entails(always(#[trigger] a_to_p(step))) by {
            ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                spec, zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(step.0, step.1))
            );
        }
        spec_entails_always_tla_forall(spec, a_to_p);
    });
}

pub proof fn lemma_always_for_after_exists_stateful_set_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
    ensures
        spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsStatefulSet))))),
{
    ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsStatefulSet));
}

pub proof fn lemma_always_for_after_exists_zk_node_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
    ensures
        spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsZKNode))))),
{
    ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsZKNode));
}

pub proof fn lemma_always_for_after_create_zk_parent_node_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
    ensures spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKParentNode))))),
{
    ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKParentNode));
}

pub proof fn lemma_always_for_after_create_zk_node_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
    ensures spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKNode))))),
{
    ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKNode));
}

pub proof fn lemma_always_for_after_update_zk_node_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
    ensures spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateZKNode))))),
{
    ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateZKNode));
}

pub proof fn lemma_always_for_after_update_status_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
    ensures spec.entails(always(lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateStatus))))),
{
    ZKCluster::lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateStatus));
}

pub proof fn sm_spec_entails_all_invariants(zookeeper: ZookeeperClusterView)
    ensures cluster_spec().entails(derived_invariants_since_beginning(zookeeper)),
{
    let spec = cluster_spec();
    // Adding two assertions to make the verification faster because all the lemmas below require the two preconditions.
    // And then the verifier doesn't have to infer it every time applying those lemmas.
    assert(spec.entails(lift_state(ZKCluster::init())));
    assert(spec.entails(always(lift_action(ZKCluster::next()))));
    ZKCluster::lemma_always_every_in_flight_msg_has_unique_id(spec);
    ZKCluster::lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    ZKCluster::lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec, zookeeper.object_ref());
    ZKCluster::lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, zookeeper.object_ref());
    ZKCluster::lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    ZKCluster::lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec);
    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    let a_to_p_1 = |sub_resource: SubResource| lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper));
    assert_by(spec.entails(always(tla_forall(a_to_p_1))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_1(sub_resource))) by {
            helper_invariants::lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec, sub_resource, zookeeper);
        }
        spec_entails_always_tla_forall(spec, a_to_p_1);
    });
    ZKCluster::lemma_always_no_pending_req_msg_at_reconcile_state(spec, zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::Init));

    // Different from other a_to_p_x, we encapsulate a_to_p_2 inside the lemma below because we find its reasoning is
    // surprisingly slow in this context. Encapsulating the reasoning reduces the verification time of this function
    // from more than 40 seconds to 2 seconds.
    let a_to_p_2 = |step: (ActionKind, SubResource)| lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterKRequestStep(step.0, step.1))));
    lemma_always_for_all_sub_resource_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper);
    // lemma_always_for_all_non_sub_resource_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper);
    lemma_always_for_after_exists_stateful_set_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper);
    lemma_always_for_after_exists_zk_node_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper);
    lemma_always_for_after_create_zk_parent_node_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper);
    lemma_always_for_after_create_zk_node_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper);
    lemma_always_for_after_update_zk_node_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper);
    lemma_always_for_after_update_status_step_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, zookeeper);

    let a_to_p_3 = |res: SubResource| lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper));
    assert_by(spec.entails(always(tla_forall(a_to_p_3))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_3(sub_resource))) by {
            helper_invariants::lemma_always_no_update_status_request_msg_in_flight_of_except_stateful_set(spec, sub_resource, zookeeper);
        }
        spec_entails_always_tla_forall(spec, a_to_p_3);
    });
    helper_invariants::lemma_always_no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(spec, zookeeper);
    helper_invariants::lemma_always_the_object_in_reconcile_satisfies_state_validation(spec, zookeeper.object_ref());
    ZKCluster::lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(spec, zookeeper.object_ref());
    ZKCluster::lemma_always_key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(spec, zookeeper.object_ref());
    ZKCluster::lemma_always_key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(spec, zookeeper.object_ref());
    let a_to_p_4 = |res: SubResource| lift_state(helper_invariants::response_at_after_get_resource_step_is_resource_get_response(res, zookeeper));
    assert_by(spec.entails(always(tla_forall(a_to_p_4))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_4(sub_resource))) by {
            helper_invariants::lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, sub_resource, zookeeper);
        }
        spec_entails_always_tla_forall(spec, a_to_p_4);
    });
    let a_to_p_5 = |res: SubResource| lift_state(ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, zookeeper).key));
    assert_by(spec.entails(always(tla_forall(a_to_p_5))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_5(sub_resource))) by {
            ZKCluster::lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, get_request(sub_resource, zookeeper).key);
        }
        spec_entails_always_tla_forall(spec, a_to_p_5);
    });
    helper_invariants::lemma_always_stateful_set_in_etcd_satisfies_unchangeable(spec, zookeeper);
    let a_to_p_6 = |sub_resource: SubResource| lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper));
    assert_by(spec.entails(always(tla_forall(a_to_p_6))), {
        assert forall |sub_resource: SubResource| spec.entails(always(#[trigger] a_to_p_6(sub_resource))) by {
            helper_invariants::lemma_always_object_in_etcd_satisfies_unchangeable(spec, sub_resource, zookeeper);
        }
        spec_entails_always_tla_forall(spec, a_to_p_6);
    });

    entails_always_and_n!(
        spec,
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(ZKCluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(zookeeper.object_ref())),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::each_scheduled_object_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        tla_forall(a_to_p_1),
        lift_state(ZKCluster::no_pending_req_msg_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::Init))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsStatefulSet))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterExistsZKNode))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKParentNode))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterCreateZKNode))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateZKNode))),
        lift_state(ZKCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(zookeeper.object_ref(), at_step_closure(ZookeeperReconcileStep::AfterUpdateStatus))),
        tla_forall(a_to_p_2),
        tla_forall(a_to_p_3),
        lift_state(helper_invariants::no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(zookeeper)),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())),
        lift_state(ZKCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref())),
        lift_state(ZKCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref())),
        lift_state(ZKCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref())),
        tla_forall(a_to_p_4),
        tla_forall(a_to_p_5),
        lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(zookeeper)),
        tla_forall(a_to_p_6)
    );
}

}
