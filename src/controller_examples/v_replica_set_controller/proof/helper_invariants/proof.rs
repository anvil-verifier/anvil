// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::predicate::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use crate::v_replica_set_controller::{
    proof::{predicate::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub proof fn lemma_eventually_always_no_pending_update_or_update_status_request_on_pods(
    spec: TempPred<VRSCluster>
)
    requires
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(VRSCluster::pod_event_disabled()))),
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::external_api_next().weak_fairness(i))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_pending_update_or_update_status_request_on_pods())))),
{
    let requirements = |msg: VRSMessage, s: VRSCluster| {
        &&& msg.content.is_update_request() ==> msg.content.get_update_request().key().kind != PodView::kind()
        &&& msg.content.is_update_status_request() ==> msg.content.get_update_status_request().key().kind != PodView::kind()
    };

    let stronger_next = |s: VRSCluster, s_prime: VRSCluster| {
        &&& VRSCluster::next()(s, s_prime)
        &&& VRSCluster::pod_event_disabled()(s)
    };

    assert forall |s: VRSCluster, s_prime: VRSCluster| #[trigger]  #[trigger] stronger_next(s, s_prime) implies VRSCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: VRSMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.in_flight().contains(msg) {
                assert(requirements(msg, s));
                assert(requirements(msg, s_prime));
            } else {
                let step = choose |step| VRSCluster::next_step(s, s_prime, step);
                match step {
                    _ => {
                        assert(requirements(msg, s_prime));
                    }
                }
            }
        }
    }

    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(VRSCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(VRSCluster::next()),
        lift_state(VRSCluster::pod_event_disabled())
    );

    VRSCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lift_state(VRSCluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_every_create_matching_pod_request_implies_at_after_create_pod_step(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView
)
    requires
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::pod_event_disabled()))),
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::the_object_in_reconcile_has_spec_and_uid_as(vrs)))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::desired_state_is(vrs)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs))))),
{
    let key = vrs.object_ref();
    let requirements = |msg: VRSMessage, s: VRSCluster| {
        ({
            let content = msg.content;
            let obj = content.get_create_request().obj;
            &&& content.is_create_request()
            &&& owned_selector_match_is(vrs, obj)
        } ==> {
            &&& exists |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterCreatePod(diff))(s)
            &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), msg)
        })
    };
    let requirements_antecedent = |msg: VRSMessage, s: VRSCluster| {
        let content = msg.content;
        let obj = content.get_create_request().obj;
        &&& content.is_create_request()
        &&& owned_selector_match_is(vrs, obj)
    };

    let stronger_next = |s: VRSCluster, s_prime: VRSCluster| {
        &&& VRSCluster::next()(s, s_prime)
        &&& VRSCluster::crash_disabled()(s)
        &&& VRSCluster::busy_disabled()(s)
        &&& VRSCluster::pod_event_disabled()(s)
        &&& VRSCluster::desired_state_is(vrs)(s)
        &&& VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& VRSCluster::every_in_flight_msg_has_unique_id()(s)
        &&& VRSCluster::the_object_in_reconcile_has_spec_and_uid_as(vrs)(s)
    };

    assert forall |s: VRSCluster, s_prime: VRSCluster| #[trigger]  #[trigger] stronger_next(s, s_prime) implies VRSCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: VRSMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if requirements_antecedent(msg, s) {
                if s.in_flight().contains(msg) {
                    assert(requirements(msg, s));

                    let diff = choose |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterCreatePod(diff))(s);
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                    assert(at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterCreatePod(diff))(s_prime)
                        || at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterCreatePod((diff - 1) as usize))(s_prime));

                    assert(requirements(msg, s_prime));
                } else {
                    let step = choose |step| VRSCluster::next_step(s, s_prime, step);
                    let cr_key = step.get_ControllerStep_0().1.get_Some_0();
                    assert(step.is_ControllerStep());
                    assert(s.ongoing_reconciles().contains_key(cr_key));
                    let local_step = s.ongoing_reconciles()[cr_key].local_state.reconcile_step;
                    let local_step_prime = s_prime.ongoing_reconciles()[cr_key].local_state.reconcile_step;
                    assert(local_step.is_AfterListPods() || local_step.is_AfterCreatePod());
                    assert(local_step_prime.is_AfterCreatePod());
                    let new_diff = local_step_prime.get_AfterCreatePod_0();
                    assume(key == cr_key); // How to prove this?
                    assert(at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterCreatePod(new_diff))(s_prime));
                }
            }
        }
    }

    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(VRSCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(VRSCluster::next()),
        lift_state(VRSCluster::crash_disabled()),
        lift_state(VRSCluster::busy_disabled()),
        lift_state(VRSCluster::pod_event_disabled()),
        lift_state(VRSCluster::desired_state_is(vrs)),
        lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(VRSCluster::every_in_flight_msg_has_unique_id()),
        lift_state(VRSCluster::the_object_in_reconcile_has_spec_and_uid_as(vrs))
    );

    VRSCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)),
        lift_state(VRSCluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_every_delete_matching_pod_request_implies_at_after_delete_pod_step(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView
)
    requires
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::pod_event_disabled()))),
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::desired_state_is(vrs)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))))),
{
    let requirements = |msg: VRSMessage, s: VRSCluster| {
        ({
            let content = msg.content;
            let key = content.get_delete_request().key;
            let obj = s.resources()[key];
            &&& content.is_delete_request()
            &&& s.resources().contains_key(key)
            &&& owned_selector_match_is(vrs, obj)
        } ==> {
            &&& exists |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterDeletePod(diff))(s)
            &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), msg)
        })
    };

    let stronger_next = |s: VRSCluster, s_prime: VRSCluster| {
        &&& VRSCluster::next()(s, s_prime)
        &&& VRSCluster::crash_disabled()(s)
        &&& VRSCluster::busy_disabled()(s)
        &&& VRSCluster::pod_event_disabled()(s)
        &&& VRSCluster::desired_state_is(vrs)(s)
    };

    assert forall |s: VRSCluster, s_prime: VRSCluster| #[trigger]  #[trigger] stronger_next(s, s_prime) implies VRSCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: VRSMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.in_flight().contains(msg) {
                assert(requirements(msg, s));

                let content = msg.content;
                let key = content.get_delete_request().key;
                let obj = s.resources()[key];
                if content.is_delete_request() 
                    && s.resources().contains_key(key)
                    && owned_selector_match_is(vrs, obj) {
                    let diff = choose |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterDeletePod(diff))(s);
                    let step = choose |step| VRSCluster::next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep(input) => {
                            assume(false) // DEAL WITH LATER
                        },
                        _ => {
                            assert(at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterDeletePod(diff))(s_prime));
                            assert(requirements(msg, s_prime));
                        }
                    }
                } else {
                    assume(false); // DEAL WITH LATER
                }

                assert(requirements(msg, s_prime));
            } else {
                assume(false); // DEAL WITH LATER
                let step = choose |step| VRSCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(_) => {
                        assume(false); // DEAL WITH LATER
                    },
                    _ => {
                        assert(requirements(msg, s_prime));
                    }
                }
            }
        }
    }

    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(VRSCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(VRSCluster::next()),
        lift_state(VRSCluster::crash_disabled()),
        lift_state(VRSCluster::busy_disabled()),
        lift_state(VRSCluster::pod_event_disabled()),
        lift_state(VRSCluster::desired_state_is(vrs))
    );

    VRSCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)),
        lift_state(VRSCluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

}
