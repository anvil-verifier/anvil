// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, 
    cluster::*, 
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
    proof::{predicate::*, helper_lemmas, helper_invariants::{predicate::*}},
};
use crate::vstd_ext::seq_lib::*;
use vstd::prelude::*;

verus!{

// WORK IN PROGRESS.
#[verifier(external_body)]
pub proof fn lemma_eventually_always_matching_pods_bounded(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        vrs.state_validation(),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(matching_pod_entries_at_max_implies_no_create_matching_pod_message_in_flight(vrs, controller_id)))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(matching_pods_bounded(vrs))))),
{
    let post = matching_pods_bounded(vrs);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& matching_pod_entries_at_max_implies_no_create_matching_pod_message_in_flight(vrs, controller_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s_prime)
    };
    
    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vrs)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(matching_pod_entries_at_max_implies_no_create_matching_pod_message_in_flight(vrs, controller_id)),
        lifted_vrs_non_interference_property_action(cluster, controller_id)
    );

    assert(spec.entails(lift_state(post)));
    assert_by(spec.entails(true_pred().leads_to(lift_state(post))), {

    });
    assert forall |s, s_prime| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        //assume(false);
    }

    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(post));
}

pub proof fn lemma_eventually_always_no_pending_update_or_update_status_request_on_pods(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_pending_update_or_update_status_request_on_pods())))),
{
    let requirements = |msg: Message, s: ClusterState| {
        &&& msg.content.is_update_request() ==> msg.content.get_update_request().key().kind != PodView::kind()
        &&& msg.content.is_update_status_request() ==> msg.content.get_update_status_request().key().kind != PodView::kind()
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s_prime)
    };
    
    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.in_flight().contains(msg) {
                assert(requirements(msg, s));
                assert(requirements(msg, s_prime));
            } else {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep((id, _, _)) => {
                        VReplicaSetReconcileState::marshal_preserves_integrity();
                        if id != controller_id {
                            assert(vrs_not_interfered_by(id)(s_prime));
                        }
                    },
                    _ => {
                        assert(requirements(msg, s_prime));
                    }
                }
            }
        }
    }

    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_non_interference_property_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

// pub proof fn lemma_eventually_always_no_pending_create_or_delete_request_not_from_controller_on_pods(
//     spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
// )
//     requires
//         spec.entails(always(lift_action(cluster.next()))),
//         cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
//         cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
//         spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
//         spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
//         spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
//         spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
//         spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
//         spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
//         spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
//         spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
//         spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
//         spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
//         spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
//         spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
//         forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
//             ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
//     ensures spec.entails(true_pred().leads_to(always(lift_state(no_pending_create_or_delete_request_not_from_controller_on_pods())))),
// {
//     let requirements = |msg: Message, s: ClusterState| {
//         ({
//             &&& !(msg.src.is_Controller())
//             &&& msg.dst.is_APIServer()
//             &&& msg.content.is_APIRequest()
//         })
//         ==>
//         ({
//             &&& msg.content.is_create_request() ==> msg.content.get_create_request().key().kind != PodView::kind()
//             &&& (msg.content.is_delete_request() && s.resources.contains_key(msg.content.get_delete_request().key)) ==> {
//                 let obj = s.resources[msg.content.get_delete_request().key];

//             }// msg.content.get_delete_request().key.kind != PodView::kind()
//         })
//     };

//     let stronger_next = |s: ClusterState, s_prime: ClusterState| {
//         &&& cluster.next()(s, s_prime)
//         &&& Cluster::there_is_the_controller_state(controller_id)(s)
//         &&& Cluster::crash_disabled(controller_id)(s)
//         &&& Cluster::req_drop_disabled()(s)
//         &&& Cluster::pod_monkey_disabled()(s)
//         &&& Cluster::every_in_flight_msg_has_unique_id()(s)
//         &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
//         &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
//         &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
//         &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
//         &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
//         &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
//                 ==> #[trigger] vrs_not_interfered_by(other_id)(s)
//         &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
//                 ==> #[trigger] vrs_not_interfered_by(other_id)(s_prime)
//     };
    
//     assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
//         assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
//         implies requirements(msg, s_prime) by {
//             if s.in_flight().contains(msg) {
//                 assert(requirements(msg, s));
//                 assert(requirements(msg, s_prime));
//             } else {
//                 let step = choose |step| cluster.next_step(s, s_prime, step);
//                 match step {
//                     Step::ControllerStep((id, _, _)) => {
//                         // VReplicaSetReconcileState::marshal_preserves_integrity();
//                         // if id != controller_id {
//                         //     assert(vrs_not_interfered_by(id)(s_prime));
//                         // }
//                     },
//                     Step::BuiltinControllersStep(..) => {
//                         assume(false);
//                     }
//                     _ => {
//                         //assume(false);
//                         assert(requirements(msg, s_prime));
//                     }
//                 }
//             }
//         }
//     }
//     assume(false);

//     helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
//         spec, cluster, controller_id
//     );
//     invariant_n!(
//         spec, lift_action(stronger_next), 
//         lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
//         lift_action(cluster.next()),
//         lift_state(Cluster::there_is_the_controller_state(controller_id)),
//         lift_state(Cluster::crash_disabled(controller_id)),
//         lift_state(Cluster::req_drop_disabled()),
//         lift_state(Cluster::pod_monkey_disabled()),
//         lift_state(Cluster::every_in_flight_msg_has_unique_id()),
//         lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
//         lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
//         lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
//         lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
//         lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
//         lifted_vrs_non_interference_property_action(cluster, controller_id)
//     );

//     cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
//     temp_pred_equality(
//         lift_state(no_pending_create_or_delete_request_not_from_controller_on_pods()),
//         lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
//     );
// }

pub proof fn lemma_eventually_always_every_create_matching_pod_request_implies_at_after_create_pod_step(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, controller_id))))),
{
    let key = vrs.object_ref();
    let requirements = |msg: Message, s: ClusterState| {
        ({
            let content = msg.content;
            let obj = content.get_create_request().obj;
            &&& content.is_create_request()
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
            &&& owned_selector_match_is(vrs, obj)
        } ==> {
            &&& exists |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterCreatePod(diff))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        })
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        let content = msg.content;
        let obj = content.get_create_request().obj;
        &&& content.is_create_request()
        &&& msg.src.is_Controller()
        &&& msg.src.get_Controller_0() == controller_id
        &&& owned_selector_match_is(vrs, obj)
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s_prime)
    };
    
    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            VReplicaSetReconcileState::marshal_preserves_integrity();
            if requirements_antecedent(msg, s) {
                if s.in_flight().contains(msg) {
                    assert(requirements(msg, s));

                    let diff = choose |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterCreatePod(diff))(s);
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterCreatePod(diff))(s_prime)
                        || at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterCreatePod((diff - 1) as usize))(s_prime));

                    assert(requirements(msg, s_prime));
                } else {
                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    let cr_key = step.get_ControllerStep_0().2.get_Some_0();
                    let local_step = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let local_step_prime = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let new_diff = local_step_prime.get_AfterCreatePod_0();
                    assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterCreatePod(new_diff))(s_prime));
                    assert(requirements(msg, s_prime));
                }
            }
        }
    }

    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vrs)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_non_interference_property_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, controller_id)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_every_delete_matching_pod_request_implies_at_after_delete_pod_step(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<VReplicaSetView>(controller_id, vrs)))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),
        spec.entails(always(lift_state(no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))))),
{
    let key = vrs.object_ref();
    let requirements = |msg: Message, s: ClusterState| {
        ({
            let content = msg.content;
            let req = content.get_delete_request();
            let key = content.get_delete_request().key;
            let req_rv = req.preconditions.unwrap().resource_version.unwrap();
            let obj = s.resources()[key];
            &&& content.is_delete_request()
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
            &&& s.resources().contains_key(key)
            &&& owned_selector_match_is(vrs, obj)

            // Delete precondition clauses.
            &&& req.preconditions.is_Some()
            &&& req.preconditions.unwrap().resource_version.is_Some()
            &&& req.preconditions.unwrap().uid.is_None()
            &&& obj.metadata.resource_version.is_Some()
            &&& obj.metadata.resource_version.unwrap() == req_rv
        } ==> {
            let content = msg.content;
            let req = content.get_delete_request();
            let req_rv = req.preconditions.unwrap().resource_version.unwrap();
            let key = req.key;
            let obj = s.resources()[key];
            &&& exists |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterDeletePod(diff))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        })
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        let content = msg.content;
        let req = content.get_delete_request();
        let key = content.get_delete_request().key;
        let req_rv = req.preconditions.unwrap().resource_version.unwrap();
        let obj = s.resources()[key];
        &&& content.is_delete_request()
        &&& msg.src.is_Controller()
        &&& msg.src.get_Controller_0() == controller_id
        &&& s.resources().contains_key(key)
        &&& owned_selector_match_is(vrs, obj)

        // Delete precondition clauses.
        &&& req.preconditions.is_Some()
        &&& req.preconditions.unwrap().resource_version.is_Some()
        &&& req.preconditions.unwrap().uid.is_None()
        &&& obj.metadata.resource_version.is_Some()
        &&& obj.metadata.resource_version.unwrap() == req_rv
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as::<VReplicaSetView>(controller_id, vrs)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s_prime)
        &&& no_pending_update_or_update_status_request_on_pods()(s)
        &&& every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
        &&& each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)(s)
    };
    
    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            VReplicaSetReconcileState::marshal_preserves_integrity();
            VReplicaSetView::marshal_preserves_integrity();
            if requirements_antecedent(msg, s) {
                if s.in_flight().contains(msg) {
                    assert(requirements(msg, s));

                    let diff = choose |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterDeletePod(diff))(s);
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterDeletePod(diff))(s_prime)
                        || at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterDeletePod((diff + 1) as usize))(s_prime));

                    assert(requirements(msg, s_prime));
                } else {
                    let content = msg.content;
                    let request_key = content.get_delete_request().key;
                    let obj = s.resources()[content.get_delete_request().key];

                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    let cr_key = step.get_ControllerStep_0().2.get_Some_0();
                    let local_step = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let local_step_prime = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let new_diff = local_step_prime.get_AfterDeletePod_0();

                    let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();

                    if local_step.is_AfterListPods() {
                        let cr_msg = step.get_ControllerStep_0().1.get_Some_0();
                        let req_msg = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg.get_Some_0();
                        let objs = cr_msg.content.get_list_response().res.unwrap();
                        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                        let desired_replicas: usize = triggering_cr.spec.replicas.unwrap_or(0) as usize;
                        let pods_or_none = objects_to_pods(objs);
                        let pods = pods_or_none.unwrap();
                        let filtered_pods = filter_pods(pods, triggering_cr);
                        let diff = filtered_pods.len() - desired_replicas;
                        seq_filter_contains_implies_seq_contains(
                            pods,
                            |pod: PodView|
                            pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                            && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                            && pod.metadata.deletion_timestamp.is_None(),
                            filtered_pods[diff - 1]
                        );

                        let idx1 = choose |i| pods[i] == filtered_pods[diff - 1];
                        assert(pods[idx1] == filtered_pods[diff - 1]);
                        assert(pods[idx1] == PodView::unmarshal(objs[idx1]).unwrap());
                        assert(filtered_pods[diff - 1].object_ref() == request_key);
                    }

                    let controller_owners = obj.metadata.owner_references.unwrap().filter(
                        |o: OwnerReferenceView| o.controller.is_Some() && o.controller.get_Some_0()
                    );
                    assert(controller_owners.contains(
                        VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr)
                            .unwrap().controller_owner_ref()
                    ));
                    assert(controller_owners.contains(vrs.controller_owner_ref()));
                    assert(cr_key.name == key.name);

                    assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::AfterDeletePod(new_diff))(s_prime));
                    assert(requirements(msg, s_prime));
                }
            } else {
                if s.in_flight().contains(msg) {
                    assert(!requirements_antecedent(msg, s));
                    let content = msg.content;
                    let req = content.get_delete_request();
                    let key = req.key;
                    let obj = s.resources()[key];

                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    match step {
                        Step::APIServerStep(input) => {
                            // Invariant every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter
                            // is essential here.
                        },
                        _ => {}
                    }
                }
            }
        }
    }

    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vrs)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<VReplicaSetView>(controller_id, vrs)),
        lifted_vrs_non_interference_property_action(cluster, controller_id),
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lift_state(every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id))
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}


}