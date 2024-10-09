// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use vstd::prelude::*;

verus! {

pub proof fn lemma_from_after_send_list_pods_req_to_receive_list_pods_resp(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef,
    req_msg: Message, diff: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<VReplicaSetView>()))),

        // spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite()))),
        // spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed()))),
        // spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        // spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)))),
        // spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)))),
    ensures
        true
        // spec.entails(
        //     lift_state(
        //         |s: Cluster| {
        //             &&& req_msg_is_the_in_flight_list_req_at_after_list_pods_step(vrs, req_msg)(s)
        //             &&& num_diff_pods_is(vrs, diff)(s)
        //         }
        //     ).leads_to(
        //         lift_state(
        //             |s: Cluster| {
        //                 &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
        //                 &&& num_diff_pods_is(vrs, diff)(s)
        //             }
        //         )
        //     )
        // )
{
    assume(false);
    // let pre = |s: Cluster| {
    //     &&& req_msg_is_the_in_flight_list_req_at_after_list_pods_step(vrs, req_msg)(s)
    //     &&& num_diff_pods_is(vrs, diff)(s)
    // };
    // let post = |s: Cluster| {
    //     &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
    //     &&& num_diff_pods_is(vrs, diff)(s)
    // };
    // let input = Some(req_msg);
    // let stronger_next = |s, s_prime: Cluster| {
    //     &&& Cluster::next()(s, s_prime)
    //     &&& Cluster::crash_disabled()(s)
    //     &&& Cluster::busy_disabled()(s)
    //     &&& Cluster::every_in_flight_msg_has_unique_id()(s)
    //     &&& Cluster::each_object_in_etcd_is_well_formed()(s)
    //     &&& helper_invariants::cluster_resources_is_finite()(s)
    //     &&& helper_invariants::every_create_request_is_well_formed()(s)
    //     &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
    //     &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)(s)
    //     &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)(s)
    // };
    // combine_spec_entails_always_n!(
    //     spec, lift_action(stronger_next),
    //     lift_action(Cluster::next()),
    //     lift_state(Cluster::crash_disabled()),
    //     lift_state(Cluster::busy_disabled()),
    //     lift_state(Cluster::every_in_flight_msg_has_unique_id()),
    //     lift_state(Cluster::each_object_in_etcd_is_well_formed()),
    //     lift_state(helper_invariants::cluster_resources_is_finite()),
    //     lift_state(helper_invariants::every_create_request_is_well_formed()),
    //     lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
    //     lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)),
    //     lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))
    // );

    // assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
    //     let step = choose |step| Cluster::next_step(s, s_prime, step);
    //     match step {
    //         Step::ApiServerStep(input) => {
    //             let msg = input.get_Some_0();
    //             lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
    //                 s, s_prime, vrs, diff, msg
    //             );
    //             // Prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is maintained.
    //             assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
    //             // Prod for the theorem prover to realize there is a response message.
    //             if msg == req_msg {
    //                 let resp_msg = Cluster::handle_list_request_msg(req_msg, s.kubernetes_api_state).1;
    //                 let resp_objs = resp_msg.content.get_list_response().res.unwrap();

    //                 assert forall |o: DynamicObjectView| #![auto]
    //                 pre(s) && matching_pod_entries(vrs, s_prime.resources()).values().contains(o)
    //                 implies resp_objs.to_set().contains(o) by {
    //                     // Tricky reasoning about .to_seq
    //                     let selector = |o: DynamicObjectView| {
    //                         &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
    //                         &&& o.object_ref().kind == PodView::kind()
    //                     };
    //                     let selected_elements = s.resources().values().filter(selector);
    //                     assert(selected_elements.contains(o));
    //                     lemma_values_finite(s.resources());
    //                     finite_set_to_seq_contains_all_set_elements(selected_elements);
    //                 }

    //                 assert forall |o: DynamicObjectView| #![auto]
    //                 pre(s) && resp_objs.contains(o)
    //                 implies !PodView::unmarshal(o).is_err() by {
    //                     // Tricky reasoning about .to_seq
    //                     let selector = |o: DynamicObjectView| {
    //                         &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
    //                         &&& o.object_ref().kind == PodView::kind()
    //                     };
    //                     let selected_elements = s.resources().values().filter(selector);
    //                     lemma_values_finite(s.resources());
    //                     finite_set_to_seq_contains_all_set_elements(selected_elements);
    //                     assert(resp_objs == selected_elements.to_seq());
    //                     assert(selected_elements.contains(o));
    //                 }
    //                 seq_pred_false_on_all_elements_implies_empty_filter(resp_objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err());

    //                 assert({
    //                     &&& s_prime.in_flight().contains(resp_msg)
    //                     &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
    //                     &&& resp_msg.content.get_list_response().res.is_Ok()
    //                     &&& {
    //                         let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    //                         // The matching pods must be a subset of the response.
    //                         &&& matching_pod_entries(vrs, s_prime.resources()).values().subset_of(resp_objs.to_set())
    //                         &&& objects_to_pods(resp_objs).is_Some()
    //                     }
    //                 });
    //                 assert(post(s_prime));
    //             }
    //         },
    //         _ => {}
    //     }
    // }

    // assert forall |s, s_prime: Cluster| pre(s) && #[trigger] stronger_next(s, s_prime) && Cluster::kubernetes_api_next().forward(input)(s, s_prime) implies post(s_prime) by {
    //     let resp_msg = Cluster::handle_list_request_msg(req_msg, s.kubernetes_api_state).1;
    //     let resp_objs = resp_msg.content.get_list_response().res.unwrap();

    //     assert forall |o: DynamicObjectView| #![auto]
    //     pre(s) && matching_pod_entries(vrs, s_prime.resources()).values().contains(o)
    //     implies resp_objs.to_set().contains(o) by {
    //         // Tricky reasoning about .to_seq
    //         let selector = |o: DynamicObjectView| {
    //             &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
    //             &&& o.object_ref().kind == PodView::kind()
    //         };
    //         let selected_elements = s.resources().values().filter(selector);
    //         assert(selected_elements.contains(o));
    //         lemma_values_finite(s.resources());
    //         finite_set_to_seq_contains_all_set_elements(selected_elements);
    //     }

    //     assert forall |o: DynamicObjectView| #![auto]
    //     pre(s) && resp_objs.contains(o)
    //     implies !PodView::unmarshal(o).is_err() by {
    //         // Tricky reasoning about .to_seq
    //         let selector = |o: DynamicObjectView| {
    //             &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
    //             &&& o.object_ref().kind == PodView::kind()
    //         };
    //         let selected_elements = s.resources().values().filter(selector);
    //         lemma_values_finite(s.resources());
    //         finite_set_to_seq_contains_all_set_elements(selected_elements);
    //         assert(resp_objs == selected_elements.to_seq());
    //         assert(selected_elements.contains(o));
    //     }
    //     seq_pred_false_on_all_elements_implies_empty_filter(resp_objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err());

    //     assert({
    //         &&& s_prime.in_flight().contains(resp_msg)
    //         &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
    //         &&& resp_msg.content.get_list_response().res.is_Ok()
    //         &&& {
    //             let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    //             // The matching pods must be a subset of the response.
    //             &&& matching_pod_entries(vrs, s_prime.resources()).values().subset_of(resp_objs.to_set())
    //             &&& objects_to_pods(resp_objs).is_Some()
    //         }
    //     });
    //     assert(post(s_prime));
    // }

    // Cluster::lemma_pre_leads_to_post_by_kubernetes_api(
    //     spec, input, stronger_next, Cluster::handle_request(), pre, post
    // );
}
    
}
