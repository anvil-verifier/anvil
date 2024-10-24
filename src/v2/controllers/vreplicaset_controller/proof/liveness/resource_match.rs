// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
    proof::{helper_invariants, helper_lemmas, liveness::{api_actions::*}, predicate::*},
};
use crate::vstd_ext::{map_lib::*, set_lib::*, seq_lib::*};
use vstd::{map_lib::*, prelude::*};

verus! {

pub proof fn lemma_from_init_step_to_send_list_pods_req(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, diff: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::Init)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& pending_req_in_flight_at_after_list_pods_step(vrs, controller_id)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        )
{
    let pre = |s: ClusterState| {
        &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetReconcileStep::Init)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: ClusterState| {
        &&& pending_req_in_flight_at_after_list_pods_step(vrs, controller_id)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let input = (None::<Message>, Some(vrs.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, controller_id)(s)
        &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property(
        spec, cluster, controller_id
    );

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_non_interference_property(cluster, controller_id),
        lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, controller_id)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();
                lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, diff, msg
                );
                // Prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is maintained.
                assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
            },
            Step::ControllerStep(..) => {
                VReplicaSetReconcileState::marshal_preserves_integrity();
            },
            _ => {
            }
        }
    }

    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}


pub proof fn lemma_from_after_send_list_pods_req_to_receive_list_pods_resp(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, 
    req_msg: Message, diff: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& req_msg_is_the_in_flight_list_req_at_after_list_pods_step(vrs, controller_id, req_msg)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& exists_resp_in_flight_at_after_list_pods_step(vrs, controller_id)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        )
{
    let pre = |s: ClusterState| {
        &&& req_msg_is_the_in_flight_list_req_at_after_list_pods_step(vrs, controller_id, req_msg)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: ClusterState| {
        &&& exists_resp_in_flight_at_after_list_pods_step(vrs, controller_id)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& helper_invariants::cluster_resources_is_finite()(s)
        &&& helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, controller_id)(s)
        &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property(
        spec, cluster, controller_id
    );

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_non_interference_property(cluster, controller_id),
        lift_state(helper_invariants::cluster_resources_is_finite()),
        lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, controller_id)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();
                lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, diff, msg
                );
                // Prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is maintained.
                assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
                // Prod for the theorem prover to realize there is a response message.
                if msg == req_msg {
                    let resp_msg = handle_list_request_msg(req_msg, s.api_server).1;
                    let resp_objs = resp_msg.content.get_list_response().res.unwrap();

                    assert forall |o: DynamicObjectView| #![auto]
                    pre(s) && matching_pod_entries(vrs, s_prime.resources()).values().contains(o)
                    implies resp_objs.to_set().contains(o) by {
                        // Tricky reasoning about .to_seq
                        let selector = |o: DynamicObjectView| {
                            &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
                            &&& o.object_ref().kind == PodView::kind()
                        };
                        let selected_elements = s.resources().values().filter(selector);
                        assert(selected_elements.contains(o));
                        lemma_values_finite(s.resources());
                        finite_set_to_seq_contains_all_set_elements(selected_elements);
                    }

                    assert forall |o: DynamicObjectView| #![auto]
                    pre(s) && resp_objs.contains(o)
                    implies !PodView::unmarshal(o).is_err() by {
                        // Tricky reasoning about .to_seq
                        let selector = |o: DynamicObjectView| {
                            &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
                            &&& o.object_ref().kind == PodView::kind()
                        };
                        let selected_elements = s.resources().values().filter(selector);
                        lemma_values_finite(s.resources());
                        finite_set_to_seq_contains_all_set_elements(selected_elements);
                        assert(resp_objs == selected_elements.to_seq());
                        assert(selected_elements.contains(o));
                    }
                    seq_pred_false_on_all_elements_implies_empty_filter(resp_objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err());

                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_list_response().res.is_Ok()
                        &&& {
                            let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                            // The matching pods must be a subset of the response.
                            &&& matching_pod_entries(vrs, s_prime.resources()).values().subset_of(resp_objs.to_set())
                            &&& objects_to_pods(resp_objs).is_Some()
                        }
                    });
                    assert(post(s_prime));
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let resp_msg = handle_list_request_msg(req_msg, s.api_server).1;
        let resp_objs = resp_msg.content.get_list_response().res.unwrap();

        assert forall |o: DynamicObjectView| #![auto]
        pre(s) && matching_pod_entries(vrs, s_prime.resources()).values().contains(o)
        implies resp_objs.to_set().contains(o) by {
            // Tricky reasoning about .to_seq
            let selector = |o: DynamicObjectView| {
                &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
                &&& o.object_ref().kind == PodView::kind()
            };
            let selected_elements = s.resources().values().filter(selector);
            assert(selected_elements.contains(o));
            lemma_values_finite(s.resources());
            finite_set_to_seq_contains_all_set_elements(selected_elements);
        }

        assert forall |o: DynamicObjectView| #![auto]
        pre(s) && resp_objs.contains(o)
        implies !PodView::unmarshal(o).is_err() by {
            // Tricky reasoning about .to_seq
            let selector = |o: DynamicObjectView| {
                &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
                &&& o.object_ref().kind == PodView::kind()
            };
            let selected_elements = s.resources().values().filter(selector);
            lemma_values_finite(s.resources());
            finite_set_to_seq_contains_all_set_elements(selected_elements);
            assert(resp_objs == selected_elements.to_seq());
            assert(selected_elements.contains(o));
            assert(s.resources().contains_value(o));
        }
        seq_pred_false_on_all_elements_implies_empty_filter(resp_objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err());

        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_list_response().res.is_Ok()
            &&& {
                let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                // The matching pods must be a subset of the response.
                &&& matching_pod_entries(vrs, s_prime.resources()).values().subset_of(resp_objs.to_set())
                &&& objects_to_pods(resp_objs).is_Some()
            }
        });
        assert(post(s_prime));
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}
    
}
