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
use vstd::{map::*, map_lib::*, math::*, prelude::*};

verus! {

// -------------- Leads-to Chaining Reasoning --------------

pub proof fn lemma_from_diff_and_init_to_current_state_matches(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, diff: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        vrs.state_validation(),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id)))),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(lift_state(current_state_matches(vrs)))
        )
{
    let invariants = {
        &&& spec.entails(always(lift_action(cluster.next())))
        &&& spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i)))
        &&& spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1))))
        &&& spec.entails(always(lift_state(Cluster::desired_state_is(vrs))))
        &&& spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
        &&& spec.entails(always(lift_state(Cluster::crash_disabled(controller_id))))
        &&& spec.entails(always(lift_state(Cluster::req_drop_disabled())))
        &&& spec.entails(always(lift_state(Cluster::pod_monkey_disabled())))
        &&& spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id())))
        &&& spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
        &&& spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
        &&& spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>())))
        &&& spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
        &&& spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
        &&& spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref()))))
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id))))

        &&& spec.entails(always(lift_state(Cluster::etcd_is_finite())))
        &&& spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id))))
        &&& spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods())))
        &&& spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs))))
        &&& spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods())))
        &&& spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id))))
        &&& spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id))))
        &&& spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))))
        &&& spec.entails(always(lift_state(helper_invariants::at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id))))
    };
    let pre = |diff: int| lift_state(
        |s: ClusterState| {
            &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let list_req = |diff: int| lift_state(
        |s: ClusterState| {
            &&& pending_req_in_flight_at_after_list_pods_step(vrs, controller_id)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let list_req_msg = |req_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
            &&& req_msg_is_the_in_flight_list_req_at_after_list_pods_step(vrs, controller_id, req_msg)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let list_resp = |diff: int| lift_state(
        |s: ClusterState| {
            &&& exists_resp_in_flight_at_after_list_pods_step(vrs, controller_id)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // Deal with transition from init to listing the pods.
    lemma_from_init_step_to_send_list_pods_req(vrs, spec, cluster, controller_id, diff);

    assert forall |req_msg: Message|
                 invariants implies #[trigger] spec.entails(list_req_msg(req_msg, diff).leads_to(list_resp(diff))) by {
        lemma_from_after_send_list_pods_req_to_receive_list_pods_resp(vrs, spec, cluster, controller_id, req_msg, diff);
    };
    leads_to_exists_intro(spec, |req_msg| list_req_msg(req_msg, diff), list_resp(diff));


    assert_by(spec.entails(list_req(diff).leads_to(tla_exists(|req_msg| list_req_msg(req_msg, diff)))), {
        assert forall |ex| #[trigger] list_req(diff).satisfied_by(ex)
            implies tla_exists(|req_msg| list_req_msg(req_msg, diff)).satisfied_by(ex) by {
            let req_msg = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
            assert((|req_msg: Message| list_req_msg(req_msg, diff))(req_msg).satisfied_by(ex));
        };
        entails_implies_leads_to(spec, list_req(diff), tla_exists(|req_msg| list_req_msg(req_msg, diff)));
    });

    leads_to_trans_n!(
        spec,
        pre(diff),
        list_req(diff),
        tla_exists(|req_msg| list_req_msg(req_msg, diff)),
        list_resp(diff)
    );

    // Now we've listed the pods, perform different behaviors accoding to the difference.
    if diff < 0 {
        let create_resp = |diff: int| lift_state(
            |s: ClusterState| {
                &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, controller_id, abs(diff))(s)
                &&& num_diff_pods_is(vrs, diff)(s)
            }
        );

        // Add first create pod request after listing pods to leads-to chain.
        lemma_from_after_receive_list_pods_resp_to_receive_create_pod_resp(vrs, spec, cluster, controller_id, diff);
        leads_to_trans_n!(
            spec,
            pre(diff),
            list_resp(diff),
            create_resp(diff + 1)
        );

        // Is this enough?
        if diff + 1 == 0 {
            // If so, pre(diff) ~> current_state_matches(vrs) trivially.
            assert forall |ex| #![auto] create_resp(0).satisfied_by(ex) implies lift_state(current_state_matches(vrs)).satisfied_by(ex) by {
                let s = ex.head();
                let resources = s.resources();

                // current_state_matches and num_diff_pods are defined subtly differently,
                // needs equality asserted explicitly.
                let f1 = |key: ObjectRef| {
                    let obj = resources[key];
                    &&& resources.contains_key(key)
                    &&& owned_selector_match_is(vrs, obj)
                };
                let f2 = |key: ObjectRef| {
                    &&& s.resources().contains_key(key)
                    &&& owned_selector_match_is(vrs, s.resources()[key])
                };

                assert(f1 == f2);
            }

            entails_implies_leads_to(spec, create_resp(diff + 1), lift_state(current_state_matches(vrs)));
            leads_to_trans_n!(
                spec,
                pre(diff),
                create_resp(diff + 1),
                lift_state(current_state_matches(vrs))
            );
            return;
        }

        // In this branch, we need to convert negative integers to natural numbers for
        // the predicate to fit the rule leads_to_rank_step_one.
        let ranking_pred = |n: nat| create_resp(-n);

        // Useful assertions to let us chain in and out of ranking_pred
        assert forall |n: nat| #![trigger create_resp(-n)]
                    spec.entails(create_resp(-n).leads_to(ranking_pred(n))) by {
            entails_implies_leads_to(spec, create_resp(-n), ranking_pred(n));
        };

        assert forall |n: nat| #![trigger create_resp(-n)]
                    spec.entails(ranking_pred(n).leads_to(create_resp(-n))) by {
            entails_implies_leads_to(spec, ranking_pred(n), create_resp(-n));
        };

         // Proving n > 0 => ranking_pred(n) ~> ranking_pred(n - 1)
        assert forall |n: nat| #![trigger ranking_pred(n)]
                    n > 0 implies spec.entails(ranking_pred(n).leads_to(ranking_pred((n - 1) as nat))) by {
            let diff = -n;
            lemma_from_after_receive_create_pod_resp_to_receive_create_pod_resp(vrs, spec, cluster, controller_id, diff);

            leads_to_trans_n!(
                spec,
                ranking_pred(n),
                create_resp(diff),
                create_resp(diff + 1),
                ranking_pred((n - 1) as nat)
            );
        };

        // Apply ranking function lemma
        leads_to_rank_step_one(spec, ranking_pred);

        // Chain everything
        assert forall |ex| #![auto] create_resp(0).satisfied_by(ex) implies lift_state(current_state_matches(vrs)).satisfied_by(ex) by {
            let s = ex.head();
            let resources = s.resources();

            // current_state_matches and num_diff_pods are defined subtly differently,
            // needs equality asserted explicitly.
            let f1 = |key: ObjectRef| {
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& owned_selector_match_is(vrs, obj)
            };
            let f2 = |key: ObjectRef| {
                &&& s.resources().contains_key(key)
                &&& owned_selector_match_is(vrs, s.resources()[key])
            };

            assert(f1 == f2);
        }

        entails_implies_leads_to(spec, create_resp(0), lift_state(current_state_matches(vrs)));
        leads_to_trans_n!(
            spec,
            pre(diff),
            create_resp(diff + 1),
            ranking_pred(-(diff + 1) as nat),
            ranking_pred(0),
            create_resp(0),
            lift_state(current_state_matches(vrs))
        );
    } else if diff > 0 {
        let delete_resp = |diff: int| lift_state(
            |s: ClusterState| {
                &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, abs(diff))(s)
                &&& num_diff_pods_is(vrs, diff)(s)
            }
        );

        // Add first delete pod request after listing pods to leads-to chain.
        lemma_from_after_receive_list_pods_resp_to_receive_delete_pod_resp(vrs, spec, cluster, controller_id, diff);
        leads_to_trans_n!(
            spec,
            pre(diff),
            list_resp(diff),
            delete_resp(diff - 1)
        );

        // Is this enough?
        if diff - 1 == 0 {
            // If so, pre(diff) ~> current_state_matches(vrs) trivially.
            assert forall |ex| #![auto] delete_resp(0).satisfied_by(ex) implies lift_state(current_state_matches(vrs)).satisfied_by(ex) by {
                let s = ex.head();
                let resources = s.resources();

                // current_state_matches and num_diff_pods are defined subtly differently,
                // needs equality asserted explicitly.
                let f1 = |key: ObjectRef| {
                    let obj = resources[key];
                    &&& resources.contains_key(key)
                    &&& owned_selector_match_is(vrs, obj)
                };
                let f2 = |key: ObjectRef| {
                    &&& s.resources().contains_key(key)
                    &&& owned_selector_match_is(vrs, s.resources()[key])
                };

                assert(f1 == f2);
            }

            entails_implies_leads_to(spec, delete_resp(diff - 1), lift_state(current_state_matches(vrs)));
            leads_to_trans_n!(
                spec,
                pre(diff),
                delete_resp(diff - 1),
                lift_state(current_state_matches(vrs))
            );
            return;
        }

        let ranking_pred = |n: nat| delete_resp(n as int);

        // Useful assertions to let us chain in and out of ranking_pred
        assert forall |n: nat| #![trigger ranking_pred(n)]
                    spec.entails(delete_resp(n as int).leads_to(ranking_pred(n))) by {
            entails_implies_leads_to(spec, delete_resp(n as int), ranking_pred(n));
        };

        assert forall |n: nat| #![trigger ranking_pred(n)]
                    spec.entails(ranking_pred(n).leads_to(delete_resp(n as int))) by {
            entails_implies_leads_to(spec, ranking_pred(n), delete_resp(n as int));
        };

         // Proving n > 0 => ranking_pred(n) ~> ranking_pred(n - 1)
        assert forall |n: nat| #![trigger ranking_pred(n)]
                    n > 0 implies spec.entails(ranking_pred(n).leads_to(ranking_pred((n - 1) as nat))) by {
            let diff = n as int;
            lemma_from_after_receive_delete_pod_resp_to_receive_delete_pod_resp(vrs, spec, cluster, controller_id, diff);

            leads_to_trans_n!(
                spec,
                ranking_pred(n),
                delete_resp(diff),
                delete_resp(diff - 1),
                ranking_pred((n - 1) as nat)
            );
        };

        // Apply ranking function lemma
        leads_to_rank_step_one(spec, ranking_pred);

        // Chain everything
        assert forall |ex| #![auto] delete_resp(0).satisfied_by(ex) implies lift_state(current_state_matches(vrs)).satisfied_by(ex) by {
            let s = ex.head();
            let resources = s.resources();

            // current_state_matches and num_diff_pods are defined subtly differently,
            // needs equality asserted explicitly.
            let f1 = |key: ObjectRef| {
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& owned_selector_match_is(vrs, obj)
            };
            let f2 = |key: ObjectRef| {
                &&& s.resources().contains_key(key)
                &&& owned_selector_match_is(vrs, s.resources()[key])
            };

            assert(f1 == f2);
        }

        entails_implies_leads_to(spec, delete_resp(0), lift_state(current_state_matches(vrs)));
        leads_to_trans_n!(
            spec,
            pre(diff),
            delete_resp(diff - 1),
            ranking_pred((diff - 1) as nat),
            ranking_pred(0),
            delete_resp(0),
            lift_state(current_state_matches(vrs))
        );
    } else {
        // diff = 0
        // list_resp(diff) ~> current_state_matches(vrs) trivially.
        assert forall |ex| #![auto] list_resp(0).satisfied_by(ex) implies lift_state(current_state_matches(vrs)).satisfied_by(ex) by {
            let s = ex.head();
            let resources = s.resources();

            // current_state_matches and num_diff_pods are defined subtly differently,
            // needs equality asserted explicitly.
            let f1 = |key: ObjectRef| {
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& owned_selector_match_is(vrs, obj)
            };
            let f2 = |key: ObjectRef| {
                &&& s.resources().contains_key(key)
                &&& owned_selector_match_is(vrs, s.resources()[key])
            };

            assert(f1 == f2);
        }

        entails_implies_leads_to(spec, list_resp(diff), lift_state(current_state_matches(vrs)));
        leads_to_trans_n!(
            spec,
            pre(diff),
            list_resp(diff),
            lift_state(current_state_matches(vrs))
        );
    }
}

// Create lemmas.

pub proof fn lemma_from_after_receive_list_pods_resp_to_receive_create_pod_resp(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, diff: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        vrs.state_validation(),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& exists_resp_in_flight_at_after_list_pods_step(vrs, controller_id)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff + 1)(s)
                    }
                )
            )
        ),
{
    let list_resp = |diff: int| lift_state(
        |s: ClusterState| {
            &&& exists_resp_in_flight_at_after_list_pods_step(vrs, controller_id)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let list_resp_msg = |resp_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
            &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_req_msg = |req_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
        &&& req_msg_is_the_in_flight_create_request_at_after_create_pod_step(vrs, controller_id, req_msg, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_req = |diff: int| lift_state(
        |s: ClusterState| {
            &&& pending_req_in_flight_at_after_create_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_resp_msg = |resp_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_resp = |diff: int| lift_state(
        |s: ClusterState| {
            &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, controller_id, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // Apply two lemmas relating to the first created pod.
    assert forall |resp_msg: Message|
                diff < 0 implies #[trigger] spec.entails(list_resp_msg(resp_msg, diff).leads_to(create_req(diff))) by {
        lemma_from_after_receive_list_pods_resp_to_send_create_pod_req(vrs, spec, cluster, controller_id, resp_msg, diff);
    };
    assert forall |req_msg: Message|
                diff < 0 implies #[trigger] spec.entails(create_req_msg(req_msg, diff).leads_to(create_resp(diff + 1))) by {
        lemma_from_after_send_create_pod_req_to_receive_ok_resp(vrs, spec, cluster, controller_id, req_msg, diff);
    };

    // Chain lemmas by transitivity.
    leads_to_exists_intro(spec, |resp_msg: Message| list_resp_msg(resp_msg, diff), create_req(diff));
    leads_to_exists_intro(spec, |req_msg: Message| create_req_msg(req_msg, diff), create_resp(diff + 1));
    assert_by(
        spec.entails(list_resp(diff).leads_to(tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, diff)))),
        {
            assert forall |ex| #[trigger] list_resp(diff).satisfied_by(ex)
                implies tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, diff)).satisfied_by(ex) by {
                let s = ex.head();
                let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_list_response().res.is_Ok()
                    &&& {
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        // The matching pods must be a subset of the response.
                        &&& matching_pod_entries(vrs, s.resources()).values().subset_of(resp_objs.to_set())
                        &&& objects_to_pods(resp_objs).is_Some()
                        &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
                    }
                };
                assert((|resp_msg: Message| list_resp_msg(resp_msg, diff))(resp_msg).satisfied_by(ex));
            };
            entails_implies_leads_to(spec, list_resp(diff), tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, diff)));
        }
    );
    assert_by(
        spec.entails(create_req(diff).leads_to(tla_exists(|req_msg: Message| create_req_msg(req_msg, diff)))),
        {
            assert forall |ex| #[trigger] create_req(diff).satisfied_by(ex)
                implies tla_exists(|req_msg: Message| create_req_msg(req_msg, diff)).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                assert((|req_msg: Message| create_req_msg(req_msg, diff))(req_msg).satisfied_by(ex));
            };
            entails_implies_leads_to(spec, create_req(diff), tla_exists(|req_msg: Message| create_req_msg(req_msg, diff)));
        }
    );
    leads_to_trans_n!(
        spec,
        list_resp(diff),
        tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, diff)),
        create_req(diff),
        tla_exists(|req_msg: Message| create_req_msg(req_msg, diff)),
        create_resp(diff + 1)
    );
}

pub proof fn lemma_from_after_receive_create_pod_resp_to_receive_create_pod_resp(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, diff: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        vrs.state_validation(),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id)))),
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, controller_id, abs(diff))(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff + 1)(s)
                    }
                )
            )
        ),
{
    let create_req_msg = |req_msg: Message, diff: int| lift_state(|s: ClusterState| {
        &&& req_msg_is_the_in_flight_create_request_at_after_create_pod_step(vrs, controller_id, req_msg, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    });
    let create_req = |diff: int| lift_state(
        |s: ClusterState| {
            &&& pending_req_in_flight_at_after_create_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_resp_msg = |resp_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_resp = |diff: int| lift_state(
        |s: ClusterState| {
            &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, controller_id, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // Apply two lemmas relating to subsequent created pods.
    assert forall |resp_msg: Message|
                diff < 0 implies #[trigger] spec.entails(create_resp_msg(resp_msg, diff).leads_to(create_req(diff))) by {
        lemma_from_after_receive_ok_resp_to_send_create_pod_req(vrs, spec, cluster, controller_id, resp_msg, diff);
    };
    assert forall |req_msg: Message|
                diff < 0 implies #[trigger] spec.entails(create_req_msg(req_msg, diff).leads_to(create_resp(diff + 1))) by {
        lemma_from_after_send_create_pod_req_to_receive_ok_resp(vrs, spec, cluster, controller_id, req_msg, diff);
    };

    // Chain the lemmas by transitivity.
    leads_to_exists_intro(spec, |resp_msg: Message| create_resp_msg(resp_msg, diff), create_req(diff));
    leads_to_exists_intro(spec, |req_msg: Message| create_req_msg(req_msg, diff), create_resp(diff + 1));
    assert_by(
        spec.entails(create_req(diff).leads_to(tla_exists(|req_msg: Message| create_req_msg(req_msg, diff)))),
        {
            assert forall |ex| #[trigger] create_req(diff).satisfied_by(ex)
                implies tla_exists(|req_msg: Message| create_req_msg(req_msg, diff)).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                assert((|req_msg: Message| create_req_msg(req_msg, diff))(req_msg).satisfied_by(ex));
            };
            entails_implies_leads_to(spec, create_req(diff), tla_exists(|req_msg: Message| create_req_msg(req_msg, diff)));
        }
    );
    assert_by(
        spec.entails(create_resp(diff).leads_to(tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, diff)))),
        {
            assert forall |ex| #[trigger] create_resp(diff).satisfied_by(ex)
                implies tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, diff)).satisfied_by(ex) by {
                let s = ex.head();
                let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_create_response().res.is_Ok()
                };
                assert((|resp_msg: Message| create_resp_msg(resp_msg, diff))(resp_msg).satisfied_by(ex));
            };
            entails_implies_leads_to(spec, create_resp(diff), tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, diff)));
        }
    );

    leads_to_trans_n!(
        spec,
        create_resp(diff),
        tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, diff)),
        create_req(diff),
        tla_exists(|req_msg: Message| create_req_msg(req_msg, diff)),
        create_resp(diff + 1)
    );
}

// Delete lemmas.

pub proof fn lemma_from_after_receive_list_pods_resp_to_receive_delete_pod_resp(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, diff: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        vrs.state_validation(),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id)))),
        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& exists_resp_in_flight_at_after_list_pods_step(vrs, controller_id)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, (diff - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff - 1)(s)
                    }
                )
            )
        ),
{
    let list_resp = |diff: int| lift_state(
        |s: ClusterState| {
            &&& exists_resp_in_flight_at_after_list_pods_step(vrs, controller_id)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let list_resp_msg = |resp_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
            &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_req_msg = |req_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
        &&& req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(vrs, controller_id, req_msg, (diff - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_req = |diff: int| lift_state(
        |s: ClusterState| {
            &&& pending_req_in_flight_at_after_delete_pod_step(vrs, controller_id, (diff - 1) as nat)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_resp_msg = |resp_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_resp = |diff: int| lift_state(
        |s: ClusterState| {
            &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // Apply two lemmas relating to the first deleted pod.
    assert forall |resp_msg: Message|
                diff > 0 implies #[trigger] spec.entails(list_resp_msg(resp_msg, diff).leads_to(delete_req(diff))) by {
        lemma_from_after_receive_list_pods_resp_to_send_delete_pod_req(vrs, spec, cluster, controller_id, resp_msg, diff);
    };
    assert forall |req_msg: Message|
                diff > 0 implies #[trigger] spec.entails(delete_req_msg(req_msg, diff).leads_to(delete_resp(diff - 1))) by {
        lemma_from_after_send_delete_pod_req_to_receive_ok_resp(vrs, spec, cluster, controller_id, req_msg, diff);
    };

    // Chain lemmas by transitivity.
    leads_to_exists_intro(spec, |resp_msg: Message| list_resp_msg(resp_msg, diff), delete_req(diff));
    leads_to_exists_intro(spec, |req_msg: Message| delete_req_msg(req_msg, diff), delete_resp(diff - 1));
    assert_by(
        spec.entails(list_resp(diff).leads_to(tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, diff)))),
        {
            assert forall |ex| #[trigger] list_resp(diff).satisfied_by(ex)
                implies tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, diff)).satisfied_by(ex) by {
                let s = ex.head();
                let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_list_response().res.is_Ok()
                    &&& {
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        // The matching pods must be a subset of the response.
                        &&& matching_pod_entries(vrs, s.resources()).values().subset_of(resp_objs.to_set())
                        &&& objects_to_pods(resp_objs).is_Some()
                        &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
                    }
                };
                assert((|resp_msg: Message| list_resp_msg(resp_msg, diff))(resp_msg).satisfied_by(ex));
            };
            entails_implies_leads_to(spec, list_resp(diff), tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, diff)));
        }
    );
    assert_by(
        spec.entails(delete_req(diff).leads_to(tla_exists(|req_msg: Message| delete_req_msg(req_msg, diff)))),
        {
            assert forall |ex| #[trigger] delete_req(diff).satisfied_by(ex)
                implies tla_exists(|req_msg: Message| delete_req_msg(req_msg, diff)).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                assert((|req_msg: Message| delete_req_msg(req_msg, diff))(req_msg).satisfied_by(ex));
            };
            entails_implies_leads_to(spec, delete_req(diff), tla_exists(|req_msg: Message| delete_req_msg(req_msg, diff)));
        }
    );
    leads_to_trans_n!(
        spec,
        list_resp(diff),
        tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, diff)),
        delete_req(diff),
        tla_exists(|req_msg: Message| delete_req_msg(req_msg, diff)),
        delete_resp(diff - 1)
    );
}

pub proof fn lemma_from_after_receive_delete_pod_resp_to_receive_delete_pod_resp(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, diff: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        vrs.state_validation(),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id)))),
        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, diff as nat)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, (diff - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff - 1)(s)
                    }
                )
            )
        ),
{
    let delete_req_msg = |req_msg: Message, diff: int| lift_state(|s: ClusterState| {
        &&& req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(vrs, controller_id, req_msg, (diff - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    });
    let delete_req = |diff: int| lift_state(
        |s: ClusterState| {
            &&& pending_req_in_flight_at_after_delete_pod_step(vrs, controller_id, (diff - 1) as nat)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_resp_msg = |resp_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_resp = |diff: int| lift_state(
        |s: ClusterState| {
            &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // Apply two lemmas relating to subsequent deleted pods.
    assert forall |resp_msg: Message|
                diff > 0 implies #[trigger] spec.entails(delete_resp_msg(resp_msg, diff).leads_to(delete_req(diff))) by {
        lemma_from_after_receive_ok_resp_to_send_delete_pod_req(vrs, spec, cluster, controller_id, resp_msg, diff);
    };
    assert forall |req_msg: Message|
                diff > 0 implies #[trigger] spec.entails(delete_req_msg(req_msg, diff).leads_to(delete_resp(diff - 1))) by {
        lemma_from_after_send_delete_pod_req_to_receive_ok_resp(vrs, spec, cluster, controller_id, req_msg, diff);
    };

    // Chain the lemmas by transitivity.
    leads_to_exists_intro(spec, |resp_msg: Message| delete_resp_msg(resp_msg, diff), delete_req(diff));
    leads_to_exists_intro(spec, |req_msg: Message| delete_req_msg(req_msg, diff), delete_resp(diff - 1));
    assert_by(
        spec.entails(delete_req(diff).leads_to(tla_exists(|req_msg: Message| delete_req_msg(req_msg, diff)))),
        {
            assert forall |ex| #[trigger] delete_req(diff).satisfied_by(ex)
                implies tla_exists(|req_msg: Message| delete_req_msg(req_msg, diff)).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                assert((|req_msg: Message| delete_req_msg(req_msg, diff))(req_msg).satisfied_by(ex));
            };
            entails_implies_leads_to(spec, delete_req(diff), tla_exists(|req_msg: Message| delete_req_msg(req_msg, diff)));
        }
    );
    assert_by(
        spec.entails(delete_resp(diff).leads_to(tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, diff)))),
        {
            assert forall |ex| #[trigger] delete_resp(diff).satisfied_by(ex)
                implies tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, diff)).satisfied_by(ex) by {
                let s = ex.head();
                let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_delete_response().res.is_Ok()
                };
                assert((|resp_msg: Message| delete_resp_msg(resp_msg, diff))(resp_msg).satisfied_by(ex));
            };
            entails_implies_leads_to(spec, delete_resp(diff), tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, diff)));
        }
    );

    leads_to_trans_n!(
        spec,
        delete_resp(diff),
        tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, diff)),
        delete_req(diff),
        tla_exists(|req_msg: Message| delete_req_msg(req_msg, diff)),
        delete_resp(diff - 1)
    );
}

// -------------------- WF1 Reasoning ----------------------

// List lemmas

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
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init)(s)
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
        &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init)(s)
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
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s)
        &&& helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s)
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
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_non_interference_property(cluster, controller_id),
        lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
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
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))))
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
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s)
        &&& helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s)
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
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_non_interference_property(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
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
                    seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(resp_objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err());

                    // TODO: Shorten up this proof.
                    assert_by(objects_to_pods(resp_objs).unwrap().no_duplicates(), {
                        let selector = |o: DynamicObjectView| {
                            &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
                            &&& o.object_ref().kind == PodView::kind()
                        };
                        let selected_elements = s.resources().values().filter(selector);
                        lemma_values_finite(s.resources());
                        finite_set_to_seq_has_no_duplicates(selected_elements);
                        let selected_elements_seq = selected_elements.to_seq();
                        let pods_seq = objects_to_pods(selected_elements_seq).unwrap();
                        assert(selected_elements_seq.no_duplicates());

                        assert forall |x: DynamicObjectView, y: DynamicObjectView| #![auto]
                            x != y 
                            && selected_elements_seq.contains(x) 
                            && selected_elements_seq.contains(y) implies x.object_ref() != y.object_ref() by {
                            finite_set_to_seq_contains_all_set_elements(selected_elements);
                            assert(selected_elements.contains(x));
                            assert(selected_elements.contains(y));
                        }

                        let lem = forall |x: DynamicObjectView, y: DynamicObjectView| #![auto]
                            x != y 
                            && selected_elements_seq.contains(x) 
                            && selected_elements_seq.contains(y) ==> x.object_ref() != y.object_ref();

                        assert forall |i: int, j: int| #![auto] 
                            0 <= i && i < pods_seq.len() && (0 <= j && j < pods_seq.len()) && !(i == j)
                            && objects_to_pods(selected_elements_seq).is_Some()
                            && lem
                            implies pods_seq[i] != pods_seq[j] by {
                            let o1 = selected_elements_seq[i];
                            let o2 = selected_elements_seq[j];
                            assert(o1.object_ref() != o2.object_ref());
                            PodView::marshal_preserves_integrity();
                            seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(selected_elements_seq, |o: DynamicObjectView| PodView::unmarshal(o).is_err());
                            assert(selected_elements_seq.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0);
                            assert(selected_elements_seq.contains(o1));
                            assert(selected_elements_seq.contains(o2));
                        }

                        assert(pods_seq.no_duplicates());
                    });

                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_list_response().res.is_Ok()
                        &&& {
                            let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                            // The matching pods must be a subset of the response.
                            &&& matching_pod_entries(vrs, s_prime.resources()).values().subset_of(resp_objs.to_set())
                            &&& objects_to_pods(resp_objs).is_Some()
                            &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
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
        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(resp_objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err());

        // TODO: Shorten up this proof.
        assert_by(objects_to_pods(resp_objs).unwrap().no_duplicates(), {
            let selector = |o: DynamicObjectView| {
                &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
                &&& o.object_ref().kind == PodView::kind()
            };
            let selected_elements = s.resources().values().filter(selector);
            lemma_values_finite(s.resources());
            finite_set_to_seq_has_no_duplicates(selected_elements);
            let selected_elements_seq = selected_elements.to_seq();
            let pods_seq = objects_to_pods(selected_elements_seq).unwrap();
            assert(selected_elements_seq.no_duplicates());

            assert forall |x: DynamicObjectView, y: DynamicObjectView| #![auto]
                x != y 
                && selected_elements_seq.contains(x) 
                && selected_elements_seq.contains(y) implies x.object_ref() != y.object_ref() by {
                finite_set_to_seq_contains_all_set_elements(selected_elements);
                assert(selected_elements.contains(x));
                assert(selected_elements.contains(y));
            }

            let lem = forall |x: DynamicObjectView, y: DynamicObjectView| #![auto]
                x != y 
                && selected_elements_seq.contains(x) 
                && selected_elements_seq.contains(y) ==> x.object_ref() != y.object_ref();

            assert forall |i: int, j: int| #![auto] 
                0 <= i && i < pods_seq.len() && (0 <= j && j < pods_seq.len()) && !(i == j)
                && objects_to_pods(selected_elements_seq).is_Some()
                && lem
                implies pods_seq[i] != pods_seq[j] by {
                let o1 = selected_elements_seq[i];
                let o2 = selected_elements_seq[j];
                assert(o1.object_ref() != o2.object_ref());
                PodView::marshal_preserves_integrity();
                seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(selected_elements_seq, |o: DynamicObjectView| PodView::unmarshal(o).is_err());
                assert(selected_elements_seq.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0);
                assert(selected_elements_seq.contains(o1));
                assert(selected_elements_seq.contains(o2));
            }

            assert(pods_seq.no_duplicates());
        });

        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_list_response().res.is_Ok()
            &&& {
                let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                // The matching pods must be a subset of the response.
                &&& matching_pod_entries(vrs, s_prime.resources()).values().subset_of(resp_objs.to_set())
                &&& objects_to_pods(resp_objs).is_Some()
                &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
            }
        });
        assert(post(s_prime));
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

// Create lemmas

pub proof fn lemma_from_after_receive_list_pods_resp_to_send_create_pod_req(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
    resp_msg: Message, diff: int
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
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        vrs.state_validation(),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& pending_req_in_flight_at_after_create_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
    let pre = |s: ClusterState| {
        &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: ClusterState| {
        &&& pending_req_in_flight_at_after_create_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let input = (Some(resp_msg), Some(vrs.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s)
        &&& helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s)
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
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        lifted_vrs_non_interference_property(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
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
            Step::ControllerStep(input) => {
                if input.0 == controller_id
                    && input.1 == Some(resp_msg) 
                    && input.2 == Some(vrs.object_ref()) {
                    VReplicaSetReconcileState::marshal_preserves_integrity();
                    helper_lemmas::lemma_filtered_pods_set_equals_matching_pods(
                        s, vrs, cluster, controller_id, resp_msg
                    );
                }
            },
            _ => {}
        }
    }

    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

// TODO: Investigate flaky proof.
pub proof fn lemma_from_after_send_create_pod_req_to_receive_ok_resp(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
    req_msg: Message, diff: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),

        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& req_msg_is_the_in_flight_create_request_at_after_create_pod_step(vrs, controller_id, req_msg, (abs(diff) - 1) as nat)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff + 1)(s)
                    }
                )
            )
        ),
{
    let pre = |s: ClusterState| {
        &&& req_msg_is_the_in_flight_create_request_at_after_create_pod_step(vrs, controller_id, req_msg, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: ClusterState| {
        &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff + 1)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s)
        &&& helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s)
        &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)(s)
        &&& helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property(
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
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_non_interference_property(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)),
        lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id))
    );


    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();
                // Case 1: We're processing the create request
                if msg == req_msg {
                    let resp_msg = handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).1;
                    let req = req_msg.content.get_create_request();
                    let created_obj = DynamicObjectView {
                        kind: req.obj.kind,
                        metadata: ObjectMetaView {
                            // Set name for new object if name is not provided, here we generate
                            // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
                            name: if req.obj.metadata.name.is_Some() {
                                req.obj.metadata.name
                            } else {
                                Some(generate_name(s.api_server))
                            },
                            namespace: Some(req.namespace), // Set namespace for new object
                            resource_version: Some(s.api_server.resource_version_counter), // Set rv for new object
                            uid: Some(s.api_server.uid_counter), // Set uid for new object
                            deletion_timestamp: None, // Unset deletion timestamp for new object
                            ..req.obj.metadata
                        },
                        spec: req.obj.spec,
                        status: marshalled_default_status(req.obj.kind, cluster.installed_types), // Overwrite the status with the default one
                    };
                    let key = created_obj.object_ref();

                    // Asserts properties about the response message
                    generated_name_is_unique(s.api_server);
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_create_response().res.is_Ok()
                    });

                    // Asserts properties about the newly inserted object.
                    assert_maps_equal!(s.resources().insert(key, created_obj) == s_prime.resources());
                    assert(s.resources().len() + 1 == s_prime.resources().len());
                    assert(created_obj.metadata.owner_references.unwrap()[0] == vrs.controller_owner_ref());
                    assert(owned_selector_match_is(vrs, created_obj));

                    // Small prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is increased.
                    a_submap_of_a_finite_map_is_finite(matching_pod_entries(vrs, s.resources()), s.resources());
                    assert(matching_pod_entries(vrs, s.resources()).insert(key, created_obj) == matching_pod_entries(vrs, s_prime.resources()));
                } else {
                    assert_by(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()), {
                        a_submap_of_a_finite_map_is_finite(matching_pod_entries(vrs, s.resources()), s.resources());
                        lemma_api_request_not_made_by_vrs_maintains_matching_pods(
                            s, s_prime, vrs, cluster, controller_id, diff, msg, Some(req_msg),
                        );
                    });
                }                
            },
            _ => {}
        }
    }

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let resp_msg = handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).1;
        let req = req_msg.content.get_create_request();
        let created_obj = DynamicObjectView {
            kind: req.obj.kind,
            metadata: ObjectMetaView {
                // Set name for new object if name is not provided, here we generate
                // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
                name: if req.obj.metadata.name.is_Some() {
                    req.obj.metadata.name
                } else {
                    Some(generate_name(s.api_server))
                },
                namespace: Some(req.namespace), // Set namespace for new object
                resource_version: Some(s.api_server.resource_version_counter), // Set rv for new object
                uid: Some(s.api_server.uid_counter), // Set uid for new object
                deletion_timestamp: None, // Unset deletion timestamp for new object
                ..req.obj.metadata
            },
            spec: req.obj.spec,
            status: marshalled_default_status(req.obj.kind, cluster.installed_types), // Overwrite the status with the default one
        };
        let key = created_obj.object_ref();

        // Asserts properties about the response message
        generated_name_is_unique(s.api_server);
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_create_response().res.is_Ok()
        });

        // Asserts properties about the newly inserted object.
        assert_maps_equal!(s.resources().insert(key, created_obj) == s_prime.resources());
        assert(s.resources().len() + 1 == s_prime.resources().len());
        assert(created_obj.metadata.owner_references.unwrap()[0] == vrs.controller_owner_ref());
        assert(owned_selector_match_is(vrs, created_obj));

        // Small prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is increased.
        a_submap_of_a_finite_map_is_finite(matching_pod_entries(vrs, s.resources()), s.resources());
        assert(matching_pod_entries(vrs, s.resources()).insert(key, created_obj) == matching_pod_entries(vrs, s_prime.resources()));
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

pub proof fn lemma_from_after_receive_ok_resp_to_send_create_pod_req(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
    resp_msg: Message, diff: int
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
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        vrs.state_validation(),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),

        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& pending_req_in_flight_at_after_create_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
    let pre = |s: ClusterState| {
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: ClusterState| {
        &&& pending_req_in_flight_at_after_create_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let input = (Some(resp_msg), Some(vrs.object_ref()));

    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s)
        &&& helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s)
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
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        lifted_vrs_non_interference_property(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();
                let pending_req_msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg;
                lemma_api_request_not_made_by_vrs_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, diff, msg, pending_req_msg
                );
                // Small prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is maintained.
                assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
            },
            Step::ControllerStep(..) => {
                VReplicaSetReconcileState::marshal_preserves_integrity();
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) 
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        VReplicaSetReconcileState::marshal_preserves_integrity();
    }

    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

// Delete lemmas

pub proof fn lemma_from_after_receive_list_pods_resp_to_send_delete_pod_req(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
    resp_msg: Message, diff: int
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
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        vrs.state_validation(),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& pending_req_in_flight_at_after_delete_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
    let pre = |s: ClusterState| {
        &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: ClusterState| {
        &&& pending_req_in_flight_at_after_delete_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let input = (Some(resp_msg), Some(vrs.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s)
        &&& helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s)
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
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        lifted_vrs_non_interference_property(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
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
            Step::ControllerStep(input) => {
                if input.0 == controller_id
                    && input.1 == Some(resp_msg) 
                    && input.2 == Some(vrs.object_ref()) {
                    VReplicaSetReconcileState::marshal_preserves_integrity();

                    let objs = resp_msg.content.get_list_response().res.unwrap();
                    let pods_or_none = objects_to_pods(objs);
                    let pods = pods_or_none.unwrap();
                    let filtered_pods = filter_pods(pods, vrs);
                    helper_lemmas::lemma_filtered_pods_set_equals_matching_pods(
                        s, vrs, cluster, controller_id, resp_msg
                    );

                    let filtered_pods_as_objects = filtered_pods.map_values(|p: PodView| p.marshal());
                    let filtered_pods_as_set = filtered_pods_as_objects.to_set();
                    assert(filtered_pods_as_objects[diff - 1] == filtered_pods[diff - 1].marshal());
                    assert(filtered_pods_as_set.contains(filtered_pods[diff - 1].marshal()));

                    let key = filtered_pods[diff - 1].object_ref();
                    let obj = s.resources()[key];
                }
            },
            _ => {}
        }
    }

    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

pub proof fn lemma_from_after_send_delete_pod_req_to_receive_ok_resp(
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
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),

        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(vrs, controller_id, req_msg, (abs(diff) - 1) as nat)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff - 1)(s)
                    }
                )
            )
        ),
{
    let pre = |s: ClusterState| {
        &&& req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(vrs, controller_id, req_msg, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: ClusterState| {
        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff - 1)(s)
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
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s)
        &&& helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s)
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
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_non_interference_property(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))
    );


    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();
                // Case 1: We're processing the delete request
                if msg == req_msg {
                    let resp_msg = handle_delete_request_msg(req_msg, s.api_server).1;
                    let req = req_msg.content.get_delete_request();
                    let key = req.key;
                  
                    // Asserts properties about the response message
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_delete_response().res.is_Ok()
                    });

                    // Small prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is decreased.
                    a_submap_of_a_finite_map_is_finite(matching_pod_entries(vrs, s.resources()), s.resources());
                    assert(matching_pod_entries(vrs, s.resources()).remove(key) == matching_pod_entries(vrs, s_prime.resources()));
                } else {
                    assert_by(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()), {
                        a_submap_of_a_finite_map_is_finite(matching_pod_entries(vrs, s.resources()), s.resources());
                        lemma_api_request_not_made_by_vrs_maintains_matching_pods(
                            s, s_prime, vrs, cluster, controller_id, diff, msg, Some(req_msg),
                        );
                    });
                }                
            },
            _ => {}
        }
    }

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let resp_msg = handle_delete_request_msg(req_msg, s.api_server).1;
        let req = req_msg.content.get_delete_request();
        let key = req.key;
        
        // Asserts properties about the response message
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_delete_response().res.is_Ok()
        });

        // Small prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is decreased.
        a_submap_of_a_finite_map_is_finite(matching_pod_entries(vrs, s.resources()), s.resources());
        assert(matching_pod_entries(vrs, s.resources()).remove(key) == matching_pod_entries(vrs, s_prime.resources()));
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

pub proof fn lemma_from_after_receive_ok_resp_to_send_delete_pod_req(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
    resp_msg: Message, diff: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        vrs.state_validation(),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id)))),

        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& pending_req_in_flight_at_after_delete_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
    let pre = |s: ClusterState| {
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: ClusterState| {
        &&& pending_req_in_flight_at_after_delete_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let input = (Some(resp_msg), Some(vrs.object_ref()));

    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s)
        &&& helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s)
        &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)(s)
        &&& helper_invariants::at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property(
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
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        lifted_vrs_non_interference_property(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)),
        lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(helper_invariants::at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();
                let pending_req_msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg;
                lemma_api_request_not_made_by_vrs_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, diff, msg, pending_req_msg
                );
                // Small prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is maintained.
                assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id
                    && input.1 == Some(resp_msg) 
                    && input.2 == Some(vrs.object_ref()) {
                    VReplicaSetReconcileState::marshal_preserves_integrity();
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) 
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        VReplicaSetReconcileState::marshal_preserves_integrity();
    }

    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

}
