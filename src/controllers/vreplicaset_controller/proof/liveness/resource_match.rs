// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_invariants, helper_lemmas, liveness::api_actions::*, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*};
use vstd::{assert_seqs_equal, map::*, map_lib::*, math::*, multiset::*, prelude::*};

verus! {

// -------------- Leads-to Chaining Reasoning --------------

pub proof fn lemma_from_diff_and_init_to_current_state_matches(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, diff: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(lift_state(
                |s: ClusterState| {
                    &&& current_state_matches(vrs)(s)
                    &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
                }))
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
        &&& spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())))
        &&& spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref()))))
        &&& spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
        &&& spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>())))
        &&& spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
        &&& spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
        &&& spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref()))))
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id))))

        &&& spec.entails(always(lift_state(Cluster::etcd_is_finite())))
        &&& spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id))))
        &&& spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))))
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
    let list_resp_msg = |resp_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
            &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let post = lift_state(
        |s: ClusterState| {
            &&& current_state_matches(vrs)(s)
            &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
            let req_msg = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
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
        let create_resp_msg = |resp_msg: Message, diff: int| lift_state(
            |s: ClusterState| {
                &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
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
            assert forall |resp_msg: Message|
                #[trigger] spec.entails(create_resp_msg(resp_msg, 0).leads_to(post)) by {
                lemma_from_after_receive_ok_resp_at_after_create_pod_step_to_done(vrs, spec, cluster, controller_id, resp_msg);
            };

            leads_to_exists_intro(spec, |resp_msg: Message| create_resp_msg(resp_msg, 0), post);
            assert_by(
                spec.entails(create_resp(0).leads_to(tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, 0)))),
                {
                    assert forall |ex| #[trigger] create_resp(0).satisfied_by(ex)
                        implies tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, 0)).satisfied_by(ex) by {
                        let s = ex.head();
                        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                        let resp_msg = choose |resp_msg| {
                            &&& #[trigger] s.in_flight().contains(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, msg)
                            &&& resp_msg.content.get_create_response().res is Ok
                        };
                        assert((|resp_msg: Message| create_resp_msg(resp_msg, 0))(resp_msg).satisfied_by(ex));
                    };
                    entails_implies_leads_to(spec, create_resp(0), tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, 0)));
                }
            );

            leads_to_trans_n!(
                spec,
                pre(diff),
                create_resp(diff + 1),
                tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, 0)),
                post
            );
            return;
        }

        // In this branch, we need to convert negative integers to natural numbers for
        // the predicate to fit the rule leads_to_rank_step_one.
        let ranking_pred = |n: nat| create_resp(-n);

        // Useful assertions to let us chain in and out of ranking_pred
        // TODO: triggering on `create_resp(-n)` lets verus panics
        assert forall |n: nat| #![trigger ranking_pred(n)]
                    spec.entails(create_resp(-n).leads_to(ranking_pred(n))) by {
            entails_implies_leads_to(spec, create_resp(-n), ranking_pred(n));
        };

        assert forall |n: nat| #![trigger ranking_pred(n)]
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
        assert forall |resp_msg: Message|
            #[trigger] spec.entails(create_resp_msg(resp_msg, 0).leads_to(post)) by {
            lemma_from_after_receive_ok_resp_at_after_create_pod_step_to_done(vrs, spec, cluster, controller_id, resp_msg);
        };

        leads_to_exists_intro(spec, |resp_msg: Message| create_resp_msg(resp_msg, 0), post);
        assert_by(
            spec.entails(create_resp(0).leads_to(tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, 0)))),
            {
                assert forall |ex| #[trigger] create_resp(0).satisfied_by(ex)
                    implies tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, 0)).satisfied_by(ex) by {
                    let s = ex.head();
                    let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] s.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_create_response().res is Ok
                    };
                    assert((|resp_msg: Message| create_resp_msg(resp_msg, 0))(resp_msg).satisfied_by(ex));
                };
                entails_implies_leads_to(spec, create_resp(0), tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, 0)));
            }
        );

        leads_to_trans_n!(
            spec,
            pre(diff),
            create_resp(diff + 1),
            ranking_pred(-(diff + 1) as nat),
            ranking_pred(0),
            create_resp(0),
            tla_exists(|resp_msg: Message| create_resp_msg(resp_msg, 0)),
            post
        );
    } else if diff > 0 {
        let delete_resp = |diff: int| lift_state(
            |s: ClusterState| {
                &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, abs(diff))(s)
                &&& num_diff_pods_is(vrs, diff)(s)
                &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
            }
        );
        let delete_resp_msg = |resp_msg: Message, diff: int| lift_state(
            |s: ClusterState| {
                &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
                &&& num_diff_pods_is(vrs, diff)(s)
                &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
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
            assert forall |resp_msg: Message|
                #[trigger] spec.entails(delete_resp_msg(resp_msg, 0).leads_to(post)) by {
                lemma_from_after_receive_ok_resp_at_after_delete_pod_step_to_done(vrs, spec, cluster, controller_id, resp_msg);
            };

            leads_to_exists_intro(spec, |resp_msg: Message| delete_resp_msg(resp_msg, 0), post);
            assert_by(
                spec.entails(delete_resp(0).leads_to(tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, 0)))),
                {
                    assert forall |ex| #[trigger] delete_resp(0).satisfied_by(ex)
                        implies tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, 0)).satisfied_by(ex) by {
                        let s = ex.head();
                        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                        let resp_msg = choose |resp_msg| {
                            &&& #[trigger] s.in_flight().contains(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, msg)
                            &&& resp_msg.content.get_get_then_delete_response().res is Ok
                        };
                        assert((|resp_msg: Message| delete_resp_msg(resp_msg, 0))(resp_msg).satisfied_by(ex));
                    };
                    entails_implies_leads_to(spec, delete_resp(0), tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, 0)));
                }
            );

            leads_to_trans_n!(
                spec,
                pre(diff),
                delete_resp(diff - 1),
                tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, 0)),
                post
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
        assert forall |resp_msg: Message|
            #[trigger] spec.entails(delete_resp_msg(resp_msg, 0).leads_to(post)) by {
            lemma_from_after_receive_ok_resp_at_after_delete_pod_step_to_done(vrs, spec, cluster, controller_id, resp_msg);
        };

        leads_to_exists_intro(spec, |resp_msg: Message| delete_resp_msg(resp_msg, 0), post);
        assert_by(
            spec.entails(delete_resp(0).leads_to(tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, 0)))),
            {
                assert forall |ex| #[trigger] delete_resp(0).satisfied_by(ex)
                    implies tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, 0)).satisfied_by(ex) by {
                    let s = ex.head();
                    let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] s.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_get_then_delete_response().res is Ok
                    };
                    assert((|resp_msg: Message| delete_resp_msg(resp_msg, 0))(resp_msg).satisfied_by(ex));
                };
                entails_implies_leads_to(spec, delete_resp(0), tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, 0)));
            }
        );

        leads_to_trans_n!(
            spec,
            pre(diff),
            delete_resp(diff - 1),
            ranking_pred((diff - 1) as nat),
            ranking_pred(0),
            delete_resp(0),
            tla_exists(|resp_msg: Message| delete_resp_msg(resp_msg, 0)),
            post
        );
    } else {
        // diff = 0
        assert forall |resp_msg: Message|
            #[trigger] spec.entails(list_resp_msg(resp_msg, 0).leads_to(post)) by {
            lemma_from_after_receive_list_pods_resp_to_done(vrs, spec, cluster, controller_id, resp_msg);
        };

        leads_to_exists_intro(spec, |resp_msg: Message| list_resp_msg(resp_msg, 0), post);
        assert_by(
            spec.entails(list_resp(0).leads_to(tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, 0)))),
            {
                assert forall |ex| #[trigger] list_resp(0).satisfied_by(ex)
                    implies tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, 0)).satisfied_by(ex) by {
                    let s = ex.head();
                    let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] s.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_list_response().res is Ok
                        &&& {
                            let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                            let resp_obj_keys = resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref());
                            // The matching pods must be a subset of the response.
                            &&& matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                            //&&& resp_objs.no_duplicates()
                            &&& objects_to_pods(resp_objs) is Some
                            &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
                            &&& resp_objs.no_duplicates()
                            &&& resp_obj_keys.no_duplicates()
                            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj) is Ok
                            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace is Some
                            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                        }
                    };
                    assert((|resp_msg: Message| list_resp_msg(resp_msg, 0))(resp_msg).satisfied_by(ex));
                };
                entails_implies_leads_to(spec, list_resp(0), tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, 0)));
            }
        );

        leads_to_trans_n!(
            spec,
            pre(diff),
            list_resp(diff),
            tla_exists(|resp_msg: Message| list_resp_msg(resp_msg, 0)),
            post
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
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
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
                let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_list_response().res is Ok
                    &&& {
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        let resp_obj_keys = resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref());
                        // The matching pods must be a subset of the response.
                        &&& matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                        //&&& resp_objs.no_duplicates()
                        &&& objects_to_pods(resp_objs) is Some
                        &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
                        &&& resp_objs.no_duplicates()
                        &&& resp_obj_keys.no_duplicates()
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj) is Ok
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace is Some
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
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
                let req_msg = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
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
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
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
                let req_msg = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
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
                let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_create_response().res is Ok
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
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
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
                        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
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
            &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
        }
    );
    let delete_req = |diff: int| lift_state(
        |s: ClusterState| {
            &&& pending_req_in_flight_at_after_delete_pod_step(vrs, controller_id, (diff - 1) as nat)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
            &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
        }
    );
    let delete_resp_msg = |resp_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
            &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
        }
    );
    let delete_resp = |diff: int| lift_state(
        |s: ClusterState| {
            &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
            &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
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
                let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_list_response().res is Ok
                    &&& {
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        let resp_obj_keys = resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref());
                        &&& objects_to_pods(resp_objs) is Some
                        &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
                        &&& resp_objs.no_duplicates()
                        &&& resp_obj_keys.no_duplicates()
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj) is Ok
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace is Some
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                        &&& matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
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
                let req_msg = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
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
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, diff as nat)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                    &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, (diff - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff - 1)(s)
                        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
                    }
                )
            )
        ),
{
    let delete_req_msg = |req_msg: Message, diff: int| lift_state(|s: ClusterState| {
        &&& req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(vrs, controller_id, req_msg, (diff - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
    });
    let delete_req = |diff: int| lift_state(
        |s: ClusterState| {
            &&& pending_req_in_flight_at_after_delete_pod_step(vrs, controller_id, (diff - 1) as nat)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
            &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
        }
    );
    let delete_resp_msg = |resp_msg: Message, diff: int| lift_state(
        |s: ClusterState| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
            &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
        }
    );
    let delete_resp = |diff: int| lift_state(
        |s: ClusterState| {
            &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
            &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
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
                let req_msg = ex.head().ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
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
                let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_get_then_delete_response().res is Ok
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
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
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
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, msg
                );
            },
            Step::ControllerStep(input) => {
                VReplicaSetReconcileState::marshal_preserves_integrity();
            },
            _ => {}
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
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
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
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;

                if msg == req_msg {
                    let resp_msg = lemma_list_pods_request_returns_ok_list_resp_containing_matching_pods(
                        s, s_prime, vrs, cluster, controller_id, msg,
                    );
                    // instantiate existential quantifier.
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg_is_ok_list_resp_containing_matching_pods(s_prime, vrs, resp_msg)
                    });
                } else {
                    lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                        s, s_prime, vrs, cluster, controller_id, msg
                    );
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input->0;
        let resp_msg = lemma_list_pods_request_returns_ok_list_resp_containing_matching_pods(
            s, s_prime, vrs, cluster, controller_id, msg,
        );
        // instantiate existential quantifier.
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg_is_ok_list_resp_containing_matching_pods(s_prime, vrs, resp_msg)
        });
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

pub proof fn lemma_from_after_receive_list_pods_resp_to_done(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
    resp_msg: Message
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
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s)
                    &&& num_diff_pods_is(vrs, 0)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& current_state_matches(vrs)(s)
                        &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
                    }
                )
            )
        ),
{
    let pre = |s: ClusterState| {
        &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s)
        &&& num_diff_pods_is(vrs, 0)(s)
    };
    let post = |s: ClusterState| {
        &&& current_state_matches(vrs)(s)
        &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, msg
                );
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id
                    && input.1 == Some(resp_msg)
                    && input.2 == Some(vrs.object_ref()) {
                    VReplicaSetReconcileState::marshal_preserves_integrity();
                    helper_lemmas::lemma_filtered_pods_set_equals_matching_pods(
                        s, vrs, cluster, controller_id, resp_msg
                    );
                    let resources = s_prime.resources();
                }
            },
            _ => {}
        }
    }

    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
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
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
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
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, msg
                );
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
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),

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
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                // Case 1: We're processing the create request
                if msg == req_msg {
                    let resp_msg = lemma_create_matching_pod_request_adds_matching_pod_and_returns_ok(
                        s, s_prime, vrs, cluster, controller_id, msg,
                    );
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_create_response().res is Ok
                    });
                } else {
                    lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                        s, s_prime, vrs, cluster, controller_id, msg
                    );
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input->0;
        let resp_msg = lemma_create_matching_pod_request_adds_matching_pod_and_returns_ok(
            s, s_prime, vrs, cluster, controller_id, msg,
        );
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_create_response().res is Ok
        });
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
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),

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
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, msg
                );
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

pub proof fn lemma_from_after_receive_ok_resp_at_after_create_pod_step_to_done(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
    resp_msg: Message,
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
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, controller_id, resp_msg, 0)(s)
                    &&& num_diff_pods_is(vrs, 0)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& current_state_matches(vrs)(s)
                        &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
                    }
                )
            )
        ),
{
    let pre = |s: ClusterState| {
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, controller_id, resp_msg, 0)(s)
        &&& num_diff_pods_is(vrs, 0)(s)
    };
    let post = |s: ClusterState| {
        &&& current_state_matches(vrs)(s)
        &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, msg
                );
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

// TODO: Investigate flaky proof and weird assertion needed. Higher priority:
// already put in a stopgap fix.
#[verifier(spinoff_prover)]
pub proof fn lemma_from_after_receive_list_pods_resp_to_send_delete_pod_req(
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
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
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
                        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
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
        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
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
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, msg
                );
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
                    let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                    let s_prime_state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                    let new_diff = s_prime_state.reconcile_step->AfterDeletePod_0;
                    helper_lemmas::lemma_filtered_pods_set_equals_matching_pods(
                        s, vrs, cluster, controller_id, resp_msg
                    );

                    let filtered_pods_as_set = filtered_pods.to_set();
                    assert(filtered_pods_as_set.contains(filtered_pods[diff - 1]));
                
                    // Small helper for converting the non-quantified result of lemma_filtered_pods_set_equals_matching_pods
                    // to the quantified quasi-invariant we need.
                    assert forall |i| {
                        &&& pre(s)
                        &&& stronger_next(s, s_prime)
                        &&& 0 <= i < new_diff 
                    } implies {
                        &&& #[trigger] s_prime.resources().contains_key(filtered_pod_keys[i])
                        &&& matching_pods(vrs, s_prime.resources()).contains(s_prime.resources()[filtered_pod_keys[i]])
                        &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]])->Ok_0 == filtered_pods[i]
                    } by {
                        assert(filtered_pods.to_set().contains(filtered_pods[i]));
                    }

                    // Stopgap fix for flaky proof.
                    assert_by(post(s_prime), {
                        assert(forall |i| {
                            &&& 0 <= i < diff
                        } ==> {
                            &&& s_prime.resources().contains_key(filtered_pod_keys[i])
                            &&& matching_pods(vrs, s_prime.resources()).contains(s_prime.resources()[filtered_pod_keys[i]])
                            &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]])->Ok_0 == #[trigger] filtered_pods[i]
                        });
                    });
                }
            },
            _ => {}
        }
    }

    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

// TODO: investigate flaky proof.
#[verifier(spinoff_prover)]
pub proof fn lemma_from_after_send_delete_pod_req_to_receive_ok_resp(
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
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),

        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(vrs, controller_id, req_msg, (abs(diff) - 1) as nat)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                    &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff - 1)(s)
                        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
                    }
                )
            )
        ),
{
    let pre = |s: ClusterState| {
        &&& req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(vrs, controller_id, req_msg, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
    };
    let post = |s: ClusterState| {
        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff - 1)(s)
        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
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
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let s_prime_state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                let filtered_pods = s_prime_state.filtered_pods->0;
                let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                let diff = s_prime_state.reconcile_step->AfterDeletePod_0;

                let msg = input->0;
                // Case 1: We're processing the get-then-delete request
                if msg == req_msg {
                    let resp_msg = lemma_get_then_delete_matching_pod_request_deletes_matching_pod_and_returns_ok(
                        s, s_prime, vrs, cluster, controller_id, msg,
                    );
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_get_then_delete_response().res is Ok
                    });

                    // maintain quantified 'invariant', which doesn't
                    // care about the pod we delete (at diff) anyway.
                    assert forall |i| {
                        &&& pre(s)
                        &&& stronger_next(s, s_prime)
                        &&& 0 <= i < diff 
                    } implies {
                        &&& #[trigger] s_prime.resources().contains_key(filtered_pod_keys[i])
                        &&& matching_pods(vrs, s_prime.resources()).contains(s_prime.resources()[filtered_pod_keys[i]])
                        &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]])->Ok_0 == filtered_pods[i]
                    } by {
                        if s.resources().contains_key(filtered_pod_keys[i]) {}
                    }
                } else {
                    lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                        s, s_prime, vrs, cluster, controller_id, msg
                    );

                    // maintain quantified 'invariant'.
                    assert forall |i| {
                        &&& pre(s)
                        &&& stronger_next(s, s_prime)
                        &&& 0 <= i < diff 
                    } implies {
                        &&& #[trigger] s_prime.resources().contains_key(filtered_pod_keys[i])
                        &&& matching_pods(vrs, s_prime.resources()).contains(s_prime.resources()[filtered_pod_keys[i]])
                        &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]])->Ok_0 == filtered_pods[i]
                    } by {
                        if s.resources().contains_key(filtered_pod_keys[i]) {}
                    }
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let s_prime_state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
        let filtered_pods = s_prime_state.filtered_pods->0;
        let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
        let diff = s_prime_state.reconcile_step->AfterDeletePod_0;

        let msg = input->0;
        let resp_msg = lemma_get_then_delete_matching_pod_request_deletes_matching_pod_and_returns_ok(
            s, s_prime, vrs, cluster, controller_id, msg,
        );
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_then_delete_response().res is Ok
        });

        // maintain quantified 'invariant', which doesn't
        // care about the pod we delete (at diff) anyway.
        assert forall |i| {
            &&& pre(s)
            &&& stronger_next(s, s_prime)
            &&& 0 <= i < diff 
        } implies {
            &&& #[trigger] s_prime.resources().contains_key(filtered_pod_keys[i])
            &&& matching_pods(vrs, s_prime.resources()).contains(s_prime.resources()[filtered_pod_keys[i]])
            &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]])->Ok_0 == filtered_pods[i]
        } by {
            if s.resources().contains_key(filtered_pod_keys[i]) {}
        }
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

// TODO: investigate flaky proof
#[verifier(rlimit(100))]
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
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),

        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                    &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& pending_req_in_flight_at_after_delete_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
                    }
                )
            )
        ),
{
    let pre = |s: ClusterState| {
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, controller_id, resp_msg, abs(diff))(s)
        &&& num_diff_pods_is(vrs, diff)(s)
        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
    };
    let post = |s: ClusterState| {
        &&& pending_req_in_flight_at_after_delete_pod_step(vrs, controller_id, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
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
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let s_prime_state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
        let filtered_pods = s_prime_state.filtered_pods->0;
        let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
        let diff = s_prime_state.reconcile_step->AfterDeletePod_0;

        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, msg
                );
            },
            Step::ControllerStep(..) => {
                VReplicaSetReconcileState::marshal_preserves_integrity();
            },
            _ => {}
        }
        // maintain quantified 'invariant'.
        assert forall |i| {
            &&& pre(s)
            &&& stronger_next(s, s_prime)
            &&& 0 <= i < diff 
        } implies {
            &&& #[trigger] s_prime.resources().contains_key(filtered_pod_keys[i])
            &&& matching_pods(vrs, s_prime.resources()).contains(s_prime.resources()[filtered_pod_keys[i]])
            &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]])->Ok_0 == filtered_pods[i]
        } by {
            if s.resources().contains_key(filtered_pod_keys[i]) {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        let s_prime_state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
        let filtered_pods = s_prime_state.filtered_pods->0;
        let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
        let diff = s_prime_state.reconcile_step->AfterDeletePod_0;

        VReplicaSetReconcileState::marshal_preserves_integrity();
        // maintain quantified 'invariant'.
        assert forall |i| {
            &&& pre(s)
            &&& stronger_next(s, s_prime)
            &&& 0 <= i < diff 
        } implies {
            &&& #[trigger] s_prime.resources().contains_key(filtered_pod_keys[i])
            &&& matching_pods(vrs, s_prime.resources()).contains(s_prime.resources()[filtered_pod_keys[i]])
            &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]])->Ok_0 == filtered_pods[i]
        } by {
            if s.resources().contains_key(filtered_pod_keys[i]) {}
        }
    }


    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

// TODO: investigate flaky proof
#[verifier(spinoff_prover)]
pub proof fn lemma_from_after_receive_ok_resp_at_after_delete_pod_step_to_done(
    vrs: VReplicaSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
    resp_msg: Message,
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
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, controller_id, resp_msg, 0)(s)
                    &&& num_diff_pods_is(vrs, 0)(s)
                    &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
                }
            ).leads_to(
                lift_state(
                    |s: ClusterState| {
                        &&& current_state_matches(vrs)(s)
                        &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
                    }
                )
            )
        ),
{
    let pre = |s: ClusterState| {
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, controller_id, resp_msg, 0)(s)
        &&& num_diff_pods_is(vrs, 0)(s)
        &&& filtered_pods_in_vrs_matching_pods(vrs, controller_id)(s)
    };
    let post = |s: ClusterState| {
        &&& current_state_matches(vrs)(s)
        &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, msg
                );
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

pub proof fn lemma_current_state_matches_is_stable(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, p: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
    requires
        spec.entails(p.leads_to(lift_state(|s: ClusterState| {
            &&& current_state_matches(vrs)(s)
            &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
        }))),
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
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
    ensures
        spec.entails(p.leads_to(always(lift_state(current_state_matches(vrs))))),
{
    let pre_post = |s: ClusterState| {
        &&& current_state_matches(vrs)(s)
        &&& no_pending_req_at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
    };
    let post = inductive_current_state_matches(vrs, controller_id);
    let final_post = current_state_matches(vrs);

    entails_implies_leads_to(spec, lift_state(pre_post), lift_state(post));
    leads_to_trans(spec, p, lift_state(pre_post), lift_state(post));

    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s)
        &&& Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)(s)
        &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)(s_prime)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };

    always_to_always_later(spec, lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)));
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition(
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
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)),
        later(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs))),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );

    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        lemma_inductive_current_state_matches_preserves_from_s_to_s_prime(vrs, cluster, controller_id, s, s_prime);
    }

    leads_to_stable(spec, lift_action(stronger_next), p, lift_state(post));
    leads_to_always_enhance(spec, true_pred(), p, lift_state(post), lift_state(final_post));
}

pub proof fn lemma_inductive_current_state_matches_preserves_from_s_to_s_prime(
    vrs: VReplicaSetView, cluster: Cluster, controller_id: int, s: ClusterState, s_prime: ClusterState
)
requires
    cluster.next()(s, s_prime),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
    Cluster::desired_state_is(vrs)(s),
    Cluster::there_is_the_controller_state(controller_id)(s),
    Cluster::crash_disabled(controller_id)(s),
    Cluster::req_drop_disabled()(s),
    Cluster::pod_monkey_disabled()(s),
    Cluster::every_in_flight_msg_has_unique_id()(s),
    Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s),
    Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s),
    Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
    Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s),
    Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)(s),
    Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s),
    cluster.each_builtin_object_in_etcd_is_well_formed()(s),
    cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
    cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
    Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)(s),
    Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)(s_prime),
    Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s),
    forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
        ==> #[trigger] vrs_rely(other_id)(s),
    Cluster::etcd_is_finite()(s),
    helper_invariants::vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s),
    helper_invariants::no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s),
    inductive_current_state_matches(vrs, controller_id)(s),
ensures
    inductive_current_state_matches(vrs, controller_id)(s_prime),
{
    VReplicaSetView::marshal_preserves_integrity();
    PodView::marshal_preserves_integrity();
    VReplicaSetReconcileState::marshal_preserves_integrity();
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            let new_msgs = s_prime.in_flight().sub(s.in_flight());
            if s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) {
                if !Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg) {
                    lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                        s, s_prime, vrs, cluster, controller_id, msg,
                    );

                    // Maintain quantified invariant.
                    if at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterListPods)(s) {
                        let req_msg = s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                        
                        assert forall |msg| {
                            &&& inductive_current_state_matches(vrs, controller_id)(s)
                            &&& #[trigger] s_prime.in_flight().contains(msg)
                            &&& msg.src is APIServer
                            &&& resp_msg_matches_req_msg(msg, req_msg)
                        } implies resp_msg_is_ok_list_resp_containing_matching_pods(s_prime, vrs, msg) by {
                            assert(forall |msg| #[trigger] new_msgs.contains(msg) ==> !(#[trigger] resp_msg_matches_req_msg(msg, req_msg)));
                            if !new_msgs.contains(msg) {
                                assert(s.in_flight().contains(msg));
                            }
                        }
                    }
                } else {
                    if at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterListPods)(s) {
                        let req_msg = s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                        
                        assert forall |msg| {
                            &&& inductive_current_state_matches(vrs, controller_id)(s)
                            &&& #[trigger] s_prime.in_flight().contains(msg)
                            &&& msg.src is APIServer
                            &&& resp_msg_matches_req_msg(msg, req_msg)
                        } implies resp_msg_is_ok_list_resp_containing_matching_pods(s_prime, vrs, msg) by {
                            if !new_msgs.contains(msg) {
                                assert(s.in_flight().contains(msg));
                            } else {
                                lemma_list_pods_request_returns_ok_list_resp_containing_matching_pods(
                                    s, s_prime, vrs, cluster, controller_id, req_msg,
                                );
                            }
                        }
                    }
                }
            } else {
                lemma_api_request_other_than_pending_req_msg_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, msg,
                );
            }
        },
        Step::ControllerStep(input) => {
            if s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) {
                if input.0 == controller_id && input.2 == Some(vrs.object_ref()) {
                    if at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterListPods)(s) {
                        let resp_msg = input.1->0;
                        assert(resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s)) by {
                            let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                            assert(s.in_flight().contains(resp_msg));
                            assert(resp_msg_matches_req_msg(resp_msg, msg));
                            assert(resp_msg_is_ok_list_resp_containing_matching_pods(s, vrs, resp_msg));
                        }
                        helper_lemmas::lemma_filtered_pods_set_equals_matching_pods(s, vrs, cluster, controller_id, resp_msg);
                    } else if at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init)(s) {
                        // prove that the newly sent message has no response.
                        if s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg is Some {
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                            assert(s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg is None);
                            assert(forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id);
                            assert(s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg)) by {
                                assert(s_prime.in_flight().contains(req_msg));
                                assert(!s.in_flight().contains(req_msg));
                            }
                            assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
                                && (forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id)
                                && s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg)
                                && msg != req_msg
                                implies msg.rpc_id != req_msg.rpc_id by {
                                if !s.in_flight().contains(msg) {} // need this to invoke trigger.
                            }
                        }
                    } else {
                        assert(inductive_current_state_matches(vrs, controller_id)(s_prime));
                    }
                } else {
                    assert(inductive_current_state_matches(vrs, controller_id)(s_prime));
                }
            } else {
                assert(inductive_current_state_matches(vrs, controller_id)(s_prime));
            }
        },
        _ => {
            let new_msgs = s_prime.in_flight().sub(s.in_flight());

            // Maintain quantified invariant.
            if at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterListPods)(s) {
                let req_msg = s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                
                assert forall |msg| {
                    &&& inductive_current_state_matches(vrs, controller_id)(s)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.src is APIServer
                    &&& resp_msg_matches_req_msg(msg, req_msg)
                } implies resp_msg_is_ok_list_resp_containing_matching_pods(s_prime, vrs, msg) by {
                    assert(forall |msg| #[trigger] new_msgs.contains(msg) ==> !(#[trigger] msg.src is APIServer));
                    if !new_msgs.contains(msg) {
                        assert(s.in_flight().contains(msg));
                    }
                }
            }
        }
    }
}
}
