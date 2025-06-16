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
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_invariants, helper_lemmas, liveness::api_actions::*, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*};
use vstd::{map::*, map_lib::*, math::*, multiset::*, prelude::*};

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
                    &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
            &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
                        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                        let resp_msg = choose |resp_msg| {
                            &&& #[trigger] s.in_flight().contains(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, msg)
                            &&& resp_msg.content.get_create_response().res.is_Ok()
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
                    let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] s.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_create_response().res.is_Ok()
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
                        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                        let resp_msg = choose |resp_msg| {
                            &&& #[trigger] s.in_flight().contains(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, msg)
                            &&& resp_msg.content.get_get_then_delete_response().res.is_Ok()
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
                    let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] s.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_get_then_delete_response().res.is_Ok()
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
                    let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] s.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_list_response().res.is_Ok()
                        &&& {
                            let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                            let resp_obj_keys = resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref());
                            // The matching pods must be a subset of the response.
                            &&& matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                            //&&& resp_objs.no_duplicates()
                            &&& objects_to_pods(resp_objs).is_Some()
                            &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
                            &&& resp_objs.no_duplicates()
                            &&& resp_obj_keys.no_duplicates()
                            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).is_Ok()
                            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
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
                let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_list_response().res.is_Ok()
                    &&& {
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        let resp_obj_keys = resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref());
                        // The matching pods must be a subset of the response.
                        &&& matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                        //&&& resp_objs.no_duplicates()
                        &&& objects_to_pods(resp_objs).is_Some()
                        &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
                        &&& resp_objs.no_duplicates()
                        &&& resp_obj_keys.no_duplicates()
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).is_Ok()
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
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
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
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
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
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
                let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_list_response().res.is_Ok()
                    &&& {
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        let resp_obj_keys = resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref());
                        &&& objects_to_pods(resp_objs).is_Some()
                        &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
                        &&& resp_objs.no_duplicates()
                        &&& resp_obj_keys.no_duplicates()
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).is_Ok()
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
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
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
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
                    &&& resp_msg.content.get_get_then_delete_response().res.is_Ok()
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
                let msg = input.get_Some_0();
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
                let msg = input.get_Some_0();

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
        let msg = input.get_Some_0();
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
                        &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
        &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
                let msg = input.get_Some_0();
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
                let msg = input.get_Some_0();
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
                let msg = input.get_Some_0();
                // Case 1: We're processing the create request
                if msg == req_msg {
                    let resp_msg = lemma_create_matching_pod_request_adds_matching_pod_and_returns_ok(
                        s, s_prime, vrs, cluster, controller_id, msg,
                    );
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_create_response().res.is_Ok()
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
        let msg = input.get_Some_0();
        let resp_msg = lemma_create_matching_pod_request_adds_matching_pod_and_returns_ok(
            s, s_prime, vrs, cluster, controller_id, msg,
        );
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_create_response().res.is_Ok()
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
                let msg = input.get_Some_0();
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
                        &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
        &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
                let msg = input.get_Some_0();
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

// TODO: Investigate flaky proof and weird assertion needed.
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
                let msg = input.get_Some_0();
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
                    let new_diff = s_prime_state.reconcile_step.get_AfterDeletePod_0();
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
                        &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                    } by {
                        assert(filtered_pods.to_set().contains(filtered_pods[i]));
                    }

                    // No idea why this assert is needed, but proof is brittle
                    // without it.
                    assert({
                        let s = s_prime;
                        let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                        let filtered_pods = state.filtered_pods.unwrap();
                        let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                        let diff = state.reconcile_step.get_AfterDeletePod_0();
                        &&& s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
                        &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
                        &&& state.reconcile_step.is_AfterDeletePod()
                        &&& state.filtered_pods.is_Some()
                        &&& filtered_pod_keys.no_duplicates()
                        &&& diff < filtered_pods.len()
                        &&& forall |i| #![trigger state.filtered_pods.unwrap()[i]] 0 <= i < diff ==> {
                            &&& s.resources().contains_key(filtered_pod_keys[i])
                            &&& matching_pods(vrs, s.resources()).contains(s.resources()[filtered_pod_keys[i]])
                            &&& PodView::unmarshal(s.resources()[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                        }
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
                let filtered_pods = s_prime_state.filtered_pods.get_Some_0();
                let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                let diff = s_prime_state.reconcile_step.get_AfterDeletePod_0();

                let msg = input.get_Some_0();
                // Case 1: We're processing the get-then-delete request
                if msg == req_msg {
                    let resp_msg = lemma_get_then_delete_matching_pod_request_deletes_matching_pod_and_returns_ok(
                        s, s_prime, vrs, cluster, controller_id, msg,
                    );
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, msg)
                        &&& resp_msg.content.get_get_then_delete_response().res.is_Ok()
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
                        &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
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
                        &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
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
        let filtered_pods = s_prime_state.filtered_pods.get_Some_0();
        let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
        let diff = s_prime_state.reconcile_step.get_AfterDeletePod_0();

        let msg = input.get_Some_0();
        let resp_msg = lemma_get_then_delete_matching_pod_request_deletes_matching_pod_and_returns_ok(
            s, s_prime, vrs, cluster, controller_id, msg,
        );
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_then_delete_response().res.is_Ok()
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
            &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
        } by {
            if s.resources().contains_key(filtered_pod_keys[i]) {}
        }
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
        let filtered_pods = s_prime_state.filtered_pods.get_Some_0();
        let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
        let diff = s_prime_state.reconcile_step.get_AfterDeletePod_0();

        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();
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
            &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
        } by {
            if s.resources().contains_key(filtered_pod_keys[i]) {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        let s_prime_state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
        let filtered_pods = s_prime_state.filtered_pods.get_Some_0();
        let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
        let diff = s_prime_state.reconcile_step.get_AfterDeletePod_0();

        VReplicaSetReconcileState::marshal_preserves_integrity();
        // maintain quantified 'invariant'.
        assert forall |i| {
            &&& pre(s)
            &&& stronger_next(s, s_prime)
            &&& 0 <= i < diff 
        } implies {
            &&& #[trigger] s_prime.resources().contains_key(filtered_pod_keys[i])
            &&& matching_pods(vrs, s_prime.resources()).contains(s_prime.resources()[filtered_pod_keys[i]])
            &&& PodView::unmarshal(s_prime.resources()[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
        } by {
            if s.resources().contains_key(filtered_pod_keys[i]) {}
        }
    }


    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

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
                        &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
        &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
                let msg = input.get_Some_0();
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

//#[verifier(spinoff_prover)]
// TODO: broken by changed ESR spec, needs new set-based (rather than map-based) argument.
#[verifier(external_body)]
pub proof fn lemma_current_state_matches_is_stable(
    spec: TempPred<ClusterState>,
    vrs: VReplicaSetView,
    p: TempPred<ClusterState>,
    cluster: Cluster,
    controller_id: int
)
    requires
        spec.entails(p.leads_to(lift_state(|s: ClusterState| {
            &&& current_state_matches(vrs)(s)
            &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
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
        spec.entails(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_interfering_update_request()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_interfering_update_status_request()))),
        spec.entails(always(lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
        spec.entails(always(lift_state(helper_invariants::at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id)))),
    ensures
        spec.entails(p.leads_to(always(lift_state(current_state_matches(vrs))))),
{
    let pre_post = |s: ClusterState| {
        &&& current_state_matches(vrs)(s)
        &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
    };
    let post = |s: ClusterState| {
        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).unwrap();
        &&& current_state_matches(vrs)(s)
        &&& {
            &&& s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
            &&& triggering_cr.spec() == vrs.spec()
            &&& triggering_cr.metadata().uid == vrs.metadata().uid
        } ==> {
            &&& {
                ||| at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init)(s)
                ||| at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterListPods)(s)
                ||| at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
                ||| at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Error)(s)
            }
            &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterListPods)(s) ==> {
                let req_msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                &&& s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.is_Some()
                &&& req_msg.dst.is_APIServer()
                &&& req_msg.content.is_list_request()
                &&& req_msg.content.get_list_request() == ListRequest {
                    kind: PodView::kind(),
                    namespace: vrs.metadata.namespace.unwrap(),
                }
                &&& forall |msg| {
                    let req_msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                    &&& #[trigger] s.in_flight().contains(msg)
                    &&& s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.is_Some()
                    &&& msg.src.is_APIServer()
                    &&& resp_msg_matches_req_msg(msg, req_msg)
                } ==> {
                    let resp_objs = msg.content.get_list_response().res.unwrap();
                    let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                    &&& msg.content.is_list_response()
                    &&& msg.content.get_list_response().res.is_Ok()
                    &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0
                    &&& resp_obj_keys.no_duplicates()
                    &&& matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                }
            }
        }
    };
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
        &&& Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)(s)
        &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& helper_invariants::no_pending_interfering_update_request()(s)
        &&& helper_invariants::no_pending_interfering_update_status_request()(s)
        &&& helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s)
        &&& helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s)
        &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)(s)
        &&& helper_invariants::at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id)(s)
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
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        lifted_vrs_rely_condition(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(helper_invariants::every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(helper_invariants::no_pending_interfering_update_request()),
        lift_state(helper_invariants::no_pending_interfering_update_status_request()),
        lift_state(helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(helper_invariants::no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)),
        lift_state(helper_invariants::every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(helper_invariants::at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id))
    );

    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        assume(false);
        VReplicaSetView::marshal_preserves_integrity();
        VReplicaSetReconcileState::marshal_preserves_integrity();
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input.get_Some_0();
                lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
                    s, s_prime, vrs, cluster, controller_id, msg
                );
                // Small prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is maintained.
                assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
                let old_pods: Set<ObjectRef> = Set::new(|key: ObjectRef| {
                    &&& s.resources().contains_key(key)
                    &&& owned_selector_match_is(vrs, s.resources()[key])
                });
                let new_pods: Set<ObjectRef> = Set::new(|key: ObjectRef| {
                    &&& s_prime.resources().contains_key(key)
                    &&& owned_selector_match_is(vrs, s_prime.resources()[key])
                });
                assert forall |key: ObjectRef| matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources())
                    implies old_pods.contains(key) ==> #[trigger] new_pods.contains(key) by {
                    if (old_pods.contains(key)) {
                        assert(owned_selector_match_is(vrs, s.resources()[key]));
                        assert(matching_pod_entries(vrs, s.resources()).contains_key(key));
                    }
                };
                assert forall |key: ObjectRef| matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources())
                    implies new_pods.contains(key) ==> #[trigger] old_pods.contains(key) by {
                    if (new_pods.contains(key)) {
                        assert(owned_selector_match_is(vrs, s_prime.resources()[key]));
                        assert(matching_pod_entries(vrs, s_prime.resources()).contains_key(key));
                    }
                };
                assert(old_pods =~= new_pods);

                let current_req_msg = input.unwrap();
                let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                let new_msgs = s_prime.in_flight().sub(s.in_flight());
                if at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterListPods)(s) {
                    let req_msg = s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                    let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).unwrap();
                    assert forall |msg| {
                        let req_msg = s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                        &&& #[trigger] s_prime.in_flight().contains(msg)
                        &&& s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.is_Some()
                        &&& msg.src.is_APIServer()
                        &&& post(s)
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                        &&& stronger_next(s, s_prime)
                    } implies {
                        let resp_objs = msg.content.get_list_response().res.unwrap();
                        let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                        &&& msg.content.is_list_response()
                        &&& msg.content.get_list_response().res.is_Ok()
                        &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0
                        &&& resp_obj_keys.no_duplicates()
                        &&& matching_pod_entries(vrs, s_prime.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                    } by {
                        if (new_msgs.contains(msg)) {
                            if current_req_msg == req_msg {
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());

                                assert forall |o: DynamicObjectView| #![auto]
                                stronger_next(s, s_prime)
                                && resp_objs.contains(o)
                                implies !PodView::unmarshal(o).is_err()
                                        && o.metadata.namespace == vrs.metadata.namespace by {
                                    // Tricky reasoning about .to_seq
                                    let selector = |o: DynamicObjectView| {
                                        &&& o.object_ref().namespace == req_msg.content.get_list_request().namespace
                                        &&& o.object_ref().kind == req_msg.content.get_list_request().kind
                                    };
                                    let selected_elements = s.resources().values().filter(selector);
                                    lemma_values_finite(s.resources());
                                    finite_set_to_seq_contains_all_set_elements(selected_elements);
                                    assert(resp_objs =~= selected_elements.to_seq());
                                    assert(selected_elements.contains(o));
                                }
                                seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                    resp_objs,
                                    |o: DynamicObjectView| PodView::unmarshal(o).is_err()
                                );

                                assert_by(resp_obj_keys.no_duplicates(), {
                                    let selector = |o: DynamicObjectView| {
                                        &&& o.object_ref().namespace == req_msg.content.get_list_request().namespace
                                        &&& o.object_ref().kind == req_msg.content.get_list_request().kind
                                    };
                                    let selected_elements = s.resources().values().filter(selector);
                                    lemma_values_finite(s.resources());
                                    finite_set_to_seq_has_no_duplicates(selected_elements);
                                    let selected_elements_seq = selected_elements.to_seq();
                                    assert(selected_elements_seq.no_duplicates());
                                    assert forall |o1: DynamicObjectView, o2: DynamicObjectView| #![auto]
                                        o1 != o2
                                        && selected_elements_seq.contains(o1)
                                        && selected_elements_seq.contains(o2)
                                        && stronger_next(s, s_prime)
                                        implies o1.object_ref() != o2.object_ref() by {
                                        finite_set_to_seq_contains_all_set_elements(selected_elements);
                                        assert(selected_elements.contains(o1));
                                        assert(selected_elements.contains(o2));
                                        assert(s.resources().values().contains(o1));
                                        assert(s.resources().values().contains(o2));
                                        assert(o1.object_ref() != o2.object_ref());
                                    }
                                    let selected_element_keys = selected_elements_seq.map_values(|o: DynamicObjectView| o.object_ref());
                                    assert(selected_element_keys.no_duplicates());
                                    assert(resp_obj_keys =~= selected_element_keys);
                                });

                                assert(matching_pod_entries(vrs, s.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set() && resp_objs.no_duplicates()) by {
                                    // reveal API server spec
                                    let selector = |o: DynamicObjectView| {
                                        &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
                                        &&& o.object_ref().kind == PodView::kind()
                                    };
                                    assert(resp_objs == s.resources().values().filter(selector).to_seq());
                                    // consistency of no_duplicates
                                    lemma_values_finite(s.resources());
                                    finite_set_to_finite_filtered_set(s.resources().values(), selector);
                                    finite_set_to_seq_has_no_duplicates(s.resources().values().filter(selector));
                                    assert(resp_objs.no_duplicates());
                                    // reveal matching_pod_entries logic
                                    let matched_entries = matching_pod_entries(vrs, s.resources());
                                    assert(matched_entries.values() =~= s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj))) by {
                                        assert forall |obj| s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj) implies matched_entries.values().contains(obj) by {
                                            assert(owned_selector_match_is(vrs, obj));
                                            assert(s.resources().contains_key(obj.object_ref()) && s.resources()[obj.object_ref()] == obj);
                                            assert(matched_entries.contains_key(obj.object_ref()) && matched_entries[obj.object_ref()] == obj);
                                        }
                                        assert forall |obj| matched_entries.values().contains(obj) implies s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj) by {
                                            assert(s.resources().contains_key(obj.object_ref()));
                                            assert(owned_selector_match_is(vrs, obj));
                                        }
                                        // optional if antisymmetry_of_set_equality is imported
                                        assert(forall |obj| matched_entries.values().contains(obj) == s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj));
                                    }
                                    assert(s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj) && selector(obj)) == matching_pod_entries(vrs, s.resources()).values());
                                    // merge 2 selectors
                                    assert((|obj| owned_selector_match_is(vrs, obj) && selector(obj)) =~= (|obj| owned_selector_match_is(vrs, obj)));
                                    // get rid of DS conversion, basically babysitting Verus
                                    assert(resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set() =~= s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj))) by {
                                        assert(resp_objs == s.resources().values().filter(selector).to_seq());
                                        assert((|obj : DynamicObjectView| owned_selector_match_is(vrs, obj) && selector(obj)) =~= (|obj : DynamicObjectView| owned_selector_match_is(vrs, obj)));
                                        seq_filter_preserves_no_duplicates(resp_objs, |obj| owned_selector_match_is(vrs, obj));
                                        seq_filter_is_a_subset_of_original_seq(resp_objs, |obj| owned_selector_match_is(vrs, obj));
                                        finite_set_to_seq_contains_all_set_elements(s.resources().values().filter(selector));
                                        finite_set_to_seq_contains_all_set_elements(s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)));
                                        // Fix to get rid of flaky proof.
                                        assert forall |obj| #![trigger owned_selector_match_is(vrs, obj)]
                                            resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set().contains(obj)
                                            implies
                                            s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj) by {
                                            assert(resp_objs.contains(obj));
                                            assert(s.resources().values().filter(selector).to_seq().contains(obj));
                                            assert(s.resources().values().filter(selector).contains(obj));
                                            assert(s.resources().values().contains(obj));
                                            assert(owned_selector_match_is(vrs, obj));
                                            assert(s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj));
                                        }
                                        assert forall |obj| #![trigger owned_selector_match_is(vrs, obj)]
                                            s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj)
                                            implies
                                            resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set().contains(obj) by {
                                            assert(s.resources().values().contains(obj));
                                            assert(selector(obj));
                                            assert(s.resources().values().filter(selector).contains(obj));
                                            assert(s.resources().values().filter(selector).to_seq().contains(obj));
                                            assert(resp_objs.contains(obj));
                                            assert(resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj));
                                            assert(resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set().contains(obj));
                                        }
                                    }
                                }

                                assert({
                                    let resp_objs = msg.content.get_list_response().res.unwrap();
                                    let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                                    &&& msg.content.is_list_response()
                                    &&& msg.content.get_list_response().res.is_Ok()
                                    &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0
                                    &&& resp_obj_keys.no_duplicates()
                                    &&& matching_pod_entries(vrs, s_prime.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                                });
                            } else {
                                assert(s.in_flight().contains(current_req_msg));
                                assert(current_req_msg.rpc_id != req_msg.rpc_id);
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                assert_by(
                                    matching_pod_entries(vrs, s_prime.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set(),
                                    {
                                        assert({
                                            &&& forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(diff))(s))
                                            &&& forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s))
                                        });
                                        assert(forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                                                ==> #[trigger] vrs_rely(other_id)(s));
                                        lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
                                            s, s_prime, vrs, cluster, controller_id, current_req_msg
                                        );
                                    }
                                );
                            }
                        } else {
                            let msg_antecedent = {
                                &&& s.in_flight().contains(msg)
                                &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                                &&& msg.src.is_APIServer()
                                &&& resp_msg_matches_req_msg(msg, req_msg)
                            };
                            let inv_pre = |msg: Message| {
                                let content = msg.content;
                                let req = content.get_delete_request();
                                let key = content.get_delete_request().key;
                                let obj = s.resources()[key];
                                &&& s.in_flight().contains(msg)
                                &&& msg.src.is_Controller()
                                &&& msg.src.get_Controller_0() == controller_id
                                &&& msg.dst.is_APIServer()
                                &&& msg.content.is_APIRequest()
                                &&& content.is_delete_request()
                                &&& s.resources().contains_key(key)
                                &&& owned_selector_match_is(vrs, obj)
                                // NOTE: We require that the resource version in etcd is
                                // equal to the one carried by the delete request to
                                // exclude the case where another reconcile working on another
                                // vrs object tries to delete the same object.
                                &&& req.preconditions.is_Some()
                                &&& req.preconditions.unwrap().resource_version.is_Some()
                                &&& req.preconditions.unwrap().uid.is_None()
                                &&& obj.metadata.resource_version.is_Some()
                                &&& obj.metadata.resource_version.unwrap() ==
                                        req.preconditions.unwrap().resource_version.unwrap()
                            };

                            if inv_pre(current_req_msg) {
                                assert(forall |diff: nat| ! #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s));
                                assert(false);
                            } else if (current_req_msg.content.is_delete_request()) {
                                let current_req = current_req_msg.content.get_delete_request();
                                if !(current_req_msg.src.is_Controller() || current_req_msg.src.is_BuiltinController()) {
                                    assert({
                                        &&& s.in_flight().contains(current_req_msg)
                                        &&& !(current_req_msg.src.is_Controller() || current_req_msg.src.is_BuiltinController())
                                        &&& current_req_msg.dst.is_APIServer()
                                        &&& current_req_msg.content.is_APIRequest()
                                    } ==>{
                                        &&& current_req_msg.content.is_create_request() ==> current_req_msg.content.get_create_request().key().kind != PodView::kind()
                                        &&& current_req_msg.content.is_delete_request() ==> current_req_msg.content.get_delete_request().key.kind != PodView::kind()
                                    });
                                } else if current_req_msg.src.is_Controller() && current_req_msg.src.get_Controller_0() != controller_id {
                                    assert(vrs_rely(current_req_msg.src.get_Controller_0())(s));
                                }
                            }

                            if msg_antecedent {
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());

                                assert_by(
                                    matching_pod_entries(vrs, s_prime.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set(),
                                    {
                                        assert({
                                            &&& forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(diff))(s))
                                            &&& forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s))
                                        });
                                        assert(forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                                                ==> #[trigger] vrs_rely(other_id)(s));
                                        lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
                                            s, s_prime, vrs, cluster, controller_id, current_req_msg
                                        );
                                    }
                                );
                                assert({
                                    let resp_objs = msg.content.get_list_response().res.unwrap();
                                    let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                                    &&& msg.content.is_list_response()
                                    &&& msg.content.get_list_response().res.is_Ok()
                                    &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0
                                    &&& resp_obj_keys.no_duplicates()
                                    //&&& matching_pod_entries(vrs, s_prime.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                                });
                            }
                        }
                    }
                }
            },
            Step::ControllerStep(input) => {
                let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).unwrap();
                if s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
                    && triggering_cr.spec() == vrs.spec()
                    && triggering_cr.metadata().uid == vrs.metadata().uid
                    && input.0 == controller_id
                    && input.2 == Some(vrs.object_ref()) {
                    let resp_msg = input.1.get_Some_0();
                    if at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterListPods)(s) {
                        let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                        let cr_msg = step.get_ControllerStep_0().1.get_Some_0();
                        let req_msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                        let new_req_msg = s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                        let objs = cr_msg.content.get_list_response().res.unwrap();
                        let obj_keys = objs.map_values(|o: DynamicObjectView| o.object_ref());
                        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).unwrap();
                        let pods_or_none = objects_to_pods(objs);
                        let pods = pods_or_none.unwrap();
                        let filtered_pods = filter_pods(pods, triggering_cr);
                        let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());

                        // Phase 1: correlate matching_pod_entries(vrs, s.resources()).values() with vrs.spec.replicas
                        let matching_pods: Set<ObjectRef> = Set::new(|key: ObjectRef| {
                            &&& s.resources().contains_key(key)
                            &&& owned_selector_match_is(vrs, s.resources()[key])
                        });
                        assert(matching_pods.len() == vrs.spec.replicas.unwrap_or(0));
                        assert(matching_pods =~= matching_pod_entries(vrs, s.resources()).dom());
                        assert(matching_pod_entries(vrs, s.resources()).is_injective());
                        a_submap_of_a_finite_map_is_finite(
                            matching_pod_entries(vrs, s.resources()),
                            s.resources()
                        );
                        injective_finite_map_implies_dom_len_is_equal_to_values_len(
                            matching_pod_entries(vrs, s.resources())
                        );
                        assert(matching_pod_entries(vrs, s.resources()).values().len() == vrs.spec.replicas.unwrap_or(0));

                        // Phase 2: correlate matching_pod_entries(vrs, s.resources()).values() with filtered_pods
                        assert(matching_pod_entries(vrs, s.resources()).values() == objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set());
                        assert_by(objs.no_duplicates(), {
                            assert forall |i: int, j: int| #![auto]
                                0 <= i < objs.len()
                                && 0 <= j < objs.len()
                                && i != j
                                && post(s)
                                && stronger_next(s, s_prime)
                                && obj_keys.no_duplicates()
                                implies objs[i] != objs[j] by {
                                assert(objs[i].object_ref() == obj_keys[i]);
                                assert(objs[j].object_ref() == obj_keys[j]);
                            }
                        });
                        assert_by(pods.no_duplicates(), {
                            assert forall |i: int, j: int| #![auto]
                                0 <= i < pods.len()
                                && 0 <= j < pods.len()
                                && i != j
                                && post(s)
                                && stronger_next(s, s_prime)
                                && obj_keys.no_duplicates()
                                implies pods[i] != pods[j] by {
                                assert(pods == objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()));
                                assert(pods.len() == objs.len());
                                seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                    objs,
                                    |obj: DynamicObjectView| PodView::unmarshal(obj).is_err()
                                );
                                assert(objs.contains(objs[i]));
                                assert(objs.contains(objs[j]));
                                assert(PodView::unmarshal(objs[i]).is_Ok());
                                assert(PodView::unmarshal(objs[j]).is_Ok());

                                assert(pods[i] == PodView::unmarshal(objs[i]).get_Ok_0());
                                assert(pods[j] == PodView::unmarshal(objs[j]).get_Ok_0());

                                assert(pods[i].object_ref() == objs[i].object_ref());
                                assert(pods[j].object_ref() == objs[j].object_ref());

                                assert(objs[i].object_ref() == obj_keys[i]);
                                assert(objs[j].object_ref() == obj_keys[j]);
                            }
                        });
                        seq_filter_preserves_no_duplicates(
                            objs,
                            |obj| owned_selector_match_is(vrs, obj)
                        );
                        objs.filter(|obj| owned_selector_match_is(vrs, obj)).unique_seq_to_set();
                        assert(objs.filter(|obj| owned_selector_match_is(vrs, obj)).len() == vrs.spec.replicas.unwrap_or(0));
                        assert(
                            objs.filter(|obj| owned_selector_match_is(vrs, obj))
                                .map_values(|obj: DynamicObjectView| PodView::unmarshal(obj).unwrap()).len()
                                == vrs.spec.replicas.unwrap_or(0)
                        );
                        assert_by(
                            objs.filter(|obj| owned_selector_match_is(vrs, obj))
                                .map_values(|obj: DynamicObjectView| PodView::unmarshal(obj).unwrap()).no_duplicates(),
                            {
                                let osm_pred = |obj: DynamicObjectView| owned_selector_match_is(vrs, obj);
                                let obj_to_pod = |obj: DynamicObjectView| PodView::unmarshal(obj).unwrap();
                                assert forall |i: int, j: int| #![auto]
                                    0 <= i < objs.filter(osm_pred).map_values(obj_to_pod).len()
                                    && 0 <= j < objs.filter(osm_pred).map_values(obj_to_pod).len()
                                    && i != j
                                    && post(s)
                                    && stronger_next(s, s_prime)
                                    && obj_keys.no_duplicates()
                                    implies objs.filter(osm_pred).map_values(obj_to_pod)[i]
                                        != objs.filter(osm_pred).map_values(obj_to_pod)[j] by {
                                    let pod_i = objs.filter(osm_pred).map_values(obj_to_pod)[i];
                                    let pod_j = objs.filter(osm_pred).map_values(obj_to_pod)[j];

                                    seq_filter_contains_implies_seq_contains(
                                        objs,
                                        osm_pred,
                                        objs.filter(osm_pred)[i]
                                    );
                                    seq_filter_contains_implies_seq_contains(
                                        objs,
                                        osm_pred,
                                        objs.filter(osm_pred)[j]
                                    );

                                    seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err());
                                    assert(objs.contains(objs.filter(osm_pred)[i]));
                                    assert(objs.contains(objs.filter(osm_pred)[j]));
                                    assert(PodView::unmarshal(objs.filter(osm_pred)[i]).unwrap() == pod_i);
                                    assert(PodView::unmarshal(objs.filter(osm_pred)[j]).unwrap() == pod_j);
                                    assert(objs.filter(osm_pred)[i].object_ref() == pod_i.object_ref());
                                    assert(objs.filter(osm_pred)[j].object_ref() == pod_j.object_ref());

                                    let idxi = choose |idx| 0 <= idx < objs.len() && objs[idx] == objs.filter(osm_pred)[i];
                                    let idxj = choose |idx| 0 <= idx < objs.len() && objs[idx] == objs.filter(osm_pred)[j];

                                    if idxi == idxj {
                                        seq_filter_preserves_no_duplicates(
                                            objs,
                                            osm_pred
                                        );
                                    } else {
                                        assert(objs[idxi].object_ref() == obj_keys[idxi]);
                                        assert(objs[idxj].object_ref() == obj_keys[idxj]);
                                        assert(objs[idxi].object_ref() != objs[idxj].object_ref());
                                    }
                                }
                            }
                        );
                        objs.filter(|obj| owned_selector_match_is(vrs, obj))
                            .map_values(|obj: DynamicObjectView| PodView::unmarshal(obj).unwrap()).unique_seq_to_set();
                        assert_by(
                            filtered_pods.to_set()
                                =~= objs.filter(|obj| owned_selector_match_is(vrs, obj))
                                    .map_values(|obj: DynamicObjectView| PodView::unmarshal(obj).unwrap()).to_set(),
                            {
                                let osm_pred = |obj: DynamicObjectView| owned_selector_match_is(vrs, obj);
                                let obj_to_pod = |obj: DynamicObjectView| PodView::unmarshal(obj).unwrap();
                                assert forall |p: PodView| #![auto]
                                    post(s)
                                    && stronger_next(s, s_prime)
                                    && filtered_pods.to_set().contains(p)
                                    implies objs.filter(osm_pred).map_values(obj_to_pod).to_set().contains(p) by {
                                    let i = choose |i: int| 0 <= i < filtered_pods.len() && filtered_pods[i] == p;
                                    assert(filtered_pods[i] == p);
                                    let pod = filtered_pods[i];
                                    let pod_pred = |pod: PodView|
                                        pod.metadata.owner_references_contains(vrs.controller_owner_ref())
                                        && vrs.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                        && pod.metadata.deletion_timestamp.is_None();
                                    assert(pod_pred(pod));
                                    seq_filter_contains_implies_seq_contains(
                                        pods,
                                        pod_pred,
                                        pod
                                    );
                                    let j = choose |j: int| 0 <= j < pods.len() && pods[j] == pod;
                                    assert(pods[j] == pod);
                                    seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err());
                                    assert(objs.contains(objs[j]));
                                    assert(PodView::unmarshal(objs[j]).unwrap() == pod);
                                    assert(owned_selector_match_is(vrs, objs[j]));
                                    assert(objs.filter(osm_pred).contains(objs[j]));
                                    let k = choose |k: int| 0 <= k < objs.filter(osm_pred).len() && objs.filter(osm_pred)[k] == objs[j];
                                    assert(PodView::unmarshal(objs.filter(osm_pred)[k]).unwrap() == pod);
                                    assert(objs.filter(osm_pred).map_values(obj_to_pod)[k] == pod);
                                }
                                assert forall |p: PodView| #![auto]
                                    post(s)
                                    && stronger_next(s, s_prime)
                                    && objs.filter(osm_pred).map_values(obj_to_pod).to_set().contains(p)
                                    implies filtered_pods.to_set().contains(p) by {
                                    let i = choose |i: int|
                                        0 <= i < objs.filter(osm_pred).map_values(obj_to_pod).len()
                                        && objs.filter(osm_pred).map_values(obj_to_pod)[i] == p;
                                    assert(objs.filter(osm_pred).map_values(obj_to_pod)[i] == p);
                                    assert(PodView::unmarshal(objs.filter(osm_pred)[i]).unwrap() == p);
                                    seq_filter_contains_implies_seq_contains(
                                        objs,
                                        osm_pred,
                                        objs.filter(osm_pred)[i]
                                    );
                                    seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err());
                                    assert(objs.contains(objs.filter(osm_pred)[i]));
                                    assert(osm_pred(objs.filter(osm_pred)[i]));
                                    let pod_pred = |pod: PodView|
                                        pod.metadata.owner_references_contains(vrs.controller_owner_ref())
                                        && vrs.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                        && pod.metadata.deletion_timestamp.is_None();
                                    let j = choose |j: int| 0 <= j < objs.len() && objs[j] == objs.filter(osm_pred)[i];
                                    assert(PodView::unmarshal(objs[j]).unwrap() == pods[j]);
                                    assert(pod_pred(pods[j]));
                                    assert(filtered_pods.contains(pods[j]));
                                }
                            }
                        );
                        assert(filtered_pods.to_set().len() == vrs.spec.replicas.unwrap_or(0));
                        assert_by(filtered_pod_keys.no_duplicates(), {
                            assert forall |i: int, j: int| #![auto]
                                0 <= i < filtered_pod_keys.len()
                                && 0 <= j < filtered_pod_keys.len()
                                && i != j
                                && post(s)
                                && stronger_next(s, s_prime)
                                && pods.no_duplicates()
                                implies filtered_pod_keys[i] != filtered_pod_keys[j] by {

                                seq_filter_contains_implies_seq_contains(
                                    pods,
                                    |pod: PodView|
                                        pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                                        && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                        && pod.metadata.deletion_timestamp.is_None(),
                                    filtered_pods[i]
                                );
                                seq_filter_contains_implies_seq_contains(
                                    pods,
                                    |pod: PodView|
                                        pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                                        && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                        && pod.metadata.deletion_timestamp.is_None(),
                                    filtered_pods[j]
                                );

                                let idxi = choose |idx| 0 <= idx < pods.len() && pods[idx] == filtered_pods[i];
                                let idxj = choose |idx| 0 <= idx < pods.len() && pods[idx] == filtered_pods[j];

                                assert(pods == objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()));
                                assert(pods.len() == objs.len());
                                seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                    objs,
                                    |obj: DynamicObjectView| PodView::unmarshal(obj).is_err()
                                );
                                assert(objs.contains(objs[idxi]));
                                assert(objs.contains(objs[idxj]));
                                assert(PodView::unmarshal(objs[idxi]).is_Ok());
                                assert(PodView::unmarshal(objs[idxj]).is_Ok());

                                assert(pods[idxi] == PodView::unmarshal(objs[idxi]).get_Ok_0());
                                assert(pods[idxj] == PodView::unmarshal(objs[idxj]).get_Ok_0());

                                assert(pods[idxi].object_ref() == objs[idxi].object_ref());
                                assert(pods[idxj].object_ref() == objs[idxj].object_ref());

                                if idxi == idxj {
                                    seq_filter_preserves_no_duplicates(
                                        pods,
                                        |pod: PodView|
                                            pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                                            && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                            && pod.metadata.deletion_timestamp.is_None(),
                                    );
                                } else {
                                    assert(obj_keys[idxi] == objs[idxi].object_ref());
                                    assert(obj_keys[idxj] == objs[idxj].object_ref());
                                    assert(objs[idxi].object_ref() != objs[idxj].object_ref());
                                }
                            }
                        });
                        assert_by(filtered_pods.no_duplicates(), {
                            let to_dyn_obj = |p: PodView| p.marshal();
                            assert forall |i: int, j: int| #![auto]
                                0 <= i < filtered_pods.len()
                                && 0 <= j < filtered_pods.len()
                                && i != j
                                && post(s)
                                && stronger_next(s, s_prime)
                                && filtered_pod_keys.no_duplicates()
                                implies filtered_pods[i]
                                    != filtered_pods[j] by {
                                assert(filtered_pods[i].object_ref() == filtered_pod_keys[i]);
                                assert(filtered_pods[j].object_ref() == filtered_pod_keys[j]);
                            }
                        });
                        filtered_pods.unique_seq_to_set();
                        assert(filtered_pods.len() == vrs.spec.replicas.unwrap_or(0));
                    }
                    if at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init)(s) {
                         // prove that the newly sent message has no response.
                         if s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.is_Some() {
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                            assert(forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id);
                            assert(s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg));
                            assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
                                && (forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id)
                                && s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg)
                                && msg != req_msg
                                implies msg.rpc_id != req_msg.rpc_id by {
                                if !s.in_flight().contains(msg) {} // need this to invoke trigger.
                            }
                        }
                    }
                } else if !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) {
                    // this empty case speeds up verification.
                }
            },
            _ => {
                let new_msgs = s_prime.in_flight().sub(s.in_flight());

                let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                let triggering_cr = VReplicaSetView::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).unwrap();
                let filtered_pods = state.filtered_pods.unwrap();

                // Maintain quantified invariant.
                if at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterListPods)(s) {
                    let req_msg = s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.get_Some_0();
                    assert forall |msg| {
                        let req_msg = s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                        &&& #[trigger] s_prime.in_flight().contains(msg)
                        &&& s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                        &&& msg.src.is_APIServer()
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                        &&& stronger_next(s, s_prime)
                    } implies {
                        let resp_objs = msg.content.get_list_response().res.unwrap();
                        let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                        &&& msg.content.is_list_response()
                        &&& msg.content.get_list_response().res.is_Ok()
                        &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0
                        &&& resp_obj_keys.no_duplicates()
                        &&& matching_pod_entries(vrs, s.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                        &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                    } by {
                        assert(forall |msg| #[trigger] new_msgs.contains(msg) ==> !(#[trigger] msg.src.is_APIServer()));
                        if !new_msgs.contains(msg) {
                            assert(s.in_flight().contains(msg));
                        }
                    }
                }
            }
        }
    }

    leads_to_stable(spec, lift_action(stronger_next), p, lift_state(post));
    leads_to_always_enhance(spec, true_pred(), p, lift_state(post), lift_state(final_post));
}

}
