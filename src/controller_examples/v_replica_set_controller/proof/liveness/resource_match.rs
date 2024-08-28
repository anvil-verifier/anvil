// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use crate::v_replica_set_controller::{
    model::{reconciler::*},
    proof::{helper_invariants, predicate::*, liveness::api_actions::*},
    trusted::{spec_types::*, step::*, liveness_theorem::*},
};
use vstd::{prelude::*, string::*, math::abs};

verus! {

pub proof fn lemma_from_diff_and_init_to_current_state_matches(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int,
)
    requires
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(VRSCluster::no_pending_req_msg_at_reconcile_state(
            vrs.object_ref(), |s: VReplicaSetReconcileState| s.reconcile_step == VReplicaSetReconcileStep::Init)))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_has_an_empty_deletion_timestamp()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)))),
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& no_pending_req_at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(lift_state(current_state_matches(vrs)))
        )
{
    let pre = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& no_pending_req_at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let list_resp = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // Deal with transition from init to listing the pods.
    lemma_from_init_step_to_send_list_pods_req(spec, vrs, diff);
    lemma_from_after_send_list_pods_req_to_receive_list_pods_resp(spec, vrs, diff);

    // TODO: Would an invariant be a better way of showing 
    // num_diff_pods_is is maintained across this introductory step?
    leads_to_trans_n!(
        spec, 
        pre(diff),
        lift_state(
            |s: VRSCluster| {
                &&& pending_req_in_flight_at_after_list_pods_step(vrs)(s)
                &&& num_diff_pods_is(vrs, diff)(s)
            }
        ),
        list_resp(diff)
    );

    // Now we've listed the pods, perform different behaviors accoding to the difference.
    if diff < 0 {
        let create_resp = |diff: int| lift_state(
            |s: VRSCluster| {
                &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, abs(diff))(s)
                &&& num_diff_pods_is(vrs, diff)(s)
            }
        );

        // Add first create pod request after listing pods to leads-to chain.
        lemma_from_after_receive_list_pods_resp_to_receive_create_pod_resp(spec, vrs, diff);
        leads_to_trans_n!(
            spec,
            pre(diff),
            list_resp(diff),
            create_resp(diff + 1)
        );

        // Is this enough?
        if diff + 1 == 0 {
            // If so, pre(diff) ~> current_state_matches(vrs) trivially.
            valid_implies_implies_leads_to(spec, create_resp(diff + 1), lift_state(current_state_matches(vrs)));
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
            valid_implies_implies_leads_to(spec, create_resp(-n), ranking_pred(n));
        };
    
        assert forall |n: nat| #![trigger create_resp(-n)]
                    spec.entails(ranking_pred(n).leads_to(create_resp(-n))) by {
            valid_implies_implies_leads_to(spec, ranking_pred(n), create_resp(-n));
        };

         // Proving n > 0 => ranking_pred(n) ~> ranking_pred(n - 1)
        assert forall |n: nat| #![trigger ranking_pred(n)] 
                    n > 0 implies spec.entails(ranking_pred(n).leads_to(ranking_pred((n - 1) as nat))) by {
            let diff = -n;
            lemma_from_after_receive_create_pod_resp_to_receive_create_pod_resp(spec, vrs, diff);

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
        valid_implies_implies_leads_to(spec, create_resp(0), lift_state(current_state_matches(vrs)));
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
            |s: VRSCluster| {
                &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, abs(diff))(s)
                &&& num_diff_pods_is(vrs, diff)(s)
            }
        );

        // Add first delete pod request after listing pods to leads-to chain.
        lemma_from_after_receive_list_pods_resp_to_receive_delete_pod_resp(spec, vrs, diff);
        leads_to_trans_n!(
            spec,
            pre(diff),
            list_resp(diff),
            delete_resp(diff - 1)
        );

        // Is this enough?
        if diff - 1 == 0 {
            // If so, pre(diff) ~> current_state_matches(vrs) trivially.
            valid_implies_implies_leads_to(spec, delete_resp(diff - 1), lift_state(current_state_matches(vrs)));
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
            valid_implies_implies_leads_to(spec, delete_resp(n as int), ranking_pred(n));
        };
    
        assert forall |n: nat| #![trigger ranking_pred(n)]
                    spec.entails(ranking_pred(n).leads_to(delete_resp(n as int))) by {
            valid_implies_implies_leads_to(spec, ranking_pred(n), delete_resp(n as int));
        };

         // Proving n > 0 => ranking_pred(n) ~> ranking_pred(n - 1)
        assert forall |n: nat| #![trigger ranking_pred(n)] 
                    n > 0 implies spec.entails(ranking_pred(n).leads_to(ranking_pred((n - 1) as nat))) by {
            let diff = n as int;
            lemma_from_after_receive_delete_pod_resp_to_receive_delete_pod_resp(spec, vrs, diff);

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
        valid_implies_implies_leads_to(spec, delete_resp(0), lift_state(current_state_matches(vrs)));
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
        valid_implies_implies_leads_to(spec, list_resp(diff), lift_state(current_state_matches(vrs)));
        leads_to_trans_n!(
            spec, 
            pre(diff),
            list_resp(diff),
            lift_state(current_state_matches(vrs))
        );
    }
}

pub proof fn lemma_from_init_step_to_send_list_pods_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int
)
    requires
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(VRSCluster::no_pending_req_msg_at_reconcile_state(
            vrs.object_ref(), |s: VReplicaSetReconcileState| s.reconcile_step == VReplicaSetReconcileStep::Init)))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_has_an_empty_deletion_timestamp()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)))),
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& no_pending_req_at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& pending_req_in_flight_at_after_list_pods_step(vrs)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        )
{
    let pre = |s: VRSCluster| {
        &&& no_pending_req_at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: VRSCluster| {
        &&& pending_req_in_flight_at_after_list_pods_step(vrs)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let input = (None, Some(vrs.object_ref()));
    let stronger_next = |s, s_prime: VRSCluster| {
        &&& VRSCluster::next()(s, s_prime)
        &&& VRSCluster::crash_disabled()(s)
        &&& VRSCluster::busy_disabled()(s)
        &&& VRSCluster::every_in_flight_msg_has_unique_id()(s)
        &&& VRSCluster::each_object_in_etcd_is_well_formed()(s)
        &&& VRSCluster::no_pending_req_msg_at_reconcile_state(vrs.object_ref(), 
                |s: VReplicaSetReconcileState| s.reconcile_step == VReplicaSetReconcileStep::Init)(s)
        &&& helper_invariants::every_create_request_has_an_empty_deletion_timestamp()(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)(s)
        &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)(s)
    };
    let state_is_init = |s: VReplicaSetReconcileState| s.reconcile_step == VReplicaSetReconcileStep::Init;
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(VRSCluster::next()),
        lift_state(VRSCluster::crash_disabled()),
        lift_state(VRSCluster::busy_disabled()),
        lift_state(VRSCluster::every_in_flight_msg_has_unique_id()),
        lift_state(VRSCluster::each_object_in_etcd_is_well_formed()),
        lift_state(VRSCluster::no_pending_req_msg_at_reconcile_state(vrs.object_ref(), state_is_init)),
        lift_state(helper_invariants::every_create_request_has_an_empty_deletion_timestamp()),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| VRSCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(msg) => {
                let msg = msg.unwrap();
                lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
                    s, s_prime, vrs, diff, msg
                );
                // Small prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is maintained.
                assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
            },
            _ => {}
        }
    }

    VRSCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next, VRSCluster::continue_reconcile(), pre, post
    );
}

#[verifier(external_body)]
pub proof fn lemma_from_after_send_list_pods_req_to_receive_list_pods_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int
)
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& pending_req_in_flight_at_after_list_pods_step(vrs)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        )
{
}

// Lemmas for creating new pods to cover shortfalls.
pub proof fn lemma_from_after_receive_list_pods_resp_to_receive_create_pod_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int
)
    requires 
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff + 1)(s)
                    }
                )
            )
        ),
{
    let list_resp = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let list_resp_msg = |resp_msg: VRSMessage, diff: int| lift_state(
        |s: VRSCluster| {
            &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, resp_msg)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_req_msg = |req_msg: VRSMessage, diff: int| lift_state(
        |s: VRSCluster| {
        &&& req_msg_is_the_in_flight_create_request_at_after_create_pod_step(vrs, req_msg, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_req = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& pending_req_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_resp_msg = |resp_msg: VRSMessage, diff: int| lift_state(
        |s: VRSCluster| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, resp_msg, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_resp = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // Apply two lemmas relating to the first created pod.
    assert forall |resp_msg: VRSMessage| 
                diff < 0 implies #[trigger] spec.entails(list_resp_msg(resp_msg, diff).leads_to(create_req(diff))) by {
        lemma_from_after_receive_list_pods_resp_to_send_create_pod_req(spec, vrs, resp_msg, diff);
    };
    assert forall |req_msg: VRSMessage| 
                diff < 0 implies #[trigger] spec.entails(create_req_msg(req_msg, diff).leads_to(create_resp(diff + 1))) by {
        lemma_from_after_send_create_pod_req_to_receive_ok_resp(spec, vrs, req_msg, diff);
    };

    // Chain lemmas by transitivity.
    leads_to_exists_intro(spec, |resp_msg: VRSMessage| list_resp_msg(resp_msg, diff), create_req(diff));
    leads_to_exists_intro(spec, |req_msg: VRSMessage| create_req_msg(req_msg, diff), create_resp(diff + 1));
    assert_by(
        spec.entails(list_resp(diff).leads_to(tla_exists(|resp_msg: VRSMessage| list_resp_msg(resp_msg, diff)))),
        {
            assert forall |ex| #[trigger] list_resp(diff).satisfied_by(ex) 
                implies tla_exists(|resp_msg: VRSMessage| list_resp_msg(resp_msg, diff)).satisfied_by(ex) by {
                let s = ex.head();
                let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_list_response().res.is_Ok()
                    &&& {
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        // The response must give back all the pods in the replicaset's namespace.
                        resp_objs.to_set() == s.resources().values().filter(
                            |o: DynamicObjectView| {
                                &&& o.kind == PodView::kind()
                                &&& o.metadata.namespace.is_Some()
                                &&& o.metadata.namespace.unwrap() == vrs.metadata.namespace.unwrap()
                            }
                        )
                    }
                };
                assert((|resp_msg: VRSMessage| list_resp_msg(resp_msg, diff))(resp_msg).satisfied_by(ex));
            };
            valid_implies_implies_leads_to(spec, list_resp(diff), tla_exists(|resp_msg: VRSMessage| list_resp_msg(resp_msg, diff)));
        }
    );
    assert_by(
        spec.entails(create_req(diff).leads_to(tla_exists(|req_msg: VRSMessage| create_req_msg(req_msg, diff)))),
        {
            assert forall |ex| #[trigger] create_req(diff).satisfied_by(ex) 
                implies tla_exists(|req_msg: VRSMessage| create_req_msg(req_msg, diff)).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
                assert((|req_msg: VRSMessage| create_req_msg(req_msg, diff))(req_msg).satisfied_by(ex));
            };
            valid_implies_implies_leads_to(spec, create_req(diff), tla_exists(|req_msg: VRSMessage| create_req_msg(req_msg, diff)));
        }
    );
    leads_to_trans_n!(
        spec,
        list_resp(diff),
        tla_exists(|resp_msg: VRSMessage| list_resp_msg(resp_msg, diff)), 
        create_req(diff),
        tla_exists(|req_msg: VRSMessage| create_req_msg(req_msg, diff)),
        create_resp(diff + 1)
    );
}

pub proof fn lemma_from_after_receive_create_pod_resp_to_receive_create_pod_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int
)
    requires 
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, abs(diff))(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff + 1)(s)
                    }
                )
            )
        ),
{
    let create_req_msg = |req_msg: VRSMessage, diff: int| lift_state(|s: VRSCluster| {
        &&& req_msg_is_the_in_flight_create_request_at_after_create_pod_step(vrs, req_msg, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    });
    let create_req = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& pending_req_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_resp_msg = |resp_msg: VRSMessage, diff: int| lift_state(
        |s: VRSCluster| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, resp_msg, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let create_resp = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // Apply two lemmas relating to subsequent created pods.
    assert forall |resp_msg: VRSMessage| 
                diff < 0 implies #[trigger] spec.entails(create_resp_msg(resp_msg, diff).leads_to(create_req(diff))) by {
        lemma_from_after_receive_ok_resp_to_send_create_pod_req(spec, vrs, resp_msg, diff);
    };
    assert forall |req_msg: VRSMessage| 
                diff < 0 implies #[trigger] spec.entails(create_req_msg(req_msg, diff).leads_to(create_resp(diff + 1))) by {
        lemma_from_after_send_create_pod_req_to_receive_ok_resp(spec, vrs, req_msg, diff);
    };

    // Chain the lemmas by transitivity.
    leads_to_exists_intro(spec, |resp_msg: VRSMessage| create_resp_msg(resp_msg, diff), create_req(diff));
    leads_to_exists_intro(spec, |req_msg: VRSMessage| create_req_msg(req_msg, diff), create_resp(diff + 1));
    assert_by(
        spec.entails(create_req(diff).leads_to(tla_exists(|req_msg: VRSMessage| create_req_msg(req_msg, diff)))),
        {
            assert forall |ex| #[trigger] create_req(diff).satisfied_by(ex) 
                implies tla_exists(|req_msg: VRSMessage| create_req_msg(req_msg, diff)).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
                assert((|req_msg: VRSMessage| create_req_msg(req_msg, diff))(req_msg).satisfied_by(ex));
            };
            valid_implies_implies_leads_to(spec, create_req(diff), tla_exists(|req_msg: VRSMessage| create_req_msg(req_msg, diff)));
        }
    );
    assert_by(
        spec.entails(create_resp(diff).leads_to(tla_exists(|resp_msg: VRSMessage| create_resp_msg(resp_msg, diff)))),
        {
            assert forall |ex| #[trigger] create_resp(diff).satisfied_by(ex) 
                implies tla_exists(|resp_msg: VRSMessage| create_resp_msg(resp_msg, diff)).satisfied_by(ex) by {
                let s = ex.head();
                let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_create_response().res.is_Ok()
                };
                assert((|resp_msg: VRSMessage| create_resp_msg(resp_msg, diff))(resp_msg).satisfied_by(ex));
            };
            valid_implies_implies_leads_to(spec, create_resp(diff), tla_exists(|resp_msg: VRSMessage| create_resp_msg(resp_msg, diff)));
        }
    );

    leads_to_trans_n!(
        spec,
        create_resp(diff),
        tla_exists(|resp_msg: VRSMessage| create_resp_msg(resp_msg, diff)),
        create_req(diff),
        tla_exists(|req_msg: VRSMessage| create_req_msg(req_msg, diff)),
        create_resp(diff + 1)
    );
}

#[verifier(external_body)]
pub proof fn lemma_from_after_receive_list_pods_resp_to_send_create_pod_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, resp_msg: VRSMessage, diff: int
)
    requires 
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, resp_msg)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& pending_req_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
}

#[verifier(external_body)]
pub proof fn lemma_from_after_send_create_pod_req_to_receive_ok_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, req_msg: VRSMessage, diff: int
)
    requires 
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& req_msg_is_the_in_flight_create_request_at_after_create_pod_step(vrs, req_msg, (abs(diff) - 1) as nat)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff + 1)(s)
                    }
                )
            )
        ),
{
}

#[verifier(external_body)]
pub proof fn lemma_from_after_receive_ok_resp_to_send_create_pod_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, resp_msg: VRSMessage, diff: int
)
    requires 
        diff < 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, resp_msg, abs(diff))(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state (
                    |s: VRSCluster| {
                        &&& pending_req_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
}

// Lemmas for deleting excess pods.
pub proof fn lemma_from_after_receive_list_pods_resp_to_receive_delete_pod_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int
)
    requires 
        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, (diff - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff - 1)(s)
                    }
                )
            )
        ),
{
    let list_resp = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let list_resp_msg = |resp_msg: VRSMessage, diff: int| lift_state(
        |s: VRSCluster| {
            &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, resp_msg)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_req_msg = |req_msg: VRSMessage, diff: int| lift_state(
        |s: VRSCluster| {
        &&& req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(vrs, req_msg, (diff - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_req = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& pending_req_in_flight_at_after_delete_pod_step(vrs, (diff - 1) as nat)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_resp_msg = |resp_msg: VRSMessage, diff: int| lift_state(
        |s: VRSCluster| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, resp_msg, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_resp = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // Apply two lemmas relating to the first deleted pod.
    assert forall |resp_msg: VRSMessage| 
                diff > 0 implies #[trigger] spec.entails(list_resp_msg(resp_msg, diff).leads_to(delete_req(diff))) by {
        lemma_from_after_receive_list_pods_resp_to_send_delete_pod_req(spec, vrs, resp_msg, diff);
    };
    assert forall |req_msg: VRSMessage| 
                diff > 0 implies #[trigger] spec.entails(delete_req_msg(req_msg, diff).leads_to(delete_resp(diff - 1))) by {
        lemma_from_after_send_delete_pod_req_to_receive_ok_resp(spec, vrs, req_msg, diff);
    };

    // Chain lemmas by transitivity.
    leads_to_exists_intro(spec, |resp_msg: VRSMessage| list_resp_msg(resp_msg, diff), delete_req(diff));
    leads_to_exists_intro(spec, |req_msg: VRSMessage| delete_req_msg(req_msg, diff), delete_resp(diff - 1));
    assert_by(
        spec.entails(list_resp(diff).leads_to(tla_exists(|resp_msg: VRSMessage| list_resp_msg(resp_msg, diff)))),
        {
            assert forall |ex| #[trigger] list_resp(diff).satisfied_by(ex) 
                implies tla_exists(|resp_msg: VRSMessage| list_resp_msg(resp_msg, diff)).satisfied_by(ex) by {
                let s = ex.head();
                let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_list_response().res.is_Ok()
                    &&& {
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        // The response must give back all the pods in the replicaset's namespace.
                        resp_objs.to_set() == s.resources().values().filter(
                            |o: DynamicObjectView| {
                                &&& o.kind == PodView::kind()
                                &&& o.metadata.namespace.is_Some()
                                &&& o.metadata.namespace.unwrap() == vrs.metadata.namespace.unwrap()
                            }
                        )
                    }
                };
                assert((|resp_msg: VRSMessage| list_resp_msg(resp_msg, diff))(resp_msg).satisfied_by(ex));
            };
            valid_implies_implies_leads_to(spec, list_resp(diff), tla_exists(|resp_msg: VRSMessage| list_resp_msg(resp_msg, diff)));
        }
    );
    assert_by(
        spec.entails(delete_req(diff).leads_to(tla_exists(|req_msg: VRSMessage| delete_req_msg(req_msg, diff)))),
        {
            assert forall |ex| #[trigger] delete_req(diff).satisfied_by(ex) 
                implies tla_exists(|req_msg: VRSMessage| delete_req_msg(req_msg, diff)).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
                assert((|req_msg: VRSMessage| delete_req_msg(req_msg, diff))(req_msg).satisfied_by(ex));
            };
            valid_implies_implies_leads_to(spec, delete_req(diff), tla_exists(|req_msg: VRSMessage| delete_req_msg(req_msg, diff)));
        }
    );
    leads_to_trans_n!(
        spec,
        list_resp(diff),
        tla_exists(|resp_msg: VRSMessage| list_resp_msg(resp_msg, diff)), 
        delete_req(diff),
        tla_exists(|req_msg: VRSMessage| delete_req_msg(req_msg, diff)),
        delete_resp(diff - 1)
    );
}

pub proof fn lemma_from_after_receive_delete_pod_resp_to_receive_delete_pod_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int
)
    requires 
        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, diff as nat)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, (diff - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff - 1)(s)
                    }
                )
            )
        ),
{
    let delete_req_msg = |req_msg: VRSMessage, diff: int| lift_state(|s: VRSCluster| {
        &&& req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(vrs, req_msg, (diff - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    });
    let delete_req = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& pending_req_in_flight_at_after_delete_pod_step(vrs, (diff - 1) as nat)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_resp_msg = |resp_msg: VRSMessage, diff: int| lift_state(
        |s: VRSCluster| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, resp_msg, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let delete_resp = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, abs(diff))(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );

    // Apply two lemmas relating to subsequent deleted pods.
    assert forall |resp_msg: VRSMessage| 
                diff > 0 implies #[trigger] spec.entails(delete_resp_msg(resp_msg, diff).leads_to(delete_req(diff))) by {
        lemma_from_after_receive_ok_resp_to_send_delete_pod_req(spec, vrs, resp_msg, diff);
    };
    assert forall |req_msg: VRSMessage| 
                diff > 0 implies #[trigger] spec.entails(delete_req_msg(req_msg, diff).leads_to(delete_resp(diff - 1))) by {
        lemma_from_after_send_delete_pod_req_to_receive_ok_resp(spec, vrs, req_msg, diff);
    };

    // Chain the lemmas by transitivity.
    leads_to_exists_intro(spec, |resp_msg: VRSMessage| delete_resp_msg(resp_msg, diff), delete_req(diff));
    leads_to_exists_intro(spec, |req_msg: VRSMessage| delete_req_msg(req_msg, diff), delete_resp(diff - 1));
    assert_by(
        spec.entails(delete_req(diff).leads_to(tla_exists(|req_msg: VRSMessage| delete_req_msg(req_msg, diff)))),
        {
            assert forall |ex| #[trigger] delete_req(diff).satisfied_by(ex) 
                implies tla_exists(|req_msg: VRSMessage| delete_req_msg(req_msg, diff)).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
                assert((|req_msg: VRSMessage| delete_req_msg(req_msg, diff))(req_msg).satisfied_by(ex));
            };
            valid_implies_implies_leads_to(spec, delete_req(diff), tla_exists(|req_msg: VRSMessage| delete_req_msg(req_msg, diff)));
        }
    );
    assert_by(
        spec.entails(delete_resp(diff).leads_to(tla_exists(|resp_msg: VRSMessage| delete_resp_msg(resp_msg, diff)))),
        {
            assert forall |ex| #[trigger] delete_resp(diff).satisfied_by(ex) 
                implies tla_exists(|resp_msg: VRSMessage| delete_resp_msg(resp_msg, diff)).satisfied_by(ex) by {
                let s = ex.head();
                let msg = s.ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
                    &&& resp_msg.content.get_delete_response().res.is_Ok()
                };
                assert((|resp_msg: VRSMessage| delete_resp_msg(resp_msg, diff))(resp_msg).satisfied_by(ex));
            };
            valid_implies_implies_leads_to(spec, delete_resp(diff), tla_exists(|resp_msg: VRSMessage| delete_resp_msg(resp_msg, diff)));
        }
    );

    leads_to_trans_n!(
        spec,
        delete_resp(diff),
        tla_exists(|resp_msg: VRSMessage| delete_resp_msg(resp_msg, diff)),
        delete_req(diff),
        tla_exists(|req_msg: VRSMessage| delete_req_msg(req_msg, diff)),
        delete_resp(diff - 1)
    );
}

#[verifier(external_body)]
pub proof fn lemma_from_after_receive_list_pods_resp_to_send_delete_pod_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, resp_msg: VRSMessage, diff: int
)
    requires 
        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, resp_msg)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& pending_req_in_flight_at_after_delete_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
}

#[verifier(external_body)]
pub proof fn lemma_from_after_send_delete_pod_req_to_receive_ok_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, req_msg: VRSMessage, diff: int
)
    requires 
        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& req_msg_is_the_in_flight_delete_request_at_after_delete_pod_step(vrs, req_msg, (abs(diff) - 1) as nat)(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state(
                    |s: VRSCluster| {
                        &&& exists_ok_resp_in_flight_at_after_delete_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff - 1)(s)
                    }
                )
            )
        ),
{
}

#[verifier(external_body)]
pub proof fn lemma_from_after_receive_ok_resp_to_send_delete_pod_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, resp_msg: VRSMessage, diff: int
)
    requires 
        diff > 0,
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& resp_msg_is_the_in_flight_ok_resp_at_after_delete_pod_step(vrs, resp_msg, abs(diff))(s)
                    &&& num_diff_pods_is(vrs, diff)(s)
                }
            ).leads_to(
                lift_state (
                    |s: VRSCluster| {
                        &&& pending_req_in_flight_at_after_delete_pod_step(vrs, (abs(diff) - 1) as nat)(s)
                        &&& num_diff_pods_is(vrs, diff)(s)
                    }
                )
            )
        ),
{
}

// Ensures that once we've reconciled, we stay reconciled.
#[verifier(external_body)]
pub proof fn lemma_current_state_matches_is_stable(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, p: TempPred<VRSCluster>
)
    requires
        spec.entails(p.leads_to(lift_state(current_state_matches(vrs)))),
    ensures
        spec.entails(p.leads_to(always(lift_state(current_state_matches(vrs))))),
{
}

}
