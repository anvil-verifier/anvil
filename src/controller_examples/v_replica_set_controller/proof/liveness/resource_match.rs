// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*,
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*, string_view::*};
use crate::v_replica_set_controller::{
    model::{reconciler::*},
    proof::{helper_invariants, predicate::*, liveness::api_actions::*},
    trusted::{spec_types::*, step::*, liveness_theorem::*},
};
use vstd::{prelude::*, seq::*, seq_lib::*, set_lib::*, string::*, map::*, map_lib::*, math::abs};

verus! {

pub proof fn lemma_from_diff_and_init_to_current_state_matches(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int,
)
    requires
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        spec.entails(always(lift_state(VRSCluster::no_pending_req_msg_at_reconcile_state(
            vrs.object_ref(), |s: VReplicaSetReconcileState| s.reconcile_step == VReplicaSetReconcileStep::Init)))),
        spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_replicas_bounded(vrs)))),
        spec.entails(always(lift_state(helper_invariants::vrs_selector_matches_template_labels(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed()))),
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
    let invariants = {
        &&& spec.entails(always(lift_action(VRSCluster::next())))
        &&& spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i)))
        &&& spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i)))
        &&& spec.entails(always(lift_state(VRSCluster::crash_disabled())))
        &&& spec.entails(always(lift_state(VRSCluster::busy_disabled())))
        &&& spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id())))
        &&& spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed())))
        &&& spec.entails(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())))
        &&& spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref()))))
        &&& spec.entails(always(lift_state(VRSCluster::no_pending_req_msg_at_reconcile_state(
            vrs.object_ref(), |s: VReplicaSetReconcileState| s.reconcile_step == VReplicaSetReconcileStep::Init))))
        &&& spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite())))
        &&& spec.entails(always(lift_state(helper_invariants::vrs_replicas_bounded(vrs))))
        &&& spec.entails(always(lift_state(helper_invariants::vrs_selector_matches_template_labels(vrs))))
        &&& spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed())))
        &&& spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods())))
        &&& spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs))))
        &&& spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))))
    };
    let pre = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& no_pending_req_at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::Init)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let list_req = |diff: int| lift_state(
        |s: VRSCluster| {
            &&& pending_req_in_flight_at_after_list_pods_step(vrs)(s)
            &&& num_diff_pods_is(vrs, diff)(s)
        }
    );
    let list_req_msg = |req_msg: VRSMessage, diff: int| lift_state(
        |s: VRSCluster| {
            &&& req_msg_is_the_in_flight_list_req_at_after_list_pods_step(vrs, req_msg)(s)
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

    assert forall |req_msg: VRSMessage| 
                 invariants implies #[trigger] spec.entails(list_req_msg(req_msg, diff).leads_to(list_resp(diff))) by {
        lemma_from_after_send_list_pods_req_to_receive_list_pods_resp(spec, vrs, req_msg, diff);
    };
    leads_to_exists_intro(spec, |req_msg| list_req_msg(req_msg, diff), list_resp(diff));

    
    assert_by(spec.entails(list_req(diff).leads_to(tla_exists(|req_msg| list_req_msg(req_msg, diff)))), {
        assert forall |ex| #[trigger] list_req(diff).satisfied_by(ex) 
            implies tla_exists(|req_msg| list_req_msg(req_msg, diff)).satisfied_by(ex) by {
            let req_msg = ex.head().ongoing_reconciles()[vrs.object_ref()].pending_req_msg.get_Some_0();
            assert((|req_msg: VRSMessage| list_req_msg(req_msg, diff))(req_msg).satisfied_by(ex));
        };
        valid_implies_implies_leads_to(spec, list_req(diff), tla_exists(|req_msg| list_req_msg(req_msg, diff)));
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
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed()))),
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
        &&& helper_invariants::every_create_request_is_well_formed()(s)
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
        lift_state(helper_invariants::every_create_request_is_well_formed()),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| VRSCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let msg = input.unwrap();
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

pub proof fn lemma_from_after_send_list_pods_req_to_receive_list_pods_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, req_msg: VRSMessage, diff: int
)
    requires
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)))),
    ensures
        spec.entails(
            lift_state(
                |s: VRSCluster| {
                    &&& req_msg_is_the_in_flight_list_req_at_after_list_pods_step(vrs, req_msg)(s)
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
    let pre = |s: VRSCluster| {
        &&& req_msg_is_the_in_flight_list_req_at_after_list_pods_step(vrs, req_msg)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: VRSCluster| {
        &&& exists_resp_in_flight_at_after_list_pods_step(vrs)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: VRSCluster| {
        &&& VRSCluster::next()(s, s_prime)
        &&& VRSCluster::crash_disabled()(s)
        &&& VRSCluster::busy_disabled()(s)
        &&& VRSCluster::every_in_flight_msg_has_unique_id()(s)
        &&& VRSCluster::each_object_in_etcd_is_well_formed()(s)
        &&& helper_invariants::cluster_resources_is_finite()(s)
        &&& helper_invariants::every_create_request_is_well_formed()(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)(s)
        &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(VRSCluster::next()),
        lift_state(VRSCluster::crash_disabled()),
        lift_state(VRSCluster::busy_disabled()),
        lift_state(VRSCluster::every_in_flight_msg_has_unique_id()),
        lift_state(VRSCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::cluster_resources_is_finite()),
        lift_state(helper_invariants::every_create_request_is_well_formed()),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| VRSCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let msg = input.get_Some_0();
                lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
                    s, s_prime, vrs, diff, msg
                );
                // Prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is maintained.
                assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
                // Prod for the theorem prover to realize there is a response message.
                if msg == req_msg {
                    let resp_msg = VRSCluster::handle_list_request_msg(req_msg, s.kubernetes_api_state).1;
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
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
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

    assert forall |s, s_prime: VRSCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && VRSCluster::kubernetes_api_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let resp_msg = VRSCluster::handle_list_request_msg(req_msg, s.kubernetes_api_state).1;
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
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
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

    VRSCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, VRSCluster::handle_request(), pre, post
    );
}

// Lemmas for creating new pods to cover shortfalls.
pub proof fn lemma_from_after_receive_list_pods_resp_to_receive_create_pod_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int
)
    requires 
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_replicas_bounded(vrs)))),
        spec.entails(always(lift_state(helper_invariants::vrs_selector_matches_template_labels(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)))),
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
    let invariants = {
        &&& spec.entails(always(lift_action(VRSCluster::next())))
        &&& spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i)))
        &&& spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i)))
        &&& spec.entails(always(lift_state(VRSCluster::crash_disabled())))
        &&& spec.entails(always(lift_state(VRSCluster::busy_disabled())))
        &&& spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id())))
        &&& spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed())))
        &&& spec.entails(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())))
        &&& spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref()))))
        &&& spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite())))
        &&& spec.entails(always(lift_state(helper_invariants::vrs_replicas_bounded(vrs))))
        &&& spec.entails(always(lift_state(helper_invariants::vrs_selector_matches_template_labels(vrs))))
        &&& spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed())))
        &&& spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods())))
        &&& spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs))))
        &&& spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))))
    };
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
                        // The matching pods must be a subset of the response.
                        &&& matching_pod_entries(vrs, s.resources()).values().subset_of(resp_objs.to_set())
                        &&& objects_to_pods(resp_objs).is_Some()
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
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_replicas_bounded(vrs)))),
        spec.entails(always(lift_state(helper_invariants::vrs_selector_matches_template_labels(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)))),
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
    let invariants = {
        &&& spec.entails(always(lift_action(VRSCluster::next())))
        &&& spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i)))
        &&& spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i)))
        &&& spec.entails(always(lift_state(VRSCluster::crash_disabled())))
        &&& spec.entails(always(lift_state(VRSCluster::busy_disabled())))
        &&& spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id())))
        &&& spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed())))
        &&& spec.entails(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())))
        &&& spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref()))))
        &&& spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite())))
        &&& spec.entails(always(lift_state(helper_invariants::vrs_replicas_bounded(vrs))))
        &&& spec.entails(always(lift_state(helper_invariants::vrs_selector_matches_template_labels(vrs))))
        &&& spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed())))
        &&& spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods())))
        &&& spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs))))
        &&& spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))))
    };
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

pub proof fn lemma_from_after_receive_list_pods_resp_to_send_create_pod_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, resp_msg: VRSMessage, diff: int
)
    requires
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_replicas_bounded(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)))),
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
    let pre = |s: VRSCluster| {
        &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, resp_msg)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: VRSCluster| {
        &&& pending_req_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let input = (Some(resp_msg), Some(vrs.object_ref()));
    let stronger_next = |s, s_prime: VRSCluster| {
        &&& VRSCluster::next()(s, s_prime)
        &&& VRSCluster::crash_disabled()(s)
        &&& VRSCluster::busy_disabled()(s)
        &&& VRSCluster::every_in_flight_msg_has_unique_id()(s)
        &&& VRSCluster::each_object_in_etcd_is_well_formed()(s)
        &&& VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())(s)
        &&& helper_invariants::cluster_resources_is_finite()(s)
        &&& helper_invariants::vrs_replicas_bounded(vrs)(s)
        &&& helper_invariants::every_create_request_is_well_formed()(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)(s)
        &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(VRSCluster::next()),
        lift_state(VRSCluster::crash_disabled()),
        lift_state(VRSCluster::busy_disabled()),
        lift_state(VRSCluster::every_in_flight_msg_has_unique_id()),
        lift_state(VRSCluster::each_object_in_etcd_is_well_formed()),
        lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())),
        lift_state(helper_invariants::cluster_resources_is_finite()),
        lift_state(helper_invariants::vrs_replicas_bounded(vrs)),
        lift_state(helper_invariants::every_create_request_is_well_formed()),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| VRSCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let msg = input.unwrap();
                lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
                    s, s_prime, vrs, diff, msg
                );
                // Small prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is maintained.
                assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
            },
            Step::ControllerStep(input) => {
                if input.0 == Some(resp_msg) && input.1 == Some(vrs.object_ref()) {
                    lemma_filtered_pods_len_equals_matching_pods_len(s, vrs, resp_msg);
                }
            },
            _ => {}
        }
    }

    VRSCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next, VRSCluster::continue_reconcile(), pre, post
    );
}

#[verifier(external_body)]
pub proof fn lemma_filtered_pods_len_equals_matching_pods_len(
    s: VRSCluster, vrs: VReplicaSetView, resp_msg: VRSMessage
)
    ensures
        ({
            let objs = resp_msg.content.get_list_response().res.unwrap();
            let pods_or_none = objects_to_pods(objs);
            let pods = pods_or_none.unwrap();
            let filtered_pods = filter_pods(pods, vrs);
            filtered_pods.len() == matching_pods(vrs, s.resources()).len()
        }),
{}
//
// @Xudong Sun take a look.
//
// filter_pods filters pods in a very similar way to matching_pods, but the former
// works on a sequence of PodViews, while the latter works on the key-value store directly.
// I'll probably come back to this soon.
//


pub proof fn lemma_from_after_send_create_pod_req_to_receive_ok_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, req_msg: VRSMessage, diff: int
)
    requires 
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_selector_matches_template_labels(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)))),
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
    let pre = |s: VRSCluster| {
        &&& req_msg_is_the_in_flight_create_request_at_after_create_pod_step(vrs, req_msg, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: VRSCluster| {
        &&& exists_ok_resp_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff + 1)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: VRSCluster| {
        &&& VRSCluster::next()(s, s_prime)
        &&& VRSCluster::crash_disabled()(s)
        &&& VRSCluster::busy_disabled()(s)
        &&& VRSCluster::every_in_flight_msg_has_unique_id()(s)
        &&& VRSCluster::each_object_in_etcd_is_well_formed()(s)
        &&& helper_invariants::cluster_resources_is_finite()(s)
        &&& helper_invariants::vrs_selector_matches_template_labels(vrs)(s)
        &&& helper_invariants::every_create_request_is_well_formed()(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)(s)
        &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(VRSCluster::next()),
        lift_state(VRSCluster::crash_disabled()),
        lift_state(VRSCluster::busy_disabled()),
        lift_state(VRSCluster::every_in_flight_msg_has_unique_id()),
        lift_state(VRSCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::cluster_resources_is_finite()),
        lift_state(helper_invariants::vrs_selector_matches_template_labels(vrs)),
        lift_state(helper_invariants::every_create_request_is_well_formed()),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| VRSCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let msg = input.get_Some_0();
                // Case 1: We're processing the create request
                if msg == req_msg {
                    let resp_msg = VRSCluster::handle_create_request_msg(req_msg, s.kubernetes_api_state).1;
                    let req = req_msg.content.get_create_request();
                    let created_obj = DynamicObjectView {
                        kind: req.obj.kind,
                        metadata: ObjectMetaView {
                            // Set name for new object if name is not provided, here we generate
                            // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
                            name: if req.obj.metadata.name.is_Some() {
                                req.obj.metadata.name
                            } else {
                                Some(generate_name(s.kubernetes_api_state))
                            },
                            namespace: Some(req.namespace), // Set namespace for new object
                            resource_version: Some(s.kubernetes_api_state.resource_version_counter), // Set rv for new object
                            uid: Some(s.kubernetes_api_state.uid_counter), // Set uid for new object
                            deletion_timestamp: None, // Unset deletion timestamp for new object
                            ..req.obj.metadata
                        },
                        spec: req.obj.spec,
                        status: marshalled_default_status::<VReplicaSetView>(req.obj.kind), // Overwrite the status with the default one
                    };
                    let key = created_obj.object_ref();

                    // Asserts properties about the response message
                    generated_name_is_unique(s.kubernetes_api_state);
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
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
                    a_submap_of_a_finite_map_is_finite(matching_pod_entries(vrs, s.resources()), s.resources());
                    lemma_api_request_not_on_matching_pods_maintains_matching_pods(
                        s, s_prime, vrs, diff, msg, req_msg,
                    );
                    assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime: VRSCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && VRSCluster::kubernetes_api_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let resp_msg = VRSCluster::handle_create_request_msg(req_msg, s.kubernetes_api_state).1;
        let req = req_msg.content.get_create_request();
        let created_obj = DynamicObjectView {
            kind: req.obj.kind,
            metadata: ObjectMetaView {
                // Set name for new object if name is not provided, here we generate
                // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
                name: if req.obj.metadata.name.is_Some() {
                    req.obj.metadata.name
                } else {
                    Some(generate_name(s.kubernetes_api_state))
                },
                namespace: Some(req.namespace), // Set namespace for new object
                resource_version: Some(s.kubernetes_api_state.resource_version_counter), // Set rv for new object
                uid: Some(s.kubernetes_api_state.uid_counter), // Set uid for new object
                deletion_timestamp: None, // Unset deletion timestamp for new object
                ..req.obj.metadata
            },
            spec: req.obj.spec,
            status: marshalled_default_status::<VReplicaSetView>(req.obj.kind), // Overwrite the status with the default one
        };
        let key = created_obj.object_ref();

        // Asserts properties about the response message
        generated_name_is_unique(s.kubernetes_api_state);
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
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

    VRSCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, VRSCluster::handle_request(), pre, post
    );
}

pub proof fn lemma_from_after_receive_ok_resp_to_send_create_pod_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, resp_msg: VRSMessage, diff: int
)
    requires 
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_replicas_bounded(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)))),
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
    let pre = |s: VRSCluster| {
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_create_pod_step(vrs, resp_msg, abs(diff))(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: VRSCluster| {
        &&& pending_req_in_flight_at_after_create_pod_step(vrs, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let input = (Some(resp_msg), Some(vrs.object_ref()));
    let stronger_next = |s, s_prime: VRSCluster| {
        &&& VRSCluster::next()(s, s_prime)
        &&& VRSCluster::crash_disabled()(s)
        &&& VRSCluster::busy_disabled()(s)
        &&& VRSCluster::every_in_flight_msg_has_unique_id()(s)
        &&& VRSCluster::each_object_in_etcd_is_well_formed()(s)
        &&& VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())(s)
        &&& helper_invariants::cluster_resources_is_finite()(s)
        &&& helper_invariants::vrs_replicas_bounded(vrs)(s)
        &&& helper_invariants::every_create_request_is_well_formed()(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)(s)
        &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(VRSCluster::next()),
        lift_state(VRSCluster::crash_disabled()),
        lift_state(VRSCluster::busy_disabled()),
        lift_state(VRSCluster::every_in_flight_msg_has_unique_id()),
        lift_state(VRSCluster::each_object_in_etcd_is_well_formed()),
        lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())),
        lift_state(helper_invariants::cluster_resources_is_finite()),
        lift_state(helper_invariants::vrs_replicas_bounded(vrs)),
        lift_state(helper_invariants::every_create_request_is_well_formed()),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| VRSCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                // TODO: This could be sped up a bit by extra annotations, but it goes through automatically.

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

// Lemmas for deleting excess pods.
pub proof fn lemma_from_after_receive_list_pods_resp_to_receive_delete_pod_resp(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, diff: int
)
    requires 
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_replicas_bounded(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)))),
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
                        // The matching pods must be a subset of the response.
                        &&& matching_pod_entries(vrs, s.resources()).values().subset_of(resp_objs.to_set())
                        &&& objects_to_pods(resp_objs).is_Some()
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

pub proof fn lemma_from_after_receive_list_pods_resp_to_send_delete_pod_req(
    spec: TempPred<VRSCluster>, vrs: VReplicaSetView, resp_msg: VRSMessage, diff: int
)
    requires 
        spec.entails(always(lift_action(VRSCluster::next()))),
        spec.entails(tla_forall(|i| VRSCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(VRSCluster::crash_disabled()))),
        spec.entails(always(lift_state(VRSCluster::busy_disabled()))),
        spec.entails(always(lift_state(VRSCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::cluster_resources_is_finite()))),
        spec.entails(always(lift_state(helper_invariants::vrs_replicas_bounded(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_create_request_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)))),
        spec.entails(always(lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)))),
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
    let pre = |s: VRSCluster| {
        &&& resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, resp_msg)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let post = |s: VRSCluster| {
        &&& pending_req_in_flight_at_after_delete_pod_step(vrs, (abs(diff) - 1) as nat)(s)
        &&& num_diff_pods_is(vrs, diff)(s)
    };
    let input = (Some(resp_msg), Some(vrs.object_ref()));
    let stronger_next = |s, s_prime: VRSCluster| {
        &&& VRSCluster::next()(s, s_prime)
        &&& VRSCluster::crash_disabled()(s)
        &&& VRSCluster::busy_disabled()(s)
        &&& VRSCluster::every_in_flight_msg_has_unique_id()(s)
        &&& VRSCluster::each_object_in_etcd_is_well_formed()(s)
        &&& VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())(s)
        &&& helper_invariants::cluster_resources_is_finite()(s)
        &&& helper_invariants::vrs_replicas_bounded(vrs)(s)
        &&& helper_invariants::every_create_request_is_well_formed()(s)
        &&& helper_invariants::no_pending_update_or_update_status_request_on_pods()(s)
        &&& helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)(s)
        &&& helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(VRSCluster::next()),
        lift_state(VRSCluster::crash_disabled()),
        lift_state(VRSCluster::busy_disabled()),
        lift_state(VRSCluster::every_in_flight_msg_has_unique_id()),
        lift_state(VRSCluster::each_object_in_etcd_is_well_formed()),
        lift_state(VRSCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(VRSCluster::pending_req_of_key_is_unique_with_unique_id(vrs.object_ref())),
        lift_state(helper_invariants::cluster_resources_is_finite()),
        lift_state(helper_invariants::vrs_replicas_bounded(vrs)),
        lift_state(helper_invariants::every_create_request_is_well_formed()),
        lift_state(helper_invariants::no_pending_update_or_update_status_request_on_pods()),
        lift_state(helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs)),
        lift_state(helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| VRSCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let msg = input.unwrap();
                lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
                    s, s_prime, vrs, diff, msg
                );
                // Small prod for the theorem prover to realize num_diff_pods_is(vrs, diff) is maintained.
                assert(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
            },
            Step::ControllerStep(input) => {
                if input.0 == Some(resp_msg) && input.1 == Some(vrs.object_ref()) {
                    let objs = resp_msg.content.get_list_response().res.unwrap();
                    let pods_or_none = objects_to_pods(objs);
                    let pods = pods_or_none.unwrap();
                    let filtered_pods = filter_pods(pods, vrs);
                    lemma_filtered_pods_set_equals_matching_pods(s, vrs, resp_msg);

                    let filtered_pods_as_objects = filtered_pods.map_values(|p: PodView| p.marshal());
                    let filtered_pods_as_set = filtered_pods_as_objects.to_set();
                    assert(filtered_pods_as_objects[diff - 1] == filtered_pods[diff - 1].marshal());
                    assert(filtered_pods_as_set.contains(filtered_pods[diff - 1].marshal()));
                }
            },
            _ => {}
        }
    }

    VRSCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next, VRSCluster::continue_reconcile(), pre, post
    );
}

#[verifier(external_body)]
pub proof fn lemma_filtered_pods_set_equals_matching_pods(
    s: VRSCluster, vrs: VReplicaSetView, resp_msg: VRSMessage
)
    ensures
        ({
            let objs = resp_msg.content.get_list_response().res.unwrap();
            let pods_or_none = objects_to_pods(objs);
            let pods = pods_or_none.unwrap();
            let filtered_pods = filter_pods(pods, vrs);
            &&& filtered_pods.no_duplicates()
            &&& filtered_pods.len() == matching_pod_entries(vrs, s.resources()).len()
            &&& filtered_pods.map_values(|p: PodView| p.marshal()).to_set() == matching_pod_entries(vrs, s.resources()).values()
        }),
{}
//
// This might actually be slightly trickier than the previous one.
//

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
