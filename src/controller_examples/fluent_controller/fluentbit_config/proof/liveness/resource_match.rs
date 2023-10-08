// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit_config::{
    common::*,
    proof::{
        helper_invariants, liveness::spec::assumption_and_invariants_of_all_phases, predicate::*,
        resource::*,
    },
    spec::{reconciler::*, resource::*, types::*},
};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{prelude::*, string::*};

verus! {

pub open spec fn sub_resource_state_matches(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        resource_state_matches(sub_resource, fbc, s.resources())
    }
}

/// Proves AtAfterKRequestStep(Get, sub_resource) ~> sub_resource_state_matches(sub_resource, fbc) and AtAfterKRequestStep(Get, sub_resource) ~>
/// AtAfterKRequestStep(Get, next_resource). The second one is not applicable to StatefulSet which doesn't have a next resource.
///
/// The proof contains two part: resource_key exists or does not exist at first. The proof of both parts contains several times of applying
/// wf1, handle_get_request => continue_reconcile => handle_create/update_request => continue_reconcile.
pub proof fn lemma_from_after_get_resource_step_to_resource_matches(
    spec: TempPred<FBCCluster>, fbc: FluentBitConfigView, sub_resource: SubResource, next_resource: SubResource
)
    requires
        fbc.well_formed(),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())))),
        spec.entails(always(lift_state(FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(helper_invariants::triggering_cr_satisfies_state_validation()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, fbc).key, fbc)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
    ensures
        spec.entails(
            lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc))
                .leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)))
        ),
        next_resource_get_step_and_request(fbc, sub_resource).0 == after_get_k_request_step(next_resource) ==> spec.entails(
            lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc))
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource, fbc)))
        ),
{
    lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(spec, sub_resource, next_resource, fbc);
    lemma_from_after_get_resource_step_and_key_exists_to_resource_matches(spec, sub_resource, next_resource, fbc);
    let key_not_exists = |s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
    };
    let key_exists = |s: FBCCluster| {
        &&& s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
    };
    or_leads_to_combine(spec, key_not_exists, key_exists, sub_resource_state_matches(sub_resource, fbc));
    temp_pred_equality(
        lift_state(key_not_exists).or(lift_state(key_exists)), lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc))
    );
    if next_resource_get_step_and_request(fbc, sub_resource).0 == after_get_k_request_step(next_resource) {
        or_leads_to_combine(spec, key_not_exists, key_exists, pending_req_in_flight_at_after_get_resource_step(next_resource, fbc));
    }
}

proof fn lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, next_resource: SubResource, fbc: FluentBitConfigView
)
    requires
        fbc.well_formed(),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(helper_invariants::triggering_cr_satisfies_state_validation()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
    ensures
        spec.entails(
            lift_state(|s: FBCCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
            }).leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)))
        ),
        next_resource_get_step_and_request(fbc, sub_resource).0 == after_get_k_request_step(next_resource) ==> spec.entails(
            lift_state(|s: FBCCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource, fbc)))
        ),
{
    let pre = lift_state(|s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
    });
    let post = lift_state(|s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, fbc)(s)
    });
    let pre_and_req_in_flight = |req_msg| lift_state(
        |s: FBCCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
            &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, fbc, req_msg)(s)
        }
    );
    let pre_and_exists_resp_in_flight = lift_state(
        |s: FBCCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
            &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, fbc)(s)
        }
    );
    let pre_and_resp_in_flight = |resp_msg| lift_state(
        |s: FBCCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
            &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, fbc, resp_msg)(s)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    );
    let post_and_req_in_flight = |req_msg| lift_state(
        |s: FBCCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
            &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, fbc, req_msg)(s)
        }
    );
    assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
    by {
        lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(spec, sub_resource, fbc, req_msg);
    }
    leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
    assert_by(
        tla_exists(pre_and_req_in_flight) == pre,
        {
            assert forall |ex| #[trigger] pre.satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
        }
    );

    assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(post))
    by {
        lemma_from_after_get_resource_step_to_after_create_resource_step(spec, sub_resource, fbc, resp_msg);
    }
    leads_to_exists_intro(spec, pre_and_resp_in_flight, post);
    assert_by(
        tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
        {
            assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
            implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0())
                    &&& resp_msg.content.get_get_response().res.is_Err()
                    &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                };
                assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
        }
    );

    let match_and_ok_resp = lift_state(sub_resource_state_matches(sub_resource, fbc))
    .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)));

    assert forall |req_msg| spec.entails(#[trigger] post_and_req_in_flight(req_msg).leads_to(match_and_ok_resp))
    by {
        lemma_resource_state_matches_at_after_create_resource_step(spec, sub_resource, fbc, req_msg);
    }
    leads_to_exists_intro(spec, post_and_req_in_flight, match_and_ok_resp);
    assert_by(
        tla_exists(post_and_req_in_flight) == post,
        {
            assert forall |ex| #[trigger] post.satisfied_by(ex)
            implies tla_exists(post_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
                assert(post_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(post_and_req_in_flight), post);
        }
    );

    valid_implies_implies_leads_to(spec, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, fbc)));

    leads_to_trans_n!(spec, pre, pre_and_exists_resp_in_flight, post, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, fbc)));

    // We already have the desired state.
    // Now prove the system can successfully enter the next state.
    if next_resource_get_step_and_request(fbc, sub_resource).0 == after_get_k_request_step(next_resource) {
        let known_ok_resp = |resp_msg: FBCMessage| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, fbc, resp_msg));
        let next_state = pending_req_in_flight_at_after_get_resource_step(next_resource, fbc);
        assert forall |resp_msg| spec.entails(#[trigger] known_ok_resp(resp_msg).leads_to(lift_state(next_state))) by {
            let pre = resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, fbc, resp_msg);
            let stronger_next = |s, s_prime: FBCCluster| {
                &&& FBCCluster::next()(s, s_prime)
                &&& FBCCluster::crash_disabled()(s)
                &&& FBCCluster::busy_disabled()(s)
                &&& FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())(s)
                &&& FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())(s)
            };

            combine_spec_entails_always_n!(
                spec, lift_action(stronger_next),
                lift_action(FBCCluster::next()),
                lift_state(FBCCluster::crash_disabled()),
                lift_state(FBCCluster::busy_disabled()),
                lift_state(FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())),
                lift_state(FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref()))
            );

            assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || next_state(s_prime) by {
                let step = choose |step| FBCCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        if input.1.is_Some() && input.1.get_Some_0() == fbc.object_ref() {
                            // assert(input)
                            assert(s_prime.ongoing_reconciles()[fbc.object_ref()].local_state.reconcile_step == after_get_k_request_step(next_resource));
                            assert(next_state(s_prime));
                        } else {
                            assert(pre(s_prime));
                        }
                    }
                    _ => {
                        assert(pre(s_prime));
                    }
                }
            }
            FBCCluster::lemma_pre_leads_to_post_by_controller(
                spec, (Some(resp_msg), Some(fbc.object_ref())), stronger_next, FBCCluster::continue_reconcile(), pre, next_state
            );
        }
        leads_to_exists_intro(spec, known_ok_resp, lift_state(next_state));
        let exists_ok_resp = lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc));
        assert_by(
            tla_exists(known_ok_resp) == exists_ok_resp,
            {
                assert forall |ex| #[trigger] exists_ok_resp.satisfied_by(ex) implies tla_exists(known_ok_resp).satisfied_by(ex) by {
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0())
                        &&& resp_msg.content.get_create_response().res.is_Ok()
                        &&& state_after_create_or_update(sub_resource, resp_msg.content.get_create_response().res.get_Ok_0(), ex.head().ongoing_reconciles()[fbc.object_ref()].local_state).is_Ok()
                    };
                    assert(known_ok_resp(resp_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(known_ok_resp), exists_ok_resp);
            }
        );
        valid_implies_implies_leads_to(spec, match_and_ok_resp, exists_ok_resp);
        leads_to_trans_n!(spec, pre, match_and_ok_resp, exists_ok_resp, lift_state(next_state));
    }
}

proof fn lemma_from_after_get_resource_step_and_key_exists_to_resource_matches(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, next_resource: SubResource, fbc: FluentBitConfigView
)
    requires
        fbc.well_formed(),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())))),
        spec.entails(always(lift_state(FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::triggering_cr_satisfies_state_validation()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, fbc).key, fbc)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc)))),
    ensures
        spec.entails(
            lift_state(|s: FBCCluster| {
                &&& s.resources().contains_key(get_request(sub_resource, fbc).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
            }).leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)))
        ),
        next_resource_get_step_and_request(fbc, sub_resource).0 == after_get_k_request_step(next_resource) ==> spec.entails(
            lift_state(|s: FBCCluster| {
                &&& s.resources().contains_key(get_request(sub_resource, fbc).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource, fbc)))
        ),
{
    let resource_key = get_request(sub_resource, fbc).key;
    let pre = lift_state(|s: FBCCluster| {
        &&& s.resources().contains_key(resource_key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
    });
    let post = pending_req_in_flight_at_after_update_resource_step(sub_resource, fbc);
    let match_and_ok_resp = lift_state(sub_resource_state_matches(sub_resource, fbc))
        .and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)));
    assert_by(
        spec.entails(pre.leads_to(match_and_ok_resp)),
        {
            let pre_and_req_in_flight = |req_msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, fbc, req_msg));

            assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc))))
            by {
                lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(spec, sub_resource, fbc, req_msg);
            }
            leads_to_exists_intro(spec, pre_and_req_in_flight, lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)));
            assert_by(
                tla_exists(pre_and_req_in_flight) == pre,
                {
                    assert forall |ex| #[trigger] pre.satisfied_by(ex)
                    implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                        let req_msg = ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
                        assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
                }
            );

            let pre_and_resp_in_flight = |resp_msg| lift_state(
                |s: FBCCluster| {
                    &&& s.resources().contains_key(resource_key)
                    &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, fbc, resp_msg)(s)
                    &&& resp_msg.content.get_get_response().res.is_Ok()
                    &&& resp_msg.content.get_get_response().res.get_Ok_0() == s.resources()[resource_key]
                }
            );

            assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(lift_state(post)))
            by {
                lemma_from_after_get_resource_step_to_after_update_resource_step(spec, sub_resource, fbc, resp_msg);
                temp_pred_equality(
                    pre_and_resp_in_flight(resp_msg), lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, fbc, resp_msg))
                );
            }
            leads_to_exists_intro(spec, pre_and_resp_in_flight, lift_state(post));
            assert_by(
                tla_exists(pre_and_resp_in_flight) == lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)),
                {
                    assert forall |ex| #[trigger] lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)).satisfied_by(ex)
                    implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                        let resp_msg = choose |resp_msg| {
                            &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                            &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0())
                            &&& resp_msg.content.get_get_response().res.is_Ok()
                            &&& resp_msg.content.get_get_response().res.get_Ok_0() == ex.head().resources()[resource_key]
                        };
                        assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_resp_in_flight), lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)));
                }
            );

            let pre_and_req_in_flight = |req_msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, fbc, req_msg));

            assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(match_and_ok_resp)) by {
                lemma_resource_state_matches_at_after_update_resource_step(spec, sub_resource, fbc, req_msg);
            }
            leads_to_exists_intro(spec, pre_and_req_in_flight, match_and_ok_resp);
            assert_by(
                tla_exists(pre_and_req_in_flight) == lift_state(post),
                {
                    assert forall |ex| #[trigger] lift_state(post).satisfied_by(ex)
                    implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                        let req_msg = ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
                        assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_req_in_flight), lift_state(post));
                }
            );

            leads_to_trans_n!(
                spec, pre, lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)),
                lift_state(post), match_and_ok_resp
            );
        }
    );

    valid_implies_implies_leads_to(spec, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, fbc)));

    leads_to_trans_n!(spec, pre, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, fbc)));

    // We already have the desired state.
    // Now prove the system can successfully enter the next state.
    if next_resource_get_step_and_request(fbc, sub_resource).0 == after_get_k_request_step(next_resource) {
        let known_ok_resp = |resp_msg: FBCMessage| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, fbc, resp_msg));
        let next_state = pending_req_in_flight_at_after_get_resource_step(next_resource, fbc);
        assert forall |resp_msg| spec.entails(#[trigger] known_ok_resp(resp_msg).leads_to(lift_state(next_state))) by {
            let pre = resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, fbc, resp_msg);
            let stronger_next = |s, s_prime: FBCCluster| {
                &&& FBCCluster::next()(s, s_prime)
                &&& FBCCluster::crash_disabled()(s)
                &&& FBCCluster::busy_disabled()(s)
                &&& FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())(s)
                &&& FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())(s)
            };

            combine_spec_entails_always_n!(
                spec, lift_action(stronger_next),
                lift_action(FBCCluster::next()),
                lift_state(FBCCluster::crash_disabled()),
                lift_state(FBCCluster::busy_disabled()),
                lift_state(FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())),
                lift_state(FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref()))
            );

            assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || next_state(s_prime) by {
                let step = choose |step| FBCCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        if input.1.is_Some() && input.1.get_Some_0() == fbc.object_ref() {
                            // assert(input)
                            assert(s_prime.ongoing_reconciles()[fbc.object_ref()].local_state.reconcile_step == after_get_k_request_step(next_resource));
                            assert(next_state(s_prime));
                        } else {
                            assert(pre(s_prime));
                        }
                    }
                    _ => {
                        assert(pre(s_prime));
                    }
                }
            }
            FBCCluster::lemma_pre_leads_to_post_by_controller(
                spec, (Some(resp_msg), Some(fbc.object_ref())), stronger_next, FBCCluster::continue_reconcile(), pre, next_state
            );
        }
        leads_to_exists_intro(spec, known_ok_resp, lift_state(next_state));
        let exists_ok_resp = lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc));
        assert_by(
            tla_exists(known_ok_resp) == exists_ok_resp,
            {
                assert forall |ex| #[trigger] exists_ok_resp.satisfied_by(ex) implies tla_exists(known_ok_resp).satisfied_by(ex) by {
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0())
                        &&& resp_msg.content.get_update_response().res.is_Ok()
                        &&& state_after_create_or_update(sub_resource, resp_msg.content.get_update_response().res.get_Ok_0(), ex.head().ongoing_reconciles()[fbc.object_ref()].local_state).is_Ok()
                    };
                    assert(known_ok_resp(resp_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(known_ok_resp), exists_ok_resp);
            }
        );
        valid_implies_implies_leads_to(spec, match_and_ok_resp, exists_ok_resp);
        leads_to_trans_n!(spec, pre, match_and_ok_resp, exists_ok_resp, lift_state(next_state));
    }
}

proof fn lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, req_msg: FBCMessage
)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
        fbc.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: FBCCluster| {
                    &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
                    &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, fbc, req_msg)(s)
                }
            ).leads_to(lift_state(
                |s: FBCCluster| {
                    &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
                    &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, fbc)(s)
                }
            ))
        ),
{
    let pre = |s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, fbc, req_msg)(s)
    };
    let post = |s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, fbc)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
        &&& FBCCluster::busy_disabled()(s)
        &&& FBCCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| FBCCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = FBCCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Err()
                        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                    });
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && FBCCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = FBCCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        });
    }

    FBCCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, FBCCluster::handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_resource_step_to_after_create_resource_step(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, resp_msg: FBCMessage
)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
        fbc.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: FBCCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
                &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, fbc, resp_msg)(s)
                &&& resp_msg.content.get_get_response().res.is_Err()
                &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
            }).leads_to(lift_state(|s: FBCCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
                &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, fbc)(s)
            }))
        ),
{
    let pre = |s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, fbc, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res.is_Err()
        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
    };
    let post = |s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, fbc)(s)
    };
    let input = (Some(resp_msg), Some(fbc.object_ref()));
    let stronger_next = |s, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
        &&& FBCCluster::every_in_flight_msg_has_unique_id()(s)
        &&& FBCCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())(s)
        &&& FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed()),
        lift_state(FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())),
        lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc))
    );

    FBCCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next, FBCCluster::continue_reconcile(), pre, post
    );
}

proof fn lemma_resource_state_matches_at_after_create_resource_step(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, req_msg: FBCMessage
)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::triggering_cr_satisfies_state_validation()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
        fbc.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: FBCCluster| {
                    &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
                    &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, fbc, req_msg)(s)
                }
            ).leads_to(
                lift_state(sub_resource_state_matches(sub_resource, fbc))
                .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)))
            )
        ),
{
    let pre = |s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, fbc, req_msg)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
        &&& FBCCluster::busy_disabled()(s)
        &&& FBCCluster::every_in_flight_msg_has_unique_id()(s)
        &&& FBCCluster::each_object_in_etcd_is_well_formed()(s)
        &&& helper_invariants::triggering_cr_satisfies_state_validation()(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::triggering_cr_satisfies_state_validation()),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc))
    );

    let post = |s: FBCCluster| {
        &&& sub_resource_state_matches(sub_resource, fbc)(s)
        &&& at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)(s)
    };

    assert forall |s, s_prime: FBCCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && FBCCluster::kubernetes_api_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let pending_msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
        let resp = FBCCluster::handle_create_request(pending_msg, s.kubernetes_api_state).1;
        assert(s_prime.in_flight().contains(resp));
        match sub_resource {
            SubResource::Secret => SecretView::marshal_preserves_integrity(),
        }
    }

    FBCCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, FBCCluster::handle_request(), pre, post
    );
    temp_pred_equality(lift_state(post), lift_state(sub_resource_state_matches(sub_resource, fbc))
    .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc))));
}

proof fn lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, req_msg: FBCMessage
)
    requires
        fbc.well_formed(),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, fbc, req_msg))
            .leads_to(lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, fbc, req_msg);
    let post = at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc);
    let resource_key = get_request(sub_resource, fbc).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
        &&& FBCCluster::busy_disabled()(s)
        &&& FBCCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)(s)
        &&& helper_invariants::no_delete_request_msg_in_flight_with_key(resource_key)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_with_key(resource_key)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)),
        lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(resource_key)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(resource_key))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| FBCCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = FBCCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res.is_Ok()
                        &&& resp_msg.content.get_get_response().res.get_Ok_0() == s_prime.resources()[resource_key]
                    });
                    assert(post(s_prime));
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && FBCCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = FBCCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == s_prime.resources()[resource_key]
        });
    }

    FBCCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, FBCCluster::handle_request(), pre, post
    );
}

proof fn lemma_resource_state_matches_at_after_update_resource_step(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, req_msg: FBCMessage
)
    requires
        fbc.well_formed(),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::triggering_cr_satisfies_state_validation()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc)))),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, fbc, req_msg))
            .leads_to(
                lift_state(sub_resource_state_matches(sub_resource, fbc))
                .and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)))
            )
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, fbc, req_msg);
    let resource_key = get_request(sub_resource, fbc).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
        &&& FBCCluster::busy_disabled()(s)
        &&& FBCCluster::every_in_flight_msg_has_unique_id()(s)
        &&& FBCCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::triggering_cr_satisfies_state_validation()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)(s)
        &&& helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)(s)
        &&& helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::triggering_cr_satisfies_state_validation()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)),
        lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)),
        lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc))
    );

    let post = |s: FBCCluster| {
        &&& sub_resource_state_matches(sub_resource, fbc)(s)
        &&& at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)(s)
    };

    assert forall |s, s_prime: FBCCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && FBCCluster::kubernetes_api_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let pending_msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
        let resp = FBCCluster::handle_update_request(pending_msg, s.kubernetes_api_state).1;
        assert(s_prime.in_flight().contains(resp));
        match sub_resource {
            SubResource::Secret => SecretView::marshal_preserves_integrity(),
        }
    }

    FBCCluster::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, FBCCluster::handle_request(), pre, post);
    temp_pred_equality(lift_state(post), lift_state(sub_resource_state_matches(sub_resource, fbc))
    .and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc))));
}

proof fn lemma_from_after_get_resource_step_to_after_update_resource_step(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, resp_msg: FBCMessage
)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())))),
        spec.entails(always(lift_state(FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, fbc).key, fbc)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc)))),
        fbc.well_formed(),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, fbc, resp_msg))
            .leads_to(lift_state(pending_req_in_flight_at_after_update_resource_step(sub_resource, fbc)))
        ),
{
    let pre = resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, fbc, resp_msg);
    let post = pending_req_in_flight_at_after_update_resource_step(sub_resource, fbc);
    let input = (Some(resp_msg), Some(fbc.object_ref()));
    let stronger_next = |s, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
        &&& FBCCluster::busy_disabled()(s)
        &&& FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())(s)
        &&& FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())(s)
        &&& FBCCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)(s)
        &&& helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc)(s)
        &&& helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, fbc).key, fbc)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::each_resp_matches_at_most_one_pending_req(fbc.object_ref())),
        lift_state(FBCCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(fbc.object_ref())),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)),
        lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc)),
        lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, fbc).key, fbc))
    );

    FBCCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        FBCCluster::continue_reconcile(), pre, post
    );
}

pub proof fn lemma_resource_object_is_stable(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, p: TempPred<FBCCluster>
)
    requires
        spec.entails(p.leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)))),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc)))),
    ensures
        spec.entails(p.leads_to(always(lift_state(sub_resource_state_matches(sub_resource, fbc))))),
{
    let post = sub_resource_state_matches(sub_resource, fbc);
    let resource_key = get_request(sub_resource, fbc).key;
    let stronger_next = |s, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)(s)
        &&& helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, fbc).key)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)),
        lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, fbc).key, fbc)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, fbc))
    );

    assert forall |s, s_prime: FBCCluster| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        match sub_resource {
            SubResource::Secret => SecretView::marshal_preserves_integrity(),
        }
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), p, lift_state(post));
}

}
