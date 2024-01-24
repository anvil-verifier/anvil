// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit_config::{
    model::{reconciler::*, resource::*},
    proof::{helper_invariants, predicate::*, resource::*},
    trusted::{spec_types::*, step::*},
};
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
use vstd::{prelude::*, string::*};

verus! {

pub proof fn lemma_from_after_get_resource_step_to_resource_matches(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView, sub_resource: SubResource)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)))),
    ensures spec.entails(lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)).leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)))),
{
    lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(spec, sub_resource, fbc);
    lemma_from_after_get_resource_step_and_key_exists_to_resource_matches(spec, sub_resource, fbc);
    let key_not_exists = lift_state(|s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
    });
    let key_exists = lift_state(|s: FBCCluster| {
        &&& s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
    });
    or_leads_to_combine_temp(spec, key_not_exists, key_exists, lift_state(sub_resource_state_matches(sub_resource, fbc)));
    temp_pred_equality(
        key_not_exists.or(key_exists), lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc))
    );
}

pub proof fn lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
    ensures
        spec.entails(lift_state(|s: FBCCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
            &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
        }).leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)))),
{
    let pre = lift_state(|s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
    });
    let post = lift_state(|s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, fbc)(s)
    });
    let pre_and_req_in_flight = |req_msg| lift_state(|s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, fbc, req_msg)(s)
    });
    let pre_and_exists_resp_in_flight = lift_state(|s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, fbc)(s)
    });
    let pre_and_resp_in_flight = |resp_msg| lift_state(|s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, fbc, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res.is_Err()
        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
    });
    let post_and_req_in_flight = |req_msg| lift_state(|s: FBCCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, fbc, req_msg)(s)
    });
    let match_and_ok_resp = lift_state(sub_resource_state_matches(sub_resource, fbc))
        .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)));

    assert_by(spec.entails(pre.leads_to(match_and_ok_resp)), {
        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight)) by {
            lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(spec, sub_resource, fbc, req_msg);
        }
        leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
        assert_by(tla_exists(pre_and_req_in_flight) == pre, {
            assert forall |ex| #[trigger] pre.satisfied_by(ex) implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
        });

        assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(post)) by {
            lemma_from_after_get_resource_step_to_after_create_resource_step(spec, sub_resource, fbc, resp_msg);
        }
        leads_to_exists_intro(spec, pre_and_resp_in_flight, post);
        assert_by(tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight, {
            assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex) implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0())
                    &&& resp_msg.content.get_get_response().res.is_Err()
                    &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                };
                assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
        });

        assert forall |req_msg| spec.entails(#[trigger] post_and_req_in_flight(req_msg).leads_to(match_and_ok_resp)) by {
            lemma_resource_state_matches_at_after_create_resource_step(spec, sub_resource, fbc, req_msg);
        }
        leads_to_exists_intro(spec, post_and_req_in_flight, match_and_ok_resp);
        assert_by(tla_exists(post_and_req_in_flight) == post, {
            assert forall |ex| #[trigger] post.satisfied_by(ex) implies tla_exists(post_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
                assert(post_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(post_and_req_in_flight), post);
        });
        leads_to_trans_n!(spec, pre, pre_and_exists_resp_in_flight, post, match_and_ok_resp);
    });

    assert_by(spec.entails(pre.leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)))), {
        valid_implies_implies_leads_to(spec, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, fbc)));
        leads_to_trans_n!(spec, pre, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, fbc)));
    });
}

proof fn lemma_from_after_get_resource_step_and_key_exists_to_resource_matches(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView
)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)))),
    ensures
        spec.entails(lift_state(|s: FBCCluster| {
            &&& s.resources().contains_key(get_request(sub_resource, fbc).key)
            &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
        }).leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)))),
{
    let resource_key = get_request(sub_resource, fbc).key;
    let pre = lift_state(|s: FBCCluster| {
        &&& s.resources().contains_key(resource_key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, fbc)(s)
    });
    let post = pending_req_in_flight_at_after_update_resource_step(sub_resource, fbc);
    let match_and_ok_resp = lift_state(sub_resource_state_matches(sub_resource, fbc)).and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)));
    assert_by(spec.entails(pre.leads_to(match_and_ok_resp)), {
        let pre_and_req_in_flight = |req_msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, fbc, req_msg));
        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc))))
        by {
            lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(spec, sub_resource, fbc, req_msg);
        }
        leads_to_exists_intro(spec, pre_and_req_in_flight, lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)));
        assert_by(tla_exists(pre_and_req_in_flight) == pre, {
            assert forall |ex| #[trigger] pre.satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
        });
        let pre_and_resp_in_flight = |resp_msg| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, fbc, resp_msg));
        assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(lift_state(post)))
        by {
            lemma_from_after_get_resource_step_to_after_update_resource_step(spec, sub_resource, fbc, resp_msg);
        }
        leads_to_exists_intro(spec, pre_and_resp_in_flight, lift_state(post));
        assert_by(tla_exists(pre_and_resp_in_flight) == lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)), {
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
        });
        let pre_and_req_in_flight = |req_msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, fbc, req_msg));
        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(match_and_ok_resp)) by {
            lemma_resource_state_matches_at_after_update_resource_step(spec, sub_resource, fbc, req_msg);
        }
        leads_to_exists_intro(spec, pre_and_req_in_flight, match_and_ok_resp);
        assert_by(tla_exists(pre_and_req_in_flight) == lift_state(post), {
            assert forall |ex| #[trigger] lift_state(post).satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), lift_state(post));
        });
        leads_to_trans_n!(
            spec, pre, lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)),
            lift_state(post), match_and_ok_resp
        );
    });

    assert_by(spec.entails(pre.leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)))), {
        valid_implies_implies_leads_to(spec, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, fbc)));
        leads_to_trans_n!(spec, pre, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, fbc)));
    });
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
    ensures
        spec.entails(lift_state(|s: FBCCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
            &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, fbc, req_msg)(s)
        }).leads_to(lift_state(|s: FBCCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
            &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, fbc)(s)
        }))),
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
            Step::ApiServerStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = FBCCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
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
        let resp_msg = FBCCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
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

#[verifier(spinoff_prover)]
proof fn lemma_from_after_get_resource_step_to_after_create_resource_step(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, resp_msg: FBCMessage)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
    ensures
        spec.entails(lift_state(|s: FBCCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
            &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, fbc, resp_msg)(s)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }).leads_to(lift_state(|s: FBCCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
            &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, fbc)(s)
        }))),
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
        &&& FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc))
    );

    FBCCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next, FBCCluster::continue_reconcile(), pre, post
    );
}

proof fn lemma_resource_state_matches_at_after_create_resource_step(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, req_msg: FBCMessage)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
    ensures
        spec.entails(lift_state(|s: FBCCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, fbc).key)
            &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, fbc, req_msg)(s)
        }).leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)).and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc))))),
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
        &&& helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref())(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref())),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc))
    );

    let post = |s: FBCCluster| {
        &&& sub_resource_state_matches(sub_resource, fbc)(s)
        &&& at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)(s)
    };

    assert forall |s, s_prime: FBCCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && FBCCluster::kubernetes_api_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let pending_msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
        let resp = FBCCluster::handle_create_request_msg(pending_msg, s.kubernetes_api_state).1;
        assert(s_prime.in_flight().contains(resp));
        match sub_resource {
            SubResource::Secret => SecretView::marshal_preserves_integrity(),
        }
    }

    FBCCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, FBCCluster::handle_request(), pre, post
    );
    temp_pred_equality(
        lift_state(post),
        lift_state(sub_resource_state_matches(sub_resource, fbc))
            .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)))
    );
}

proof fn lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, req_msg: FBCMessage)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)))),
    ensures
        spec.entails(lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, fbc, req_msg))
            .leads_to(lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)))),
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
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| FBCCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = FBCCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
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
        let resp_msg = FBCCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
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

proof fn lemma_resource_state_matches_at_after_update_resource_step(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, req_msg: FBCMessage)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)))),
    ensures
        spec.entails(lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, fbc, req_msg))
            .leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)).and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc))))),
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
        &&& helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref())(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(fbc.object_ref())),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc))
    );

    let post = |s: FBCCluster| {
        &&& sub_resource_state_matches(sub_resource, fbc)(s)
        &&& at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)(s)
    };

    assert forall |s, s_prime: FBCCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && FBCCluster::kubernetes_api_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let pending_msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg.get_Some_0();
        let resp = FBCCluster::handle_update_request_msg(pending_msg, s.kubernetes_api_state).1;
        assert(s_prime.in_flight().contains(resp));
        match sub_resource {
            SubResource::Secret => SecretView::marshal_preserves_integrity(),
        }
    }

    FBCCluster::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, FBCCluster::handle_request(), pre, post);
    temp_pred_equality(
        lift_state(post),
        lift_state(sub_resource_state_matches(sub_resource, fbc))
            .and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, fbc)))
    );
}

proof fn lemma_from_after_get_resource_step_to_after_update_resource_step(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, resp_msg: FBCMessage
)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)))),
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
        &&& FBCCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCCluster::every_in_flight_msg_has_unique_id()(s)
        &&& FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::crash_disabled()),
        lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::pending_req_of_key_is_unique_with_unique_id(fbc.object_ref())),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc))
    );

    FBCCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, FBCCluster::continue_reconcile(), pre, post);
}

pub proof fn lemma_resource_object_is_stable(
    spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView, p: TempPred<FBCCluster>
)
    requires
        spec.entails(p.leads_to(lift_state(sub_resource_state_matches(sub_resource, fbc)))),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)))),
    ensures
        spec.entails(p.leads_to(always(lift_state(sub_resource_state_matches(sub_resource, fbc))))),
{
    let post = sub_resource_state_matches(sub_resource, fbc);
    let resource_key = get_request(sub_resource, fbc).key;
    let stronger_next = |s, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, fbc)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight(sub_resource, fbc)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc))
    );

    assert forall |s, s_prime: FBCCluster| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        match sub_resource {
            SubResource::Secret => SecretView::marshal_preserves_integrity(),
        }
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), p, lift_state(post));
}

}
