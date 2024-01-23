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
use crate::rabbitmq_controller::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants,
        liveness::{resource_match::*, spec::assumption_and_invariants_of_all_phases},
        predicate::*,
        resource::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{prelude::*, string::*};

verus! {

pub proof fn lemma_from_after_get_stateful_set_step_to_stateful_set_matches(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)))),
    ensures spec.entails(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq)).leads_to(lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)))),
{
    let next_res = next_resource_after(SubResource::StatefulSet).get_AfterKRequestStep_1();
    lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(spec, SubResource::StatefulSet, next_res, rabbitmq);
    lemma_from_after_get_stateful_set_step_and_key_exists_to_stateful_set_matches(spec, rabbitmq);
    let key_not_exists = lift_state(|s: RMQCluster| {
        &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq)(s)
    });
    let key_exists = lift_state(|s: RMQCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq)(s)
    });
    or_leads_to_combine_temp(spec, key_not_exists, key_exists, lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)));
    temp_pred_equality(
        key_not_exists.or(key_exists), lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq))
    );
}

proof fn lemma_from_after_get_stateful_set_step_and_key_exists_to_stateful_set_matches(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)))),
    ensures
        spec.entails(lift_state(|s: RMQCluster| {
            &&& s.resources().contains_key(get_request(SubResource::StatefulSet, rabbitmq).key)
            &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq)(s)
        }).leads_to(lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)))),
{
    let sts_key = get_request(SubResource::StatefulSet, rabbitmq).key;
    let pre = lift_state(|s: RMQCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq)(s)
    });
    let stateful_set_matches = lift_state(|s: RMQCluster| {
        &&& s.resources().contains_key(sts_key)
        &&& sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq)(s)
    });
    let stateful_set_not_matches = lift_state(|s: RMQCluster| {
        &&& s.resources().contains_key(sts_key)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq)(s)
    });
    let post = lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq));

    assert_by(spec.entails(stateful_set_matches.leads_to(post)), {
        valid_implies_implies_leads_to(spec, stateful_set_matches, post);
    });

    assert_by(spec.entails(stateful_set_not_matches.leads_to(post)), {
        let pre1 = |req_msg| lift_state(|s: RMQCluster| {
            &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(SubResource::StatefulSet, rabbitmq, req_msg)(s)
            &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
        });
        let post1 = lift_state(|s: RMQCluster| {
            &&& at_after_get_resource_step_and_exists_ok_resp_in_flight(SubResource::StatefulSet, rabbitmq)(s)
            &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
        });
        assert forall |req_msg| spec.entails(#[trigger] pre1(req_msg).leads_to(post1)) by {
            lemma_from_key_exists_to_receives_ok_resp_at_after_get_stateful_set_step(spec, rabbitmq, req_msg);
        }
        leads_to_exists_intro(spec, pre1, post1);
        assert_by(tla_exists(pre1) == stateful_set_not_matches, {
            assert forall |ex| #[trigger] stateful_set_not_matches.satisfied_by(ex)
            implies tla_exists(pre1).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
                assert(pre1(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre1), stateful_set_not_matches);
        });

        let pre2 = |resp_msg| lift_state(|s: RMQCluster| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq, resp_msg)(s)
            &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
        });
        let post2 = lift_state(|s: RMQCluster| {
            &&& pending_req_in_flight_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)(s)
            &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
        });
        assert forall |resp_msg| spec.entails(#[trigger] pre2(resp_msg).leads_to(post2)) by {
            lemma_from_after_get_stateful_set_step_to_after_update_stateful_set_step(spec, rabbitmq, resp_msg);
        }
        leads_to_exists_intro(spec, pre2, post2);
        assert_by(tla_exists(pre2) == post1, {
            assert forall |ex| #[trigger] post1.satisfied_by(ex)
            implies tla_exists(pre2).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
                    &&& resp_msg.content.get_get_response().res.is_Ok()
                    &&& resp_msg.content.get_get_response().res.get_Ok_0() == ex.head().resources()[sts_key]
                };
                assert(pre2(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre2), post1);
        });

        let pre3 = |req_msg| lift_state(|s: RMQCluster| {
            &&& req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq, req_msg)(s)
            &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
        });
        assert forall |req_msg| spec.entails(#[trigger] pre3(req_msg).leads_to(post)) by {
            lemma_stateful_set_state_matches_at_after_update_stateful_set_step(spec, rabbitmq, req_msg);
        }
        leads_to_exists_intro(spec, pre3, post);
        assert_by(tla_exists(pre3) == post2, {
            assert forall |ex| #[trigger] post2.satisfied_by(ex)
            implies tla_exists(pre3).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
                assert(pre3(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre3), post2);
        });

        leads_to_trans_n!(spec, stateful_set_not_matches, post1, post2, post);
    });

    or_leads_to_combine_temp(spec, stateful_set_matches, stateful_set_not_matches, post);
    temp_pred_equality(stateful_set_matches.or(stateful_set_not_matches), pre);
}

#[verifier(spinoff_prover)]
proof fn lemma_from_key_exists_to_receives_ok_resp_at_after_get_stateful_set_step(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(rabbitmq)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)))),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| {
                &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(SubResource::StatefulSet, rabbitmq, req_msg)(s)
                &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
            })
            .leads_to(lift_state(|s: RMQCluster| {
                &&& at_after_get_resource_step_and_exists_ok_resp_in_flight(SubResource::StatefulSet, rabbitmq)(s)
                &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
            }))
        ),
{
    let pre = |s: RMQCluster| {
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(SubResource::StatefulSet, rabbitmq, req_msg)(s)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
    };
    let post = |s: RMQCluster| {
        &&& at_after_get_resource_step_and_exists_ok_resp_in_flight(SubResource::StatefulSet, rabbitmq)(s)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
    };
    let resource_key = get_request(SubResource::StatefulSet, rabbitmq).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(rabbitmq)(s)
        &&& helper_invariants::cm_rv_stays_unchanged(rabbitmq)(s, s_prime)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(rabbitmq)),
        lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                assert(!resource_delete_request_msg(resource_key)(req));
                assert(!resource_update_request_msg(resource_key)(req));
                assert(!resource_update_status_request_msg(resource_key)(req));
                if req == req_msg {
                    let resp_msg = RMQCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
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

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = RMQCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == s_prime.resources()[resource_key]
        });
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, RMQCluster::handle_request(), pre, post
    );
}

#[verifier(spinoff_prover)]
proof fn lemma_from_after_get_stateful_set_step_to_after_update_stateful_set_step(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, resp_msg: RMQMessage
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)))),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| {
                &&& resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq, resp_msg)(s)
                &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
            })
            .leads_to(lift_state(|s: RMQCluster| {
                &&& pending_req_in_flight_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)(s)
                &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
            }))
        ),
{
    let pre = |s: RMQCluster| {
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(SubResource::StatefulSet, rabbitmq, resp_msg)(s)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
    };
    let post = |s: RMQCluster| {
        &&& pending_req_in_flight_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)(s)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
    };
    let input = (Some(resp_msg), Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::desired_state_is(rabbitmq)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(rabbitmq)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
        &&& helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)(s)
        &&& helper_invariants::cm_rv_stays_unchanged(rabbitmq)(s, s_prime)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(rabbitmq)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)),
        lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)),
        lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq))
    );

    assert forall |s, s_prime: RMQCluster| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        let resource_key = get_request(SubResource::StatefulSet, rabbitmq).key;
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                assert(!resource_delete_request_msg(resource_key)(req));
                assert(!resource_update_request_msg(resource_key)(req));
                assert(!resource_update_status_request_msg(resource_key)(req));
            },
            _ => {}
        }
    }
    RMQCluster::lemma_pre_leads_to_post_by_controller(spec, input, stronger_next, RMQCluster::continue_reconcile(), pre, post);
}

#[verifier(spinoff_prover)]
proof fn lemma_stateful_set_state_matches_at_after_update_stateful_set_step(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)))),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| {
                &&& req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq, req_msg)(s)
                &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
            })
            .leads_to(lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)))
        ),
{
    let pre = |s: RMQCluster| {
        &&& req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq, req_msg)(s)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)(s)
    };
    let post = sub_resource_state_matches(SubResource::StatefulSet, rabbitmq);

    let resource_key = get_request(SubResource::StatefulSet, rabbitmq).key;
    let resource_well_formed = |s: RMQCluster| {
        s.resources().contains_key(resource_key)
        ==> RMQCluster::etcd_object_is_well_formed(resource_key)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& resource_well_formed(s)
        &&& RMQCluster::desired_state_is(rabbitmq)(s)
        &&& helper_invariants::the_object_in_reconcile_satisfies_state_validation(rabbitmq.object_ref())(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(rabbitmq)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
        &&& helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)(s)
    };
    always_weaken_temp(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()), lift_state(resource_well_formed));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(resource_well_formed),
        lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(rabbitmq.object_ref())),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(rabbitmq)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)),
        lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq))
    );

    assert forall |s, s_prime: RMQCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let pending_msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let resp = RMQCluster::handle_update_request_msg(pending_msg, s.kubernetes_api_state).1;
        assert(s_prime.in_flight().contains(resp));
        StatefulSetView::marshal_preserves_integrity();
    }

    assert forall |s, s_prime: RMQCluster| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                assert(!resource_delete_request_msg(resource_key)(req));
                assert(!resource_update_status_request_msg(resource_key)(req));
                if resource_update_request_msg(resource_key)(req) {} else {}
            },
            _ => {}
        }
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, RMQCluster::handle_request(), pre, post);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_stateful_set_is_stable(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, p: TempPred<RMQCluster>)
    requires
        spec.entails(p.leads_to(lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)))),
    ensures spec.entails(p.leads_to(always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, rabbitmq))))),
{
    let post = sub_resource_state_matches(SubResource::StatefulSet, rabbitmq);
    let resource_key = get_request(SubResource::StatefulSet, rabbitmq).key;
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
        &&& helper_invariants::cm_rv_stays_unchanged(rabbitmq)(s, s_prime)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)),
        lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq))
    );

    assert forall |s, s_prime: RMQCluster| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        StatefulSetView::marshal_preserves_integrity();
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                assert(!resource_delete_request_msg(resource_key)(req));
                if resource_update_request_msg(resource_key)(req) {} else {}
            },
            _ => {}
        }
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), p, lift_state(post));
}

}
