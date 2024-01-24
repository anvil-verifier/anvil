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
use crate::zookeeper_controller::{
    model::{reconciler::*, resource::*},
    proof::{helper_invariants, liveness::resource_match::*, predicate::*, resource::*},
    trusted::{spec_types::*, step::*},
};
use vstd::{prelude::*, string::*};

verus! {

pub proof fn lemma_from_after_get_stateful_set_step_to_stateful_set_matches(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(zookeeper)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(zookeeper)))),
    ensures spec.entails(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)).leads_to(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper)))),
{
    lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(spec, SubResource::StatefulSet, zookeeper);
    lemma_from_after_get_stateful_set_step_and_key_exists_to_stateful_set_matches(spec, zookeeper);
    let key_not_exists = lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)(s)
    });
    let key_exists = lift_state(|s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)(s)
    });
    or_leads_to_combine_temp(spec, key_not_exists, key_exists, lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper)));
    temp_pred_equality(
        key_not_exists.or(key_exists), lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper))
    );
}

proof fn lemma_from_after_get_stateful_set_step_and_key_exists_to_stateful_set_matches(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(zookeeper)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
                &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)(s)
            }).leads_to(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper)))
        ),
{
    let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
    let pre = lift_state(|s: ZKCluster| {
        &&& s.resources().contains_key(get_request(SubResource::StatefulSet, zookeeper).key)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)(s)
    });
    let stateful_set_matches = lift_state(|s: ZKCluster| {
        &&& s.resources().contains_key(sts_key)
        &&& sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)(s)
    });
    let stateful_set_not_matches = lift_state(|s: ZKCluster| {
        &&& s.resources().contains_key(sts_key)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::StatefulSet, zookeeper)(s)
    });
    let post = lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper));

    assert_by(spec.entails(stateful_set_matches.leads_to(post)), {
        valid_implies_implies_leads_to(spec, stateful_set_matches, post);
    });

    assert_by(spec.entails(stateful_set_not_matches.leads_to(post)), {
        let pre1 = |req_msg| lift_state(|s: ZKCluster| {
            &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(SubResource::StatefulSet, zookeeper, req_msg)(s)
            &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
        });
        let post1 = lift_state(|s: ZKCluster| {
            &&& at_after_get_resource_step_and_exists_ok_resp_in_flight(SubResource::StatefulSet, zookeeper)(s)
            &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
        });
        assert forall |req_msg| spec.entails(#[trigger] pre1(req_msg).leads_to(post1)) by {
            lemma_from_key_exists_to_receives_ok_resp_at_after_get_stateful_set_step(spec, zookeeper, req_msg);
        }
        leads_to_exists_intro(spec, pre1, post1);
        assert_by(tla_exists(pre1) == stateful_set_not_matches, {
            assert forall |ex| #[trigger] stateful_set_not_matches.satisfied_by(ex)
            implies tla_exists(pre1).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                assert(pre1(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre1), stateful_set_not_matches);
        });

        let pre2 = |resp_msg| lift_state(|s: ZKCluster| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(SubResource::StatefulSet, zookeeper, resp_msg)(s)
            &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
        });
        let post2 = lift_state(|s: ZKCluster| {
            &&& pending_req_in_flight_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
            &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
        });
        assert forall |resp_msg| spec.entails(#[trigger] pre2(resp_msg).leads_to(post2)) by {
            lemma_from_after_get_stateful_set_step_to_after_update_stateful_set_step(spec, zookeeper, resp_msg);
        }
        leads_to_exists_intro(spec, pre2, post2);
        assert_by(tla_exists(pre2) == post1, {
            assert forall |ex| #[trigger] post1.satisfied_by(ex)
            implies tla_exists(pre2).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                    &&& resp_msg.content.get_get_response().res.is_Ok()
                    &&& resp_msg.content.get_get_response().res.get_Ok_0() == ex.head().resources()[sts_key]
                };
                assert(pre2(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre2), post1);
        });

        let pre3 = |req_msg| lift_state(|s: ZKCluster| {
            &&& req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(SubResource::StatefulSet, zookeeper, req_msg)(s)
            &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
        });
        assert forall |req_msg| spec.entails(#[trigger] pre3(req_msg).leads_to(post)) by {
            lemma_stateful_set_state_matches_at_after_update_stateful_set_step(spec, zookeeper, req_msg);
        }
        leads_to_exists_intro(spec, pre3, post);
        assert_by(tla_exists(pre3) == post2, {
            assert forall |ex| #[trigger] post2.satisfied_by(ex)
            implies tla_exists(pre3).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                assert(pre3(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre3), post2);
        });

        leads_to_trans_n!(spec, stateful_set_not_matches, post1, post2, post);
    });

    or_leads_to_combine_temp(spec, stateful_set_matches, stateful_set_not_matches, post);
    temp_pred_equality(stateful_set_matches.or(stateful_set_not_matches), pre);
}

proof fn lemma_from_key_exists_to_receives_ok_resp_at_after_get_stateful_set_step(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, req_msg: ZKMessage
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(SubResource::StatefulSet, zookeeper, req_msg)(s)
                &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
            })
            .leads_to(lift_state(|s: ZKCluster| {
                &&& at_after_get_resource_step_and_exists_ok_resp_in_flight(SubResource::StatefulSet, zookeeper)(s)
                &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
            }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(SubResource::StatefulSet, zookeeper, req_msg)(s)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
    };
    let post = |s: ZKCluster| {
        &&& at_after_get_resource_step_and_exists_ok_resp_in_flight(SubResource::StatefulSet, zookeeper)(s)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
    };
    let resource_key = get_request(SubResource::StatefulSet, zookeeper).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)(s)
        &&& helper_invariants::cm_rv_stays_unchanged(zookeeper)(s, s_prime)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)),
        lift_action(helper_invariants::cm_rv_stays_unchanged(zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                assert(!resource_delete_request_msg(resource_key)(req));
                assert(!resource_update_request_msg(resource_key)(req));
                assert(!resource_update_status_request_msg(resource_key)(req));
                if input.get_Some_0() == req_msg {
                    let resp_msg = ZKCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
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

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == s_prime.resources()[resource_key]
        });
    }

    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, ZKCluster::handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_stateful_set_step_to_after_update_stateful_set_step(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, resp_msg: ZKMessage
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(zookeeper)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(SubResource::StatefulSet, zookeeper, resp_msg)(s)
                &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
            })
            .leads_to(lift_state(|s: ZKCluster| {
                &&& pending_req_in_flight_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
                &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
            }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(SubResource::StatefulSet, zookeeper, resp_msg)(s)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
    };
    let post = |s: ZKCluster| {
        &&& pending_req_in_flight_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
    };
    let input = (Some(resp_msg), Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::desired_state_is(zookeeper)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(zookeeper)(s)
        &&& helper_invariants::cm_rv_stays_unchanged(zookeeper)(s, s_prime)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::desired_state_is(zookeeper)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(zookeeper)),
        lift_action(helper_invariants::cm_rv_stays_unchanged(zookeeper))
    );

    assert forall |s, s_prime: ZKCluster| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        let resource_key = get_request(SubResource::StatefulSet, zookeeper).key;
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
    ZKCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        ZKCluster::continue_reconcile(), pre, post
    );
}

proof fn lemma_stateful_set_state_matches_at_after_update_stateful_set_step(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, req_msg: ZKMessage)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(SubResource::StatefulSet, zookeeper, req_msg)(s)
                &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
            })
            .leads_to(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper)))
        ),
{
    let pre = |s: ZKCluster| {
        &&& req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(SubResource::StatefulSet, zookeeper, req_msg)(s)
        &&& !sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
    };
    let post = sub_resource_state_matches(SubResource::StatefulSet, zookeeper);

    let resource_key = get_request(SubResource::StatefulSet, zookeeper).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::desired_state_is(zookeeper)(s)
        &&& helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
        &&& helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::desired_state_is(zookeeper)),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)),
        lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(zookeeper))
    );

    assert forall |s, s_prime: ZKCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let pending_msg = s.ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
        let resp = ZKCluster::handle_update_request_msg(pending_msg, s.kubernetes_api_state).1;
        assert(s_prime.in_flight().contains(resp));
        StatefulSetView::marshal_preserves_integrity();
    }

    assert forall |s, s_prime: ZKCluster| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
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

    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, ZKCluster::handle_request(), pre, post);
}

pub proof fn lemma_stateful_set_is_stable(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, p: TempPred<ZKCluster>
)
    requires
        spec.entails(p.leads_to(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(zookeeper)))),
    ensures spec.entails(p.leads_to(always(lift_state(sub_resource_state_matches(SubResource::StatefulSet, zookeeper))))),
{
    let post = sub_resource_state_matches(SubResource::StatefulSet, zookeeper);
    let resource_key = get_request(SubResource::StatefulSet, zookeeper).key;
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, zookeeper)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
        &&& helper_invariants::cm_rv_stays_unchanged(zookeeper)(s, s_prime)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::StatefulSet, zookeeper)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)),
        lift_action(helper_invariants::cm_rv_stays_unchanged(zookeeper))
    );

    assert forall |s, s_prime: ZKCluster| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        StatefulSetView::marshal_preserves_integrity();
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
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
