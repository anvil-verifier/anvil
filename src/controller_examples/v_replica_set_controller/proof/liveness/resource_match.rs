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
    proof::{helper_invariants, predicate::*, resource::*},
    trusted::{spec_types::*, step::*},
};
use vstd::{prelude::*, string::*};

verus! {

pub proof fn lemma_from_after_get_resource_step_to_resource_matches(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView, sub_resource: SubResource
)
    requires
        sub_resource != SubResource::StatefulSet,
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
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)))),
    ensures
        spec.entails(
            lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper))
                .leads_to(lift_state(sub_resource_state_matches(sub_resource, zookeeper)))
        ),
        sub_resource != SubResource::ConfigMap ==> spec.entails(
            lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper))
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource).get_AfterKRequestStep_1(), zookeeper)))
        ),
        sub_resource == SubResource::ConfigMap ==> spec.entails(
            lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper))
                .leads_to(lift_state(pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper)))
        ),
{
    lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(spec, sub_resource, zookeeper);
    lemma_from_after_get_resource_step_and_key_exists_to_resource_matches(spec, sub_resource, zookeeper);
    let key_not_exists = lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper)(s)
    });
    let key_exists = lift_state(|s: ZKCluster| {
        &&& s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper)(s)
    });
    or_leads_to_combine_temp(spec, key_not_exists, key_exists, lift_state(sub_resource_state_matches(sub_resource, zookeeper)));
    temp_pred_equality(
        key_not_exists.or(key_exists), lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper))
    );

    let next_state = if sub_resource != SubResource::ConfigMap {
        pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource).get_AfterKRequestStep_1(), zookeeper)
    } else {
        pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper) // ConfigMap is a bit different since its next step is not a SubResource type
    };
    or_leads_to_combine_temp(spec, key_not_exists, key_exists, lift_state(next_state));
}

pub proof fn lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(
    spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper)(s)
            }).leads_to(lift_state(sub_resource_state_matches(sub_resource, zookeeper)))
        ),
        sub_resource != SubResource::ConfigMap && sub_resource != SubResource::StatefulSet ==> spec.entails(
            lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource).get_AfterKRequestStep_1(), zookeeper)))
        ),
        sub_resource == SubResource::ConfigMap ==> spec.entails(
            lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper)))
        ),
{
    let pre = lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper)(s)
    });
    let post = lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, zookeeper)(s)
    });
    let pre_and_req_in_flight = |req_msg| lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, zookeeper, req_msg)(s)
    });
    let pre_and_exists_resp_in_flight = lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, zookeeper)(s)
    });
    let pre_and_resp_in_flight = |resp_msg| lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, zookeeper, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res.is_Err()
        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
    });
    let post_and_req_in_flight = |req_msg| lift_state(|s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, zookeeper, req_msg)(s)
    });
    let match_and_ok_resp = lift_state(sub_resource_state_matches(sub_resource, zookeeper))
        .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)));
    let next_state = if sub_resource != SubResource::ConfigMap {
        pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource).get_AfterKRequestStep_1(), zookeeper)
    } else {
        pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper) // ConfigMap is a bit different since its next step is not a SubResource type
    };

    assert_by(spec.entails(pre.leads_to(match_and_ok_resp)), {
        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight)) by {
            lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(spec, sub_resource, zookeeper, req_msg);
        }
        leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
        assert_by(tla_exists(pre_and_req_in_flight) == pre, {
            assert forall |ex| #[trigger] pre.satisfied_by(ex) implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
        });

        assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(post)) by {
            lemma_from_after_get_resource_step_to_after_create_resource_step(spec, sub_resource, zookeeper, resp_msg);
        }
        leads_to_exists_intro(spec, pre_and_resp_in_flight, post);
        assert_by(tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight, {
            assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex) implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                    &&& resp_msg.content.get_get_response().res.is_Err()
                    &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                };
                assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
        });

        assert forall |req_msg| spec.entails(#[trigger] post_and_req_in_flight(req_msg).leads_to(match_and_ok_resp)) by {
            lemma_resource_state_matches_at_after_create_resource_step(spec, sub_resource, zookeeper, req_msg);
        }
        leads_to_exists_intro(spec, post_and_req_in_flight, match_and_ok_resp);
        assert_by(tla_exists(post_and_req_in_flight) == post, {
            assert forall |ex| #[trigger] post.satisfied_by(ex) implies tla_exists(post_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                assert(post_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(post_and_req_in_flight), post);
        });
        leads_to_trans_n!(spec, pre, pre_and_exists_resp_in_flight, post, match_and_ok_resp);
    });

    assert_by(spec.entails(pre.leads_to(lift_state(sub_resource_state_matches(sub_resource, zookeeper)))), {
        valid_implies_implies_leads_to(spec, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, zookeeper)));
        leads_to_trans_n!(spec, pre, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, zookeeper)));
    });

    // We already have the desired state.
    // Now prove the system can successfully enter the next state.
    if sub_resource != SubResource::StatefulSet {
        assert_by(spec.entails(pre.leads_to(lift_state(next_state))), {
            let known_ok_resp = |resp_msg: ZKMessage| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, zookeeper, resp_msg));
            assert forall |resp_msg| spec.entails(#[trigger] known_ok_resp(resp_msg).leads_to(lift_state(next_state))) by {
                let pre = resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, zookeeper, resp_msg);
                let stronger_next = |s, s_prime: ZKCluster| {
                    &&& ZKCluster::next()(s, s_prime)
                    &&& ZKCluster::crash_disabled()(s)
                    &&& ZKCluster::busy_disabled()(s)
                    &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
                    &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
                };

                combine_spec_entails_always_n!(
                    spec, lift_action(stronger_next),
                    lift_action(ZKCluster::next()),
                    lift_state(ZKCluster::crash_disabled()),
                    lift_state(ZKCluster::busy_disabled()),
                    lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
                    lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref()))
                );

                assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || next_state(s_prime) by {
                    let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep(input) => {
                            if input.1.is_Some() && input.1.get_Some_0() == zookeeper.object_ref() {
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
                ZKCluster::lemma_pre_leads_to_post_by_controller(
                    spec, (Some(resp_msg), Some(zookeeper.object_ref())), stronger_next, ZKCluster::continue_reconcile(), pre, next_state
                );
            }
            leads_to_exists_intro(spec, known_ok_resp, lift_state(next_state));
            let exists_ok_resp = lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper));
            assert_by(tla_exists(known_ok_resp) == exists_ok_resp, {
                assert forall |ex| #[trigger] exists_ok_resp.satisfied_by(ex) implies tla_exists(known_ok_resp).satisfied_by(ex) by {
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                        &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                        &&& resp_msg.content.get_create_response().res.is_Ok()
                        &&& state_after_create(sub_resource, zookeeper, resp_msg.content.get_create_response().res.get_Ok_0(), ex.head().ongoing_reconciles()[zookeeper.object_ref()].local_state).is_Ok()
                    };
                    assert(known_ok_resp(resp_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(known_ok_resp), exists_ok_resp);
            });
            valid_implies_implies_leads_to(spec, match_and_ok_resp, exists_ok_resp);
            leads_to_trans_n!(spec, pre, match_and_ok_resp, exists_ok_resp, lift_state(next_state));
        });
    }
}

proof fn lemma_from_after_get_resource_step_and_key_exists_to_resource_matches(
    spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView
)
    requires
        sub_resource != SubResource::StatefulSet,
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
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(sub_resource, zookeeper).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper)(s)
            }).leads_to(lift_state(sub_resource_state_matches(sub_resource, zookeeper)))
        ),
        sub_resource != SubResource::ConfigMap ==> spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(sub_resource, zookeeper).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource).get_AfterKRequestStep_1(), zookeeper)))
        ),
        sub_resource == SubResource::ConfigMap ==> spec.entails(
            lift_state(|s: ZKCluster| {
                &&& s.resources().contains_key(get_request(sub_resource, zookeeper).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper)))
        ),
{
    let resource_key = get_request(sub_resource, zookeeper).key;
    let pre = lift_state(|s: ZKCluster| {
        &&& s.resources().contains_key(resource_key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, zookeeper)(s)
    });
    let post = pending_req_in_flight_at_after_update_resource_step(sub_resource, zookeeper);
    let match_and_ok_resp = lift_state(sub_resource_state_matches(sub_resource, zookeeper)).and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)));
    let next_state = if sub_resource != SubResource::ConfigMap {
        pending_req_in_flight_at_after_get_resource_step(next_resource_after(sub_resource).get_AfterKRequestStep_1(), zookeeper)
    } else {
        pending_req_in_flight_at_after_exists_stateful_set_step(zookeeper) // ConfigMap is a bit different since its next step is not a SubResource type
    };
    assert_by(spec.entails(pre.leads_to(match_and_ok_resp)), {
        let pre_and_req_in_flight = |req_msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, zookeeper, req_msg));
        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper))))
        by {
            lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(spec, sub_resource, zookeeper, req_msg);
        }
        leads_to_exists_intro(spec, pre_and_req_in_flight, lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)));
        assert_by(tla_exists(pre_and_req_in_flight) == pre, {
            assert forall |ex| #[trigger] pre.satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
        });
        let pre_and_resp_in_flight = |resp_msg| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, zookeeper, resp_msg));
        assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(lift_state(post)))
        by {
            lemma_from_after_get_resource_step_to_after_update_resource_step(spec, sub_resource, zookeeper, resp_msg);
        }
        leads_to_exists_intro(spec, pre_and_resp_in_flight, lift_state(post));
        assert_by(tla_exists(pre_and_resp_in_flight) == lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)), {
            assert forall |ex| #[trigger] lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)).satisfied_by(ex)
            implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                    &&& resp_msg.content.get_get_response().res.is_Ok()
                    &&& resp_msg.content.get_get_response().res.get_Ok_0() == ex.head().resources()[resource_key]
                };
                assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_resp_in_flight), lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)));
        });
        let pre_and_req_in_flight = |req_msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, zookeeper, req_msg));
        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(match_and_ok_resp)) by {
            lemma_resource_state_matches_at_after_update_resource_step(spec, sub_resource, zookeeper, req_msg);
        }
        leads_to_exists_intro(spec, pre_and_req_in_flight, match_and_ok_resp);
        assert_by(tla_exists(pre_and_req_in_flight) == lift_state(post), {
            assert forall |ex| #[trigger] lift_state(post).satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), lift_state(post));
        });
        leads_to_trans_n!(
            spec, pre, lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)),
            lift_state(post), match_and_ok_resp
        );
    });

    assert_by(spec.entails(pre.leads_to(lift_state(sub_resource_state_matches(sub_resource, zookeeper)))), {
        valid_implies_implies_leads_to(spec, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, zookeeper)));
        leads_to_trans_n!(spec, pre, match_and_ok_resp, lift_state(sub_resource_state_matches(sub_resource, zookeeper)));
    });

    // We already have the desired state.
    // Now prove the system can successfully enter the next state.
    assert_by(spec.entails(pre.leads_to(lift_state(next_state))), {
        let known_ok_resp = |resp_msg: ZKMessage| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, zookeeper, resp_msg));
        assert forall |resp_msg| spec.entails(#[trigger] known_ok_resp(resp_msg).leads_to(lift_state(next_state))) by {
            let pre = resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, zookeeper, resp_msg);
            let stronger_next = |s, s_prime: ZKCluster| {
                &&& ZKCluster::next()(s, s_prime)
                &&& ZKCluster::crash_disabled()(s)
                &&& ZKCluster::busy_disabled()(s)
                &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
                &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
            };
            combine_spec_entails_always_n!(
                spec, lift_action(stronger_next),
                lift_action(ZKCluster::next()),
                lift_state(ZKCluster::crash_disabled()),
                lift_state(ZKCluster::busy_disabled()),
                lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
                lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref()))
            );
            assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || next_state(s_prime) by {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        if input.1.is_Some() && input.1.get_Some_0() == zookeeper.object_ref() {
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
            ZKCluster::lemma_pre_leads_to_post_by_controller(
                spec, (Some(resp_msg), Some(zookeeper.object_ref())), stronger_next, ZKCluster::continue_reconcile(), pre, next_state
            );
        }
        leads_to_exists_intro(spec, known_ok_resp, lift_state(next_state));
        let exists_ok_resp = lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper));
        assert_by(tla_exists(known_ok_resp) == exists_ok_resp, {
            assert forall |ex| #[trigger] exists_ok_resp.satisfied_by(ex) implies tla_exists(known_ok_resp).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0())
                    &&& resp_msg.content.get_update_response().res.is_Ok()
                    &&& state_after_update(sub_resource, zookeeper, resp_msg.content.get_update_response().res.get_Ok_0(), ex.head().ongoing_reconciles()[zookeeper.object_ref()].local_state).is_Ok()
                };
                assert(known_ok_resp(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(known_ok_resp), exists_ok_resp);
        });
        valid_implies_implies_leads_to(spec, match_and_ok_resp, exists_ok_resp);
        leads_to_trans_n!(spec, pre, match_and_ok_resp, exists_ok_resp, lift_state(next_state));
    });
}

proof fn lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(
    spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView, req_msg: ZKMessage
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)))),
    ensures
        spec.entails(
            lift_state(
                |s: ZKCluster| {
                    &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
                    &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, zookeeper, req_msg)(s)
                }
            ).leads_to(lift_state(
                |s: ZKCluster| {
                    &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
                    &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, zookeeper)(s)
                }
            ))
        ),
{
    let pre = |s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, zookeeper, req_msg)(s)
    };
    let post = |s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, zookeeper)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                assert(!resource_create_request_msg(get_request(sub_resource, zookeeper).key)(input.get_Some_0()));
                if input.get_Some_0() == req_msg {
                    let resp_msg = ZKCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
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

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = ZKCluster::handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        });
    }

    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, ZKCluster::handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_resource_step_to_after_create_resource_step(
    spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView, resp_msg: ZKMessage
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
    ensures
        spec.entails(
            lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
                &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, zookeeper, resp_msg)(s)
                &&& resp_msg.content.get_get_response().res.is_Err()
                &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
            }).leads_to(lift_state(|s: ZKCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
                &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, zookeeper)(s)
            }))
        ),
{
    let pre = |s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, zookeeper, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res.is_Err()
        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
    };
    let post = |s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, zookeeper)(s)
    };
    let input = (Some(resp_msg), Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                assert(!resource_create_request_msg(get_request(sub_resource, zookeeper).key)(input.get_Some_0()));
            },
            _ => {}
        }
    }

    ZKCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next, ZKCluster::continue_reconcile(), pre, post
    );
}

proof fn lemma_resource_state_matches_at_after_create_resource_step(
    spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView, req_msg: ZKMessage
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)))),
    ensures
        spec.entails(
            lift_state(
                |s: ZKCluster| {
                    &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
                    &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, zookeeper, req_msg)(s)
                }
            ).leads_to(
                lift_state(sub_resource_state_matches(sub_resource, zookeeper))
                .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)))
            )
        ),
{
    let pre = |s: ZKCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, zookeeper, req_msg)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper))
    );

    let post = |s: ZKCluster| {
        &&& sub_resource_state_matches(sub_resource, zookeeper)(s)
        &&& at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)(s)
    };

    assert forall |s, s_prime: ZKCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let pending_msg = s.ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
        let resp = ZKCluster::handle_create_request_msg(pending_msg, s.kubernetes_api_state).1;
        assert(s_prime.in_flight().contains(resp));
        match sub_resource {
            SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
            SubResource::ClientService => ServiceView::marshal_preserves_integrity(),
            SubResource::AdminServerService => ServiceView::marshal_preserves_integrity(),
            SubResource::ConfigMap => ConfigMapView::marshal_preserves_integrity(),
            SubResource::StatefulSet => StatefulSetView::marshal_preserves_integrity(),
        }
    }

    assert forall |s, s_prime: ZKCluster| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                if resource_create_request_msg(get_request(sub_resource, zookeeper).key)(input.get_Some_0()) {} else {}
            },
            _ => {},
        }
    }

    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, ZKCluster::handle_request(), pre, post
    );
    temp_pred_equality(
        lift_state(post),
        lift_state(sub_resource_state_matches(sub_resource, zookeeper))
            .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)))
    );
}

proof fn lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView, req_msg: ZKMessage)
    requires
        sub_resource != SubResource::StatefulSet,
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)))),
    ensures
        spec.entails(lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, zookeeper, req_msg))
            .leads_to(lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)))),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, zookeeper, req_msg);
    let post = at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper);
    let resource_key = get_request(sub_resource, zookeeper).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                assert(!resource_update_request_msg(get_request(sub_resource, zookeeper).key)(req));
                assert(!resource_delete_request_msg(get_request(sub_resource, zookeeper).key)(req));
                assert(!resource_update_status_request_msg(get_request(sub_resource, zookeeper).key)(req));
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

proof fn lemma_resource_state_matches_at_after_update_resource_step(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView, req_msg: ZKMessage)
    requires
        sub_resource != SubResource::StatefulSet,
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)))),
    ensures
        spec.entails(lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, zookeeper, req_msg))
            .leads_to(lift_state(sub_resource_state_matches(sub_resource, zookeeper))
                .and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper))))),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, zookeeper, req_msg);
    let resource_key = get_request(sub_resource, zookeeper).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::desired_state_is(zookeeper)(s)
        &&& helper_invariants::the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)(s)
        &&& helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)(s)
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
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)),
        lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper))
    );

    let post = |s: ZKCluster| {
        &&& sub_resource_state_matches(sub_resource, zookeeper)(s)
        &&& at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)(s)
    };

    assert forall |s, s_prime: ZKCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && ZKCluster::kubernetes_api_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let pending_msg = s.ongoing_reconciles()[zookeeper.object_ref()].pending_req_msg.get_Some_0();
        let resp = ZKCluster::handle_update_request_msg(pending_msg, s.kubernetes_api_state).1;
        assert(s_prime.in_flight().contains(resp));
        match sub_resource {
            SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
            SubResource::ClientService => ServiceView::marshal_preserves_integrity(),
            SubResource::AdminServerService => ServiceView::marshal_preserves_integrity(),
            SubResource::ConfigMap => ConfigMapView::marshal_preserves_integrity(),
            _ => {}
        }
    }

    assert forall |s, s_prime: ZKCluster| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                assert(!resource_delete_request_msg(resource_key)(input.get_Some_0()));
                assert(!resource_update_status_request_msg(resource_key)(input.get_Some_0()));
                if resource_update_request_msg(resource_key)(input.get_Some_0()) {} else {}
            },
            _ => {},
        }
    }

    ZKCluster::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, ZKCluster::handle_request(), pre, post);
    temp_pred_equality(
        lift_state(post),
        lift_state(sub_resource_state_matches(sub_resource, zookeeper))
            .and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, zookeeper)))
    );
}

proof fn lemma_from_after_get_resource_step_to_after_update_resource_step(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView, resp_msg: ZKMessage)
    requires
        sub_resource != SubResource::StatefulSet,
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)))),
    ensures spec.entails(lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, zookeeper, resp_msg)).leads_to(lift_state(pending_req_in_flight_at_after_update_resource_step(sub_resource, zookeeper)))),
{
    let pre = resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, zookeeper, resp_msg);
    let post = pending_req_in_flight_at_after_update_resource_step(sub_resource, zookeeper);
    let input = (Some(resp_msg), Some(zookeeper.object_ref()));
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::desired_state_is(zookeeper)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)(s)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)(s)
        &&& helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::pending_req_of_key_is_unique_with_unique_id(zookeeper.object_ref())),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)),
        lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)),
        lift_state(ZKCluster::desired_state_is(zookeeper))
    );

    assert forall |s, s_prime: ZKCluster| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                assert(!resource_update_status_request_msg(get_request(sub_resource, zookeeper).key)(req));
                assert(!resource_delete_request_msg(get_request(sub_resource, zookeeper).key)(req));
                if resource_update_request_msg(get_request(sub_resource, zookeeper).key)(req) {} else {}
            },
            _ => {},
        }
    }

    ZKCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        ZKCluster::continue_reconcile(), pre, post
    );
}

pub proof fn lemma_resource_object_is_stable(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView, p: TempPred<ZKCluster>)
    requires
        sub_resource != SubResource::StatefulSet,
        spec.entails(p.leads_to(lift_state(sub_resource_state_matches(sub_resource, zookeeper)))),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)))),
    ensures spec.entails(p.leads_to(always(lift_state(sub_resource_state_matches(sub_resource, zookeeper))))),
{
    let post = sub_resource_state_matches(sub_resource, zookeeper);
    let resource_key = get_request(sub_resource, zookeeper).key;
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(helper_invariants::no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper))
    );

    assert forall |s, s_prime: ZKCluster| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                assert(!resource_delete_request_msg(get_request(sub_resource, zookeeper).key)(req));
                assert(!resource_update_status_request_msg(get_request(sub_resource, zookeeper).key)(req));
                if resource_update_request_msg(get_request(sub_resource, zookeeper).key)(req) {} else {}
            },
            _ => {},
        }
        match sub_resource {
            SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
            SubResource::ClientService => ServiceView::marshal_preserves_integrity(),
            SubResource::AdminServerService => ServiceView::marshal_preserves_integrity(),
            SubResource::ConfigMap => ConfigMapView::marshal_preserves_integrity(),
            _ => {}
        }
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), p, lift_state(post));
}

}
