// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
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
use crate::rabbitmq_controller::{
    common::*,
    proof::{
        helper_invariants, liveness::spec::assumption_and_invariants_of_all_phases, predicate::*,
        resource::*,
    },
    spec::{reconciler::*, resource::*, types::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{prelude::*, string::*};

verus! {

pub open spec fn current_state_matches(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        resource_state_matches(sub_resource, rabbitmq, s.resources())
    }
}

proof fn lemma_from_after_get_resource_step_to_resource_matches(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, sub_resource: SubResource)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, rabbitmq).key, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::ServerConfigMap, rabbitmq)))),
    ensures
        spec.entails(
            lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq))
                .leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))
        ),
{
    lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(spec, sub_resource, rabbitmq);
    lemma_from_after_get_resource_step_and_key_exists_to_resource_matches(spec, sub_resource, rabbitmq);
    let key_not_exists = |s: RMQCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq)(s)
    };
    let key_exists = |s: RMQCluster| {
        &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq)(s)
    };
    or_leads_to_combine(spec, key_not_exists, key_exists, current_state_matches(sub_resource, rabbitmq));
    temp_pred_equality(
        lift_state(key_not_exists).or(lift_state(key_exists)), lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq))
    );
}

proof fn lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(
    spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq)(s)
            }).leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))
        ),
{
    let pre = lift_state(|s: RMQCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq)(s)
    });
    let post = lift_state(|s: RMQCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, rabbitmq)(s)
    });
    let pre_and_req_in_flight = |req_msg| lift_state(
        |s: RMQCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
            &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, req_msg)(s)
        }
    );
    let pre_and_exists_resp_in_flight = lift_state(
        |s: RMQCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
            &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, rabbitmq)(s)
        }
    );
    let pre_and_resp_in_flight = |resp_msg| lift_state(
        |s: RMQCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
            &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, rabbitmq, resp_msg)(s)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    );
    let post_and_req_in_flight = |req_msg| lift_state(
        |s: RMQCluster| {
            &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
            &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, rabbitmq, req_msg)(s)
        }
    );
    assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
    by {
        lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(spec, sub_resource, rabbitmq, req_msg);
    }
    leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
    assert_by(
        tla_exists(pre_and_req_in_flight) == pre,
        {
            assert forall |ex| #[trigger] pre.satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
        }
    );

    assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(post))
    by {
        lemma_from_after_get_resource_step_to_after_create_resource_step(spec, sub_resource, rabbitmq, resp_msg);
    }
    leads_to_exists_intro(spec, pre_and_resp_in_flight, post);
    assert_by(
        tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
        {
            assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
            implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
                    &&& resp_msg.content.get_get_response().res.is_Err()
                    &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
                };
                assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
        }
    );

    assert forall |req_msg| spec.entails(#[trigger] post_and_req_in_flight(req_msg).leads_to(lift_state(current_state_matches(sub_resource, rabbitmq))))
    by {
        lemma_resource_state_matches_at_after_create_resource_step(spec, sub_resource, rabbitmq, req_msg);
    }
    leads_to_exists_intro(spec, post_and_req_in_flight, lift_state(current_state_matches(sub_resource, rabbitmq)));
    assert_by(
        tla_exists(post_and_req_in_flight) == post,
        {
            assert forall |ex| #[trigger] post.satisfied_by(ex)
            implies tla_exists(post_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
                assert(post_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(post_and_req_in_flight), post);
        }
    );

    leads_to_trans_temp(spec, pre, pre_and_exists_resp_in_flight, post);
    leads_to_trans_temp(spec, pre, post, lift_state(current_state_matches(sub_resource, rabbitmq)));
}

proof fn lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(
    spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: RMQCluster| {
                    &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                    &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, req_msg)(s)
                }
            ).leads_to(lift_state(
                |s: RMQCluster| {
                    &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                    &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, rabbitmq)(s)
                }
            ))
        ),
{
    let pre = |s: RMQCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, req_msg)(s)
    };
    let post = |s: RMQCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, rabbitmq)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = RMQCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
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

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = RMQCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        });
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, RMQCluster::handle_request(), pre, post
    );
}

proof fn lemma_from_after_get_resource_step_and_key_exists_to_resource_matches(
    spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, rabbitmq).key, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq)))),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| {
                &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq)(s)
            }).leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))
        ),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let pre = lift_state(|s: RMQCluster| {
        &&& s.resources().contains_key(resource_key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq)(s)
    });
    let post = pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq);
    assert_by(
        spec.entails(pre.leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))),
        {
            let pre_and_req_in_flight = |req_msg| lift_state(
                |s: RMQCluster| {
                    req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, rabbitmq, req_msg)(s)
                }
            );

            assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq))))
            by {
                lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(spec, sub_resource, rabbitmq, req_msg);
                temp_pred_equality(
                    pre_and_req_in_flight(req_msg),
                    lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, rabbitmq, req_msg))
                );
            }
            leads_to_exists_intro(spec, pre_and_req_in_flight, lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq)));
            assert_by(
                tla_exists(pre_and_req_in_flight) == pre,
                {
                    assert forall |ex| #[trigger] pre.satisfied_by(ex)
                    implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                        let req_msg = ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
                        assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
                }
            );

            let pre_and_resp_in_flight = |resp_msg| lift_state(
                |s: RMQCluster| {
                    &&& s.resources().contains_key(resource_key)
                    &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, rabbitmq, resp_msg)(s)
                    &&& resp_msg.content.get_get_response().res.is_Ok()
                    &&& resp_msg.content.get_get_response().res.get_Ok_0() == s.resources()[resource_key]
                }
            );

            assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(lift_state(post)))
            by {
                lemma_from_after_get_resource_step_to_after_update_resource_step(spec, sub_resource, rabbitmq, resp_msg);
                temp_pred_equality(
                    pre_and_resp_in_flight(resp_msg), lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, resp_msg))
                );
            }
            leads_to_exists_intro(spec, pre_and_resp_in_flight, lift_state(post));
            assert_by(
                tla_exists(pre_and_resp_in_flight) == lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq)),
                {
                    assert forall |ex| #[trigger] lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq)).satisfied_by(ex)
                    implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                        let resp_msg = choose |resp_msg| {
                            &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                            &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
                            &&& resp_msg.content.get_get_response().res.is_Ok()
                            &&& resp_msg.content.get_get_response().res.get_Ok_0() == ex.head().resources()[resource_key]
                        };
                        assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_resp_in_flight), lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq)));
                }
            );

            let pre_and_req_in_flight = |req_msg| lift_state(
                |s: RMQCluster| {
                    req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rabbitmq, req_msg)(s)
                }
            );

            assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))) by {
                lemma_resource_state_matches_at_after_update_resource_step(spec, sub_resource, rabbitmq, req_msg);
                temp_pred_equality(
                    pre_and_req_in_flight(req_msg),
                    lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rabbitmq, req_msg))
                );
            }
            leads_to_exists_intro(spec, pre_and_req_in_flight, lift_state(current_state_matches(sub_resource, rabbitmq)));
            assert_by(
                tla_exists(pre_and_req_in_flight) == lift_state(post),
                {
                    assert forall |ex| #[trigger] lift_state(post).satisfied_by(ex)
                    implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                        let req_msg = ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
                        assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(pre_and_req_in_flight), lift_state(post));
                }
            );

            leads_to_trans_n!(
                spec, pre, lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq)), lift_state(post),
                lift_state(current_state_matches(sub_resource, rabbitmq))
            );
        }
    );
}

proof fn lemma_from_after_get_resource_step_to_after_create_resource_step(
    spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: RMQMessage
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(|s: RMQCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, rabbitmq, resp_msg)(s)
                &&& resp_msg.content.get_get_response().res.is_Err()
                &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
            }).leads_to(lift_state(|s: RMQCluster| {
                &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, rabbitmq)(s)
            }))
        ),
{
    let pre = |s: RMQCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, rabbitmq, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res.is_Err()
        &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
    };
    let post = |s: RMQCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, rabbitmq)(s)
    };
    let input = (Some(resp_msg), Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq))
    );

    RMQCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next, RMQCluster::continue_reconcile(), pre, post
    );
}

proof fn lemma_resource_state_matches_at_after_create_resource_step(
    spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(
                |s: RMQCluster| {
                    &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                    &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, rabbitmq, req_msg)(s)
                }
            ).leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))
        ),
{
    let pre = |s: RMQCluster| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, rabbitmq, req_msg)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(sub_resource, rabbitmq))
    );

    let post = current_state_matches(sub_resource, rabbitmq);

    assert forall |s, s_prime: RMQCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime) implies post(s_prime) by {
        assert(make(sub_resource, rabbitmq, s.ongoing_reconciles()[rabbitmq.object_ref()].local_state).is_Ok());
        match sub_resource {
            SubResource::HeadlessService => {
                ServiceView::marshal_preserves_integrity();
                assert(ServiceView::unmarshal(make_headless_service(rabbitmq).marshal()).get_Ok_0().spec.is_Some());
                assert(ServiceView::unmarshal(make_headless_service(rabbitmq).marshal()).get_Ok_0().state_validation());
                assert(RMQCluster::object_validity_check(make_headless_service(rabbitmq).marshal()).is_None());
                assert(post(s_prime));
            },
            SubResource::Service => {ServiceView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::ErlangCookieSecret => {SecretView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::DefaultUserSecret => {SecretView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::PluginsConfigMap => {
                ConfigMapView::marshal_preserves_integrity();assert(post(s_prime));
                assert(ConfigMapView::unmarshal(make_plugins_config_map(rabbitmq).marshal()).get_Ok_0().data == make_plugins_config_map(rabbitmq).data);
                assert(post(s_prime));
            },
            SubResource::ServerConfigMap => {
                ConfigMapView::marshal_preserves_integrity();
                assert(ConfigMapView::unmarshal(make_server_config_map(rabbitmq).marshal()).get_Ok_0().data == make_server_config_map(rabbitmq).data);
                assert(post(s_prime));
            },
            SubResource::ServiceAccount => {ServiceAccountView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::Role => {RoleView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::RoleBinding => {
                RoleBindingView::marshal_preserves_integrity();
                RoleBindingView::marshal_status_preserves_integrity();
                RoleBindingView::marshal_spec_preserves_integrity();
                RoleBindingView::unmarshal_result_determined_by_unmarshal_spec_and_status();
                assert(RoleBindingView::unmarshal(make_role_binding(rabbitmq).marshal()).get_Ok_0().state_validation());
                assert(RoleBindingView::unmarshal_spec(make_role_binding(rabbitmq).marshal().spec).get_Ok_0().0 == make_role_binding(rabbitmq).role_ref);
                assert(post(s_prime));},
            SubResource::StatefulSet => {
                StatefulSetView::marshal_preserves_integrity();
                StatefulSetView::marshal_status_preserves_integrity();
                StatefulSetView::marshal_spec_preserves_integrity();
                StatefulSetView::unmarshal_result_determined_by_unmarshal_spec_and_status();
                let cm_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
                assert(s.resources().contains_key(cm_key));
                assert(s.resources()[cm_key].metadata.resource_version.is_Some());
                assert(s.ongoing_reconciles()[rabbitmq.object_ref()].local_state.latest_config_map_rv_opt == Some(int_to_string_view(s.resources()[cm_key].metadata.resource_version.get_Some_0())));
                assert(post(s_prime));},
        }
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, RMQCluster::handle_request(), pre, current_state_matches(sub_resource, rabbitmq)
    );
}

proof fn lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(
    spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, rabbitmq, req_msg))
            .leads_to(lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq)))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, rabbitmq, req_msg);
    let post = at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq);
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)(s)
        &&& helper_invariants::no_delete_request_msg_in_flight_with_key(resource_key)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_with_key(resource_key)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)),
        lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(resource_key)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(resource_key))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if input.get_Some_0() == req_msg {
                    let resp_msg = RMQCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
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
        let resp_msg = RMQCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
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

proof fn lemma_resource_state_matches_at_after_update_resource_step(
    spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rabbitmq, req_msg))
            .leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rabbitmq, req_msg);
    let post = current_state_matches(sub_resource, rabbitmq);
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)(s)
        &&& helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)(s)
        &&& helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)),
        lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)),
        lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq))
    );

    assert forall |s, s_prime: RMQCluster| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime) implies post(s_prime) by {
        assert(make(sub_resource, rabbitmq, s.ongoing_reconciles()[rabbitmq.object_ref()].local_state).is_Ok());
        match sub_resource {
            SubResource::HeadlessService => {
                ServiceView::marshal_preserves_integrity();
                assert(ServiceView::unmarshal(make_headless_service(rabbitmq).marshal()).get_Ok_0().spec.is_Some());
                assert(ServiceView::unmarshal(make_headless_service(rabbitmq).marshal()).get_Ok_0().state_validation());
                assert(RMQCluster::object_validity_check(make_headless_service(rabbitmq).marshal()).is_None());
                assert(post(s_prime));
            },
            SubResource::Service => {ServiceView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::ErlangCookieSecret => {SecretView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::DefaultUserSecret => {SecretView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::PluginsConfigMap => {
                ConfigMapView::marshal_preserves_integrity();assert(post(s_prime));
                assert(ConfigMapView::unmarshal(make_plugins_config_map(rabbitmq).marshal()).get_Ok_0().data == make_plugins_config_map(rabbitmq).data);
                assert(post(s_prime));
            },
            SubResource::ServerConfigMap => {
                ConfigMapView::marshal_preserves_integrity();
                assert(ConfigMapView::unmarshal(make_server_config_map(rabbitmq).marshal()).get_Ok_0().data == make_server_config_map(rabbitmq).data);
                assert(post(s_prime));
            },
            SubResource::ServiceAccount => {ServiceAccountView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::Role => {RoleView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::RoleBinding => {
                RoleBindingView::marshal_preserves_integrity();
                RoleBindingView::marshal_status_preserves_integrity();
                RoleBindingView::marshal_spec_preserves_integrity();
                RoleBindingView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            },
            SubResource::StatefulSet => {
                StatefulSetView::marshal_preserves_integrity();
                StatefulSetView::marshal_status_preserves_integrity();
                StatefulSetView::marshal_spec_preserves_integrity();
                StatefulSetView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            },
        }
    }

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, RMQCluster::handle_request(), pre, current_state_matches(sub_resource, rabbitmq)
    );
}

proof fn lemma_from_after_get_resource_step_to_after_update_resource_step(
    spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: RMQMessage
)
    requires
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, rabbitmq).key, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
        rabbitmq.well_formed(),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, resp_msg))
            .leads_to(lift_state(pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq)))
        ),
{
    let pre = resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, resp_msg);
    let post = pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq);
    let input = (Some(resp_msg), Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::crash_disabled()(s)
        &&& RMQCluster::busy_disabled()(s)
        &&& RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())(s)
        &&& RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)(s)
        &&& helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)(s)
        &&& helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, rabbitmq).key, rabbitmq)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)),
        lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)),
        lift_state(helper_invariants::object_of_key_only_has_owner_reference_pointing_to_current_cr(get_request(sub_resource, rabbitmq).key, rabbitmq))
    );

    RMQCluster::lemma_pre_leads_to_post_by_controller(
        spec, input, stronger_next,
        RMQCluster::continue_reconcile(), pre, post
    );
}

proof fn lemma_resource_object_is_stable(
    spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, p: TempPred<RMQCluster>
)
    requires
        spec.entails(p.leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
        sub_resource != SubResource::StatefulSet,
    ensures
        spec.entails(p.leads_to(always(lift_state(current_state_matches(sub_resource, rabbitmq))))),
{
    let post = current_state_matches(sub_resource, rabbitmq);
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)(s)
        &&& helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(sub_resource, rabbitmq)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)),
        lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq))
    );

    assert forall |s, s_prime: RMQCluster| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        match sub_resource {
            SubResource::HeadlessService => {
                ServiceView::marshal_preserves_integrity();
                assert(ServiceView::unmarshal(make_headless_service(rabbitmq).marshal()).get_Ok_0().spec.is_Some());
                assert(ServiceView::unmarshal(make_headless_service(rabbitmq).marshal()).get_Ok_0().state_validation());
                assert(RMQCluster::object_validity_check(make_headless_service(rabbitmq).marshal()).is_None());
                assert(post(s_prime));
            },
            SubResource::Service => {ServiceView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::ErlangCookieSecret => {SecretView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::DefaultUserSecret => {SecretView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::PluginsConfigMap => {
                ConfigMapView::marshal_preserves_integrity();assert(post(s_prime));
                assert(ConfigMapView::unmarshal(make_plugins_config_map(rabbitmq).marshal()).get_Ok_0().data == make_plugins_config_map(rabbitmq).data);
                assert(post(s_prime));
            },
            SubResource::ServerConfigMap => {
                ConfigMapView::marshal_preserves_integrity();
                assert(ConfigMapView::unmarshal(make_server_config_map(rabbitmq).marshal()).get_Ok_0().data == make_server_config_map(rabbitmq).data);
                assert(post(s_prime));
            },
            SubResource::ServiceAccount => {ServiceAccountView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::Role => {RoleView::marshal_preserves_integrity();assert(post(s_prime));},
            SubResource::RoleBinding => {
                RoleBindingView::marshal_preserves_integrity();
                RoleBindingView::marshal_status_preserves_integrity();
                RoleBindingView::marshal_spec_preserves_integrity();
                RoleBindingView::unmarshal_result_determined_by_unmarshal_spec_and_status();
            },
            _ => {}
        }
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), p, lift_state(post));
}

proof fn lemma_stateful_set_is_stable(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, p: TempPred<RMQCluster>
)
    requires
        spec.entails(p.leads_to(lift_state(current_state_matches(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(SubResource::StatefulSet, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(SubResource::StatefulSet, rabbitmq).key)))),
        spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(SubResource::StatefulSet, rabbitmq).key, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)))),
    ensures
        spec.entails(p.leads_to(always(lift_state(current_state_matches(SubResource::StatefulSet, rabbitmq))))),
{
    let post = current_state_matches(SubResource::StatefulSet, rabbitmq);
    let resource_key = get_request(SubResource::StatefulSet, rabbitmq).key;
    let stronger_next = |s, s_prime: RMQCluster| {
        &&& RMQCluster::next()(s, s_prime)
        &&& helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(SubResource::StatefulSet, rabbitmq).key)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(SubResource::StatefulSet, rabbitmq).key)(s)
        &&& helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(SubResource::StatefulSet, rabbitmq).key, rabbitmq)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
        // &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s_prime)
        &&& helper_invariants::cm_rv_stays_unchanged(rabbitmq)(s, s_prime)
    };
    always_to_always_later(spec, lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(SubResource::StatefulSet, rabbitmq).key)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, rabbitmq)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_with_key(get_request(SubResource::StatefulSet, rabbitmq).key)),
        lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(SubResource::StatefulSet, rabbitmq).key, rabbitmq)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)),
        // later(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq))),
        lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq))
    );

    assert forall |s, s_prime: RMQCluster| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        StatefulSetView::marshal_preserves_integrity();
        StatefulSetView::marshal_status_preserves_integrity();
        StatefulSetView::marshal_spec_preserves_integrity();
        StatefulSetView::unmarshal_result_determined_by_unmarshal_spec_and_status();
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), p, lift_state(post));
}

}
