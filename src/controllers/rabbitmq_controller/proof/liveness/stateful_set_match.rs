// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
// DEPRECATED
#![allow(unused_imports)]
use crate::vstatefulset_controller::trusted::spec_types::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
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
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::crash_disabled()))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)))),
    ensures spec.entails(lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq)).leads_to(lift_state(sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)))),
{
    let next_res = next_resource_after(SubResource::VStatefulSetView)->AfterKRequestStep_1;
    lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(spec, SubResource::VStatefulSetView, next_res, rabbitmq);
    lemma_from_after_get_stateful_set_step_and_key_exists_to_stateful_set_matches(spec, rabbitmq);
    let key_not_exists = lift_state(|s: ClusterState| {
        &&& !s.resources().contains_key(get_request(SubResource::VStatefulSetView, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
    });
    let key_exists = lift_state(|s: ClusterState| {
        &&& s.resources().contains_key(get_request(SubResource::VStatefulSetView, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
    });
    or_leads_to_combine(spec, key_not_exists, key_exists, lift_state(sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)));
    temp_pred_equality(
        key_not_exists.or(key_exists), lift_state(pending_req_in_flight_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq))
    );
}

proof fn lemma_from_after_get_stateful_set_step_and_key_exists_to_stateful_set_matches(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.controller_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::crash_disabled()))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)))),
    ensures
        spec.entails(lift_state(|s: ClusterState| {
            &&& s.resources().contains_key(get_request(SubResource::VStatefulSetView, rabbitmq).key)
            &&& pending_req_in_flight_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
        }).leads_to(lift_state(sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)))),
{
    let sts_key = get_request(SubResource::VStatefulSetView, rabbitmq).key;
    let pre = lift_state(|s: ClusterState| {
        &&& s.resources().contains_key(get_request(SubResource::VStatefulSetView, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
    });
    let stateful_set_matches = lift_state(|s: ClusterState| {
        &&& s.resources().contains_key(sts_key)
        &&& sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
    });
    let stateful_set_not_matches = lift_state(|s: ClusterState| {
        &&& s.resources().contains_key(sts_key)
        &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& pending_req_in_flight_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
    });
    let post = lift_state(sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq));

    assert_by(spec.entails(stateful_set_matches.leads_to(post)), {
        entails_implies_leads_to(spec, stateful_set_matches, post);
    });

    assert_by(spec.entails(stateful_set_not_matches.leads_to(post)), {
        let pre1 = |req_msg| lift_state(|s: ClusterState| {
            &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(SubResource::VStatefulSetView, rabbitmq, req_msg)(s)
            &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
        });
        let post1 = lift_state(|s: ClusterState| {
            &&& at_after_get_resource_step_and_exists_ok_resp_in_flight(SubResource::VStatefulSetView, rabbitmq)(s)
            &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
        });
        assert forall |req_msg| spec.entails(#[trigger] pre1(req_msg).leads_to(post1)) by {
            lemma_from_key_exists_to_receives_ok_resp_at_after_get_stateful_set_step(spec, rabbitmq, req_msg);
        }
        leads_to_exists_intro(spec, pre1, post1);
        assert_by(tla_exists(pre1) == stateful_set_not_matches, {
            assert forall |ex| #[trigger] stateful_set_not_matches.satisfied_by(ex)
            implies tla_exists(pre1).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
                assert(pre1(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre1), stateful_set_not_matches);
        });

        let pre2 = |resp_msg| lift_state(|s: ClusterState| {
            &&& resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq, resp_msg)(s)
            &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
        });
        let post2 = lift_state(|s: ClusterState| {
            &&& pending_req_in_flight_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
            &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
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
                    &&& resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0)
                    &&& resp_msg.content.get_get_response().res is Ok
                    &&& resp_msg.content.get_get_response().res->Ok_0 == ex.head().resources()[sts_key]
                };
                assert(pre2(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre2), post1);
        });

        let pre3 = |req_msg| lift_state(|s: ClusterState| {
            &&& req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq, req_msg)(s)
            &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
        });
        assert forall |req_msg| spec.entails(#[trigger] pre3(req_msg).leads_to(post)) by {
            lemma_stateful_set_state_matches_at_after_update_stateful_set_step(spec, rabbitmq, req_msg);
        }
        leads_to_exists_intro(spec, pre3, post);
        assert_by(tla_exists(pre3) == post2, {
            assert forall |ex| #[trigger] post2.satisfied_by(ex)
            implies tla_exists(pre3).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
                assert(pre3(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre3), post2);
        });

        leads_to_trans_n!(spec, stateful_set_not_matches, post1, post2, post);
    });

    or_leads_to_combine(spec, stateful_set_matches, stateful_set_not_matches, post);
    temp_pred_equality(stateful_set_matches.or(stateful_set_not_matches), pre);
}

#[verifier(spinoff_prover)]
proof fn lemma_from_key_exists_to_receives_ok_resp_at_after_get_stateful_set_step(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::crash_disabled()))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)))),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(SubResource::VStatefulSetView, rabbitmq, req_msg)(s)
                &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
            })
            .leads_to(lift_state(|s: ClusterState| {
                &&& at_after_get_resource_step_and_exists_ok_resp_in_flight(SubResource::VStatefulSetView, rabbitmq)(s)
                &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
            }))
        ),
{
    let pre = |s: ClusterState| {
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(SubResource::VStatefulSetView, rabbitmq, req_msg)(s)
        &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
    };
    let post = |s: ClusterState| {
        &&& at_after_get_resource_step_and_exists_ok_resp_in_flight(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
    };
    let resource_key = get_request(SubResource::VStatefulSetView, rabbitmq).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled()(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq)(s)
        &&& helper_invariants::cm_rv_stays_unchanged(rabbitmq)(s, s_prime)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled()),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq)),
        lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let req = input->0;
                assert(!resource_delete_request_msg(resource_key)(req));
                assert(!resource_update_request_msg(resource_key)(req));
                assert(!resource_update_status_request_msg(resource_key)(req));
                if req == req_msg {
                    let resp_msg = handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
                    assert({
                        &&& s_prime.in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                        &&& resp_msg.content.get_get_response().res is Ok
                        &&& resp_msg.content.get_get_response().res->Ok_0 == s_prime.resources()[resource_key]
                    });
                    assert(post(s_prime));
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = handle_get_request_msg(req_msg, s.kubernetes_api_state).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res is Ok
            &&& resp_msg.content.get_get_response().res->Ok_0 == s_prime.resources()[resource_key]
        });
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

#[verifier(spinoff_prover)]
proof fn lemma_from_after_get_stateful_set_step_to_after_update_stateful_set_step(
    spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.controller_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::crash_disabled()))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)))),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq, resp_msg)(s)
                &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
            })
            .leads_to(lift_state(|s: ClusterState| {
                &&& pending_req_in_flight_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
                &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
            }))
        ),
{
    let pre = |s: ClusterState| {
        &&& resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(SubResource::VStatefulSetView, rabbitmq, resp_msg)(s)
        &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
    };
    let post = |s: ClusterState| {
        &&& pending_req_in_flight_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
    };
    let input = (Some(resp_msg), Some(rabbitmq.object_ref()));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled()(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& Cluster::desired_state_is(rabbitmq)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq)(s)
        &&& helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
        &&& helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)(s)
        &&& helper_invariants::cm_rv_stays_unchanged(rabbitmq)(s, s_prime)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled()),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(rabbitmq.object_ref())),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq)),
        lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)),
        lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)),
        lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq))
    );

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        let resource_key = get_request(SubResource::VStatefulSetView, rabbitmq).key;
        match step {
            Step::APIServerStep(input) => {
                let req = input->0;
                assert(!resource_delete_request_msg(resource_key)(req));
                assert(!resource_update_request_msg(resource_key)(req));
                assert(!resource_update_status_request_msg(resource_key)(req));
            },
            _ => {}
        }
    }
    Cluster::lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post);
}

#[verifier(spinoff_prover)]
proof fn lemma_stateful_set_state_matches_at_after_update_stateful_set_step(spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, req_msg: Message)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::crash_disabled()))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)))),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq, req_msg)(s)
                &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
            })
            .leads_to(lift_state(sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)))
        ),
{
    let pre = |s: ClusterState| {
        &&& req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq, req_msg)(s)
        &&& !sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s)
    };
    let post = sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq);

    let resource_key = get_request(SubResource::VStatefulSetView, rabbitmq).key;
    let resource_well_formed = |s: ClusterState| {
        s.resources().contains_key(resource_key)
        ==> Cluster::etcd_object_is_well_formed(resource_key)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled()(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& resource_well_formed(s)
        &&& Cluster::desired_state_is(rabbitmq)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
        &&& helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)(s)
    };
    always_weaken(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()), lift_state(resource_well_formed));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled()),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(resource_well_formed),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)),
        lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::stateful_set_in_etcd_satisfies_unchangeable(rabbitmq))
    );

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let pending_msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let resp = handle_update_request_msg(pending_msg, s.kubernetes_api_state).1;
        assert(s_prime.in_flight().contains(resp));
        VStatefulSetView::marshal_preserves_integrity();
    }

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let req = input->0;
                assert(!resource_delete_request_msg(resource_key)(req));
                assert(!resource_update_status_request_msg(resource_key)(req));
                if resource_update_request_msg(resource_key)(req) {} else {}
            },
            _ => {}
        }
    }

    cluster.lemma_pre_leads_to_post_by_api_server(spec, input, stronger_next, APIServerStep::HandleRequest, pre, post);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_stateful_set_is_stable(spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, p: TempPred<ClusterState>)
    requires
        spec.entails(p.leads_to(lift_state(sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)))),
        spec.entails(always(lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq)))),
    ensures spec.entails(p.leads_to(always(lift_state(sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq))))),
{
    let post = sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq);
    let resource_key = get_request(SubResource::VStatefulSetView, rabbitmq).key;
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
        &&& helper_invariants::cm_rv_stays_unchanged(rabbitmq)(s, s_prime)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)),
        lift_action(helper_invariants::cm_rv_stays_unchanged(rabbitmq))
    );

    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        VStatefulSetView::marshal_preserves_integrity();
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let req = input->0;
                assert(!resource_delete_request_msg(resource_key)(req));
                if resource_update_request_msg(resource_key)(req) {} else {}
            },
            _ => {}
        }
    }

    leads_to_stable(spec, lift_action(stronger_next), p, lift_state(post));
}

}
