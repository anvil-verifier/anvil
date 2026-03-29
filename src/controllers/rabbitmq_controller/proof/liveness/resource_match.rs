// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::vstatefulset_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    api_server::{types::APIServerStep, state_machine::*},
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::resource_builder::*;
use crate::rabbitmq_controller::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants, liveness::spec::assumption_and_invariants_of_all_phases, predicate::*,
        resource::*, helper_lemmas::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*, rely_guarantee::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::{prelude::*, string::*};

verus! {

// Proves AtAfterKRequestStep(Get, sub_resource) ~> resource_state_matches(sub_resource, rabbitmq) and AtAfterKRequestStep(Get, sub_resource) ~>
// AtAfterKRequestStep(Get, next_resource). The second one is not applicable to StatefulSet which doesn't have a next resource.
//
// The proof contains two part: resource_key exists or does not exist at first. The proof of both parts contains several times of applying
// wf1, handle_get_request => continue_reconcile => handle_create/update_request => continue_reconcile.
pub proof fn lemma_from_after_get_resource_step_to_resource_matches(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, sub_resource: SubResource, next_resource: SubResource
)
    requires
        // sub_resource != SubResource::VStatefulSetView,
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)))),
    ensures
        spec.entails(lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id))
            .leads_to(lift_state(resource_state_matches(sub_resource, rabbitmq)))),
        next_resource_after(sub_resource) == after_get_k_request_step(next_resource) ==> spec.entails(
            lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id))
                .leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id)))
        ),
{
    lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(controller_id, cluster, spec, sub_resource, next_resource, rabbitmq);
    lemma_from_after_get_resource_step_and_key_exists_to_resource_matches(controller_id, cluster, spec, sub_resource, next_resource, rabbitmq);
    let key_not_exists = lift_state(|s: ClusterState| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id)(s)
    });
    let key_exists = lift_state(|s: ClusterState| {
        &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id)(s)
    });
    or_leads_to_combine(spec, key_not_exists, key_exists, lift_state(resource_state_matches(sub_resource, rabbitmq)));
    temp_pred_equality(
        key_not_exists.or(key_exists), lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id))
    );
    if next_resource_after(sub_resource) == after_get_k_request_step(next_resource) {
        or_leads_to_combine(spec, key_not_exists, key_exists, lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id)));
    }
}

pub proof fn lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, next_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq)))),
    ensures
        spec.entails(lift_state(|s: ClusterState| {
            &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
            &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id)(s)
        }).leads_to(lift_state(resource_state_matches(sub_resource, rabbitmq)))),
        next_resource_after(sub_resource) == after_get_k_request_step(next_resource) ==> spec.entails(
            lift_state(|s: ClusterState| {
                &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id)))
        ),
{
    let pre = lift_state(|s: ClusterState| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id)(s)
    });
    let post = lift_state(|s: ClusterState| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, rabbitmq, controller_id)(s)
    });
    let pre_and_req_in_flight = |req_msg| lift_state(|s: ClusterState| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
    });
    let pre_and_exists_resp_in_flight = lift_state(|s: ClusterState| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, rabbitmq, controller_id)(s)
    });
    let pre_and_resp_in_flight = |resp_msg| lift_state(|s: ClusterState| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res is Err
        &&& resp_msg.content.get_get_response().res->Err_0 is ObjectNotFound
    });
    let post_and_req_in_flight = |req_msg| lift_state(|s: ClusterState| {
        &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
    });
    let match_and_ok_resp = lift_state(resource_state_matches(sub_resource, rabbitmq))
        .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)));
    let next_state = pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id);

    assert_by(spec.entails(pre.leads_to(match_and_ok_resp)), {
        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight)) by {
            lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(controller_id, cluster, spec, sub_resource, rabbitmq, req_msg);
        }
        leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
        assert_by(tla_exists(pre_and_req_in_flight) == pre, {
            assert forall |ex| #[trigger] pre.satisfied_by(ex) implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
        });

        assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(post)) by {
            lemma_from_after_get_resource_step_to_after_create_resource_step(controller_id, cluster, spec, sub_resource, rabbitmq, resp_msg);
        }
        leads_to_exists_intro(spec, pre_and_resp_in_flight, post);
        assert_by(tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight, {
            assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex) implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0)
                    &&& resp_msg.content.get_get_response().res is Err
                    &&& resp_msg.content.get_get_response().res->Err_0 is ObjectNotFound
                };
                assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
        });

        assert forall |req_msg| spec.entails(#[trigger] post_and_req_in_flight(req_msg).leads_to(match_and_ok_resp)) by {
            lemma_resource_state_matches_at_after_create_resource_step(controller_id, cluster, spec, sub_resource, rabbitmq, req_msg);
        }
        leads_to_exists_intro(spec, post_and_req_in_flight, match_and_ok_resp);
        assert_by(tla_exists(post_and_req_in_flight) == post, {
            assert forall |ex| #[trigger] post.satisfied_by(ex) implies tla_exists(post_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
                assert(post_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(post_and_req_in_flight), post);
        });
        leads_to_trans_n!(spec, pre, pre_and_exists_resp_in_flight, post, match_and_ok_resp);
    });

    assert_by(spec.entails(pre.leads_to(lift_state(resource_state_matches(sub_resource, rabbitmq)))), {
        entails_implies_leads_to(spec, match_and_ok_resp, lift_state(resource_state_matches(sub_resource, rabbitmq)));
        leads_to_trans_n!(spec, pre, match_and_ok_resp, lift_state(resource_state_matches(sub_resource, rabbitmq)));
    });

    // We already have the desired state.
    // Now prove the system can successfully enter the next state.
    if next_resource_after(sub_resource) == after_get_k_request_step(next_resource) {
        assert_by(spec.entails(pre.leads_to(lift_state(next_state))), {
            let known_ok_resp = |resp_msg: Message| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, resp_msg));
            assert forall |resp_msg| spec.entails(#[trigger] known_ok_resp(resp_msg).leads_to(lift_state(next_state))) by {
                let pre = resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, resp_msg);
                let stronger_next = |s, s_prime: ClusterState| {
                    &&& cluster.next()(s, s_prime)
                    &&& Cluster::crash_disabled(controller_id)(s)
                    &&& Cluster::req_drop_disabled()(s)
                    &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rabbitmq.object_ref())(s)
                    &&& Cluster::every_in_flight_msg_has_unique_id()(s)
                };
                combine_spec_entails_always_n!(
                    spec, lift_action(stronger_next),
                    lift_action(cluster.next()),
                    lift_state(Cluster::crash_disabled(controller_id)),
                    lift_state(Cluster::req_drop_disabled()),
                    lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rabbitmq.object_ref())),
                    lift_state(Cluster::every_in_flight_msg_has_unique_id())
                );

                assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || next_state(s_prime) by {
                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep(input) => {
                            if input.2 is Some && input.2->0 == rabbitmq.object_ref() {
                                assert(RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state).unwrap().reconcile_step == after_get_k_request_step(next_resource));
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
                cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, (Some(resp_msg), Some(rabbitmq.object_ref())), stronger_next, ControllerStep::ContinueReconcile, pre, next_state
                );
            }
            leads_to_exists_intro(spec, known_ok_resp, lift_state(next_state));
            let exists_ok_resp = lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id));
            assert_by(tla_exists(known_ok_resp) == exists_ok_resp, {
                assert forall |ex| #[trigger] exists_ok_resp.satisfied_by(ex) implies tla_exists(known_ok_resp).satisfied_by(ex) by {
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0)
                        &&& resp_msg.content.get_create_response().res is Ok
                        &&& state_after_create(sub_resource, rabbitmq, resp_msg.content.get_create_response().res->Ok_0, RabbitmqReconcileState::unmarshal(ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state).unwrap()) is Ok
                    };
                    assert(known_ok_resp(resp_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(known_ok_resp), exists_ok_resp);
            });
            entails_implies_leads_to(spec, match_and_ok_resp, exists_ok_resp);
            leads_to_trans_n!(spec, pre, match_and_ok_resp, exists_ok_resp, lift_state(next_state));
        });
    }
}

proof fn lemma_from_after_get_resource_step_and_key_exists_to_resource_matches(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, next_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        // sub_resource != SubResource::VStatefulSetView,
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id)(s)
            }).leads_to(lift_state(resource_state_matches(sub_resource, rabbitmq)))
        ),
        next_resource_after(sub_resource) == after_get_k_request_step(next_resource) ==> spec.entails(
            lift_state(|s: ClusterState| {
                &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id)(s)
            }).leads_to(lift_state(pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id)))
        ),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let pre = lift_state(|s: ClusterState| {
        &&& s.resources().contains_key(resource_key)
        &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq, controller_id)(s)
    });
    let post = pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq, controller_id);
    let match_and_ok_resp = lift_state(resource_state_matches(sub_resource, rabbitmq)).and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)));
    let next_state = pending_req_in_flight_at_after_get_resource_step(next_resource, rabbitmq, controller_id);
    assert_by(spec.entails(pre.leads_to(match_and_ok_resp)), {
        let pre_and_req_in_flight = |req_msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, rabbitmq, controller_id, req_msg));
        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id))))
        by {
            lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(controller_id, cluster, spec, sub_resource, rabbitmq, req_msg);
        }
        leads_to_exists_intro(spec, pre_and_req_in_flight, lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)));
        assert_by(tla_exists(pre_and_req_in_flight) == pre, {
            assert forall |ex| #[trigger] pre.satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), pre);
        });
        let pre_and_resp_in_flight = |resp_msg| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg));
        assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(lift_state(post)))
        by {
            lemma_from_after_get_resource_step_to_after_update_resource_step(controller_id, cluster, spec, sub_resource, rabbitmq, resp_msg);
        }
        leads_to_exists_intro(spec, pre_and_resp_in_flight, lift_state(post));
        assert_by(tla_exists(pre_and_resp_in_flight) == lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)), {
            assert forall |ex| #[trigger] lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)).satisfied_by(ex)
            implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
                let resp_msg = choose |resp_msg| {
                    &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0)
                    &&& resp_msg.content.get_get_response().res is Ok
                    &&& resp_msg.content.get_get_response().res->Ok_0 == ex.head().resources()[resource_key]
                };
                assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_resp_in_flight), lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)));
        });
        let pre_and_req_in_flight = |req_msg| lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, req_msg));
        assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(match_and_ok_resp)) by {
            lemma_resource_state_matches_at_after_update_resource_step(controller_id, cluster, spec, sub_resource, rabbitmq, req_msg);
        }
        leads_to_exists_intro(spec, pre_and_req_in_flight, match_and_ok_resp);
        assert_by(tla_exists(pre_and_req_in_flight) == lift_state(post), {
            assert forall |ex| #[trigger] lift_state(post).satisfied_by(ex)
            implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
                let req_msg = ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
                assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
            }
            temp_pred_equality(tla_exists(pre_and_req_in_flight), lift_state(post));
        });
        leads_to_trans_n!(
            spec, pre, lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)),
            lift_state(post), match_and_ok_resp
        );
    });

    assert_by(spec.entails(pre.leads_to(lift_state(resource_state_matches(sub_resource, rabbitmq)))), {
        entails_implies_leads_to(spec, match_and_ok_resp, lift_state(resource_state_matches(sub_resource, rabbitmq)));
        leads_to_trans_n!(spec, pre, match_and_ok_resp, lift_state(resource_state_matches(sub_resource, rabbitmq)));
    });

    // We already have the desired state.
    // Now prove the system can successfully enter the next state.
    if next_resource_after(sub_resource) == after_get_k_request_step(next_resource) {
        assert_by(spec.entails(pre.leads_to(lift_state(next_state))), {
            let known_ok_resp = |resp_msg: Message| lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, resp_msg));
            assert forall |resp_msg| spec.entails(#[trigger] known_ok_resp(resp_msg).leads_to(lift_state(next_state))) by {
                let pre = resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, resp_msg);
                let stronger_next = |s, s_prime: ClusterState| {
                    &&& cluster.next()(s, s_prime)
                    &&& Cluster::crash_disabled(controller_id)(s)
                    &&& Cluster::req_drop_disabled()(s)
                    &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rabbitmq.object_ref())(s)
                    &&& Cluster::every_in_flight_msg_has_unique_id()(s)
                };

                combine_spec_entails_always_n!(
                    spec, lift_action(stronger_next),
                    lift_action(cluster.next()),
                    lift_state(Cluster::crash_disabled(controller_id)),
                    lift_state(Cluster::req_drop_disabled()),
                    lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rabbitmq.object_ref())),
                    lift_state(Cluster::every_in_flight_msg_has_unique_id())
                );

                assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || next_state(s_prime) by {
                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep(input) => {
                            if input.2 is Some && input.2->0 == rabbitmq.object_ref() {
                                // assert(input)
                                assert(RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state).unwrap().reconcile_step == after_get_k_request_step(next_resource));
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
                cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, (Some(resp_msg), Some(rabbitmq.object_ref())), stronger_next, ControllerStep::ContinueReconcile, pre, next_state
                );
            }
            leads_to_exists_intro(spec, known_ok_resp, lift_state(next_state));
            let exists_ok_resp = lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id));
            assert_by(tla_exists(known_ok_resp) == exists_ok_resp, {
                assert forall |ex| #[trigger] exists_ok_resp.satisfied_by(ex) implies tla_exists(known_ok_resp).satisfied_by(ex) by {
                    let resp_msg = choose |resp_msg| {
                        &&& #[trigger] ex.head().in_flight().contains(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0)
                        &&& resp_msg.content.get_update_response().res is Ok
                        &&& state_after_update(sub_resource, rabbitmq, resp_msg.content.get_update_response().res->Ok_0, RabbitmqReconcileState::unmarshal(ex.head().ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state).unwrap()) is Ok
                    };
                    assert(known_ok_resp(resp_msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(known_ok_resp), exists_ok_resp);
            });
            entails_implies_leads_to(spec, match_and_ok_resp, exists_ok_resp);
            leads_to_trans_n!(spec, pre, match_and_ok_resp, exists_ok_resp, lift_state(next_state));
        });
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_from_key_not_exists_to_receives_not_found_resp_at_after_get_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        spec.entails(always(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                    &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
                }
            ).leads_to(lift_state(
                |s: ClusterState| {
                    &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                    &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, rabbitmq, controller_id)(s)
                }
            ))
        ),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let pre = |s: ClusterState| {
        &&& !s.resources().contains_key(resource_key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
    };
    let post = |s: ClusterState| {
        &&& !s.resources().contains_key(resource_key)
        &&& at_after_get_resource_step_and_exists_not_found_resp_in_flight(sub_resource, rabbitmq, controller_id)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)),
        lift_state(rmq_rely_conditions(cluster, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                if input->0 == req_msg {
                    assert(post(s_prime));
                } else {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                        s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0
                    );
                }
            },
            _ => {}
        }
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let resp_msg = handle_get_request_msg(req_msg, s.api_server).1;
        assert({
            &&& s_prime.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg.content.get_get_response().res is Err
            &&& resp_msg.content.get_get_response().res->Err_0 is ObjectNotFound
        });
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

proof fn lemma_from_after_get_resource_step_to_after_create_resource_step_by_controller(
    controller_id: int,  cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: Message,
    s: ClusterState, s_prime: ClusterState
)
requires
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(rabbitmq.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s),
    resp_msg.content.get_get_response().res is Err,
    resp_msg.content.get_get_response().res->Err_0 is ObjectNotFound,
    !s.resources().contains_key(get_request(sub_resource, rabbitmq).key),
ensures
    pending_req_in_flight_at_after_create_resource_step(sub_resource, rabbitmq, controller_id)(s_prime),
    !s_prime.resources().contains_key(get_request(sub_resource, rabbitmq).key),
{
    RabbitmqReconcileState::marshal_preserves_integrity();
    match sub_resource {
        SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
        SubResource::Service => ServiceView::marshal_preserves_integrity(),
        SubResource::ErlangCookieSecret => SecretView::marshal_preserves_integrity(),
        SubResource::DefaultUserSecret => SecretView::marshal_preserves_integrity(),
        SubResource::PluginsConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServerConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServiceAccount => ServiceAccountView::marshal_preserves_integrity(),
        SubResource::Role => RoleView::marshal_preserves_integrity(),
        SubResource::RoleBinding => RoleBindingView::marshal_preserves_integrity(),
        SubResource::VStatefulSetView => VStatefulSetView::marshal_preserves_integrity(),
    }
    let step = after_create_k_request_step(sub_resource);
    let msg = s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
    let req = msg.content.get_create_request();
    assert(at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s_prime));
    assert(Cluster::has_pending_k8s_api_req_msg(controller_id, s_prime, rabbitmq.object_ref()));
    assert(s_prime.in_flight().contains(msg));
    assert(msg.src == HostId::Controller(controller_id, rabbitmq.object_ref()));
    assert(resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
    assert(req_obj_matches_sub_resource_requirements(sub_resource, rabbitmq, msg.content.get_create_request().obj)(s_prime)) by {
        let obj = msg.content.get_create_request().obj;
        if sub_resource == SubResource::VStatefulSetView {
            let cm_key = make_server_config_map_key(rabbitmq);
            let cm_obj = s.resources()[cm_key];
            let made_sts = make_sts_pass_state_validation(rabbitmq, int_to_string_view(cm_obj.metadata.resource_version->0));
            let req_obj_spec = VStatefulSetView::unmarshal(obj)->Ok_0.spec;
            assert(VStatefulSetView::unmarshal(obj) is Ok);
            assert(VStatefulSetView::unmarshal(obj)->Ok_0.state_validation());
            assert(obj.metadata.labels == made_sts.metadata.labels);
            assert(obj.metadata.annotations == made_sts.metadata.annotations);
            assert(req_obj_spec.template == made_sts.spec.template);
        }
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_from_after_get_resource_step_to_after_create_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        spec.entails(always(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(
            lift_state(|s: ClusterState| {
                &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s)
                &&& resp_msg.content.get_get_response().res is Err
                &&& resp_msg.content.get_get_response().res->Err_0 is ObjectNotFound
            }).leads_to(lift_state(|s: ClusterState| {
                &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, rabbitmq, controller_id)(s)
            }))
        ),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let pre = |s: ClusterState| {
        &&& !s.resources().contains_key(resource_key)
        &&& resp_msg_is_the_in_flight_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s)
        &&& resp_msg.content.get_get_response().res is Err
        &&& resp_msg.content.get_get_response().res->Err_0 is ObjectNotFound
    };
    let post = |s: ClusterState| {
        &&& !s.resources().contains_key(resource_key)
        &&& pending_req_in_flight_at_after_create_resource_step(sub_resource, rabbitmq, controller_id)(s)
    };
    let key = rabbitmq.object_ref();
    let input = (Some(resp_msg), Some(key));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)),
        lift_state(rmq_rely_conditions(cluster, controller_id))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                    s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0
                );
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.2 == Some(key) {
                    lemma_from_after_get_resource_step_to_after_create_resource_step_by_controller(
                        controller_id, cluster, sub_resource, rabbitmq, resp_msg, s, s_prime
                    );
                }
            }
            _ => {}
        }
    }

    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

proof fn lemma_resource_state_matches_at_after_create_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        spec.entails(always(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(
            lift_state(
                |s: ClusterState| {
                    &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
                    &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
                }
            ).leads_to(
                lift_state(resource_state_matches(sub_resource, rabbitmq))
                .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)))
            )
        ),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let pre = |s: ClusterState| {
        &&& !s.resources().contains_key(resource_key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
    };
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)),
        lift_state(rmq_rely_conditions(cluster, controller_id))
    );

    let post = |s: ClusterState| {
        &&& resource_state_matches(sub_resource, rabbitmq)(s)
        &&& at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)(s)
    };

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let pending_msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let resp = lemma_create_sub_resource_request_returns_ok(
            s, s_prime, rabbitmq, cluster, controller_id, sub_resource, pending_msg
        );
        assert(s_prime.in_flight().contains(resp));
    }

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                if msg.src != HostId::Controller(controller_id, rabbitmq.object_ref()) {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
                        s, s_prime, rabbitmq, cluster, controller_id, sub_resource, msg
                    );
                    assert(pre(s_prime));
                } else {
                    lemma_create_sub_resource_request_returns_ok(
                        s, s_prime, rabbitmq, cluster, controller_id, sub_resource, msg
                    );
                    assert(post(s_prime));
                }
            },
            _ => {},
        }
    }

    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
    temp_pred_equality(
        lift_state(post),
        lift_state(resource_state_matches(sub_resource, rabbitmq))
            .and(lift_state(at_after_create_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)))
    );
}

proof fn lemma_from_key_exists_to_receives_ok_resp_at_after_get_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        // sub_resource != SubResource::VStatefulSetView,
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)))),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, rabbitmq, controller_id, req_msg))
                .leads_to(lift_state(at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)))
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(sub_resource, rabbitmq, controller_id, req_msg);
    let post = at_after_get_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id);
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)(s)
        &&& helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)),
        lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let req = input->0;
                assert(!resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(req));
                assert(!resource_delete_request_msg(get_request(sub_resource, rabbitmq).key)(req));
                assert(!resource_update_status_request_msg(get_request(sub_resource, rabbitmq).key)(req));
                if input->0 == req_msg {
                    let resp_msg = handle_get_request_msg(req_msg, s.api_server).1;
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
        let resp_msg = handle_get_request_msg(req_msg, s.api_server).1;
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
#[verifier(rlimit(100))]
proof fn lemma_resource_state_matches_at_after_update_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: Message
)
    requires
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        spec.entails(always(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures
        spec.entails(
            lift_state(req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, req_msg))
                .leads_to(
                    lift_state(resource_state_matches(sub_resource, rabbitmq))
                        .and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)))
                )
        ),
{
    let pre = req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rabbitmq, controller_id, req_msg);
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let input = Some(req_msg);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)),
        lift_state(rmq_rely_conditions(cluster, controller_id))
    );

    let post = |s: ClusterState| {
        &&& resource_state_matches(sub_resource, rabbitmq)(s)
        &&& at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)(s)
    };

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let resp_msg = lemma_update_sub_resource_request_returns_ok(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, req_msg);
        assert(s_prime.in_flight().contains(resp_msg));
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                if input->0 != req_msg {
                    lemma_api_request_other_than_pending_req_msg_maintains_resource_object(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0);
                } else {
                    let resp_msg = lemma_update_sub_resource_request_returns_ok(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, req_msg);
                    assert(s_prime.in_flight().contains(resp_msg));
                }
            },
            _ => {},
        }
    }

    cluster.lemma_pre_leads_to_post_by_api_server(spec, input, stronger_next, APIServerStep::HandleRequest, pre, post);
    temp_pred_equality(
        lift_state(post),
        lift_state(resource_state_matches(sub_resource, rabbitmq))
            .and(lift_state(at_after_update_resource_step_and_exists_ok_resp_in_flight(sub_resource, rabbitmq, controller_id)))
    );
}

proof fn lemma_from_after_get_resource_step_to_after_update_resource_step_by_controller(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: Message,
    s: ClusterState, s_prime: ClusterState
)
requires
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(rabbitmq.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg)(s),
ensures
    pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq, controller_id)(s_prime),
{
    RabbitmqReconcileState::marshal_preserves_integrity();
    match sub_resource {
        SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
        SubResource::Service => ServiceView::marshal_preserves_integrity(),
        SubResource::ErlangCookieSecret => SecretView::marshal_preserves_integrity(),
        SubResource::DefaultUserSecret => SecretView::marshal_preserves_integrity(),
        SubResource::PluginsConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServerConfigMap => ConfigMapView::marshal_preserves_integrity(),
        SubResource::ServiceAccount => ServiceAccountView::marshal_preserves_integrity(),
        SubResource::Role => RoleView::marshal_preserves_integrity(),
        SubResource::RoleBinding => RoleBindingView::marshal_preserves_integrity(),
        SubResource::VStatefulSetView => VStatefulSetView::marshal_preserves_integrity(),
    }
    assert(s.resources() == s_prime.resources());
    let step = after_update_k_request_step(sub_resource);
    let msg = s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
    let req = msg.content.get_update_request();
    let returned_obj = resp_msg.content.get_get_response().res->Ok_0;
    assert(req_obj_matches_sub_resource_requirements(sub_resource, rabbitmq, msg.content.get_update_request().obj)(s_prime)) by {
        let obj = req.obj;
        assert(returned_obj.metadata.owner_references == Some(make_owner_references(rabbitmq)));
        if sub_resource == SubResource::VStatefulSetView {
            let cm_key = make_server_config_map_key(rabbitmq);
            let cm_obj = s.resources()[cm_key];
            assert(returned_obj == s.resources()[returned_obj.object_ref()]);
            let found_sts = VStatefulSetView::unmarshal(returned_obj).unwrap();
            let updated_sts = update_sts_pass_state_validation(rabbitmq, found_sts, int_to_string_view(cm_obj.metadata.resource_version->0));
            assert(updated_sts.state_validation());
        }
    }
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(500))]
proof fn lemma_from_after_get_resource_step_to_after_update_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: Message
)
    requires
        // sub_resource != SubResource::VStatefulSetView,
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)))),
        spec.entails(always(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(
            lift_state(resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg))
                .leads_to(lift_state(pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq, controller_id)))
        ),
{
    let pre = resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, resp_msg);
    let post = pending_req_in_flight_at_after_update_resource_step(sub_resource, rabbitmq, controller_id);
    let input = (Some(resp_msg), Some(rabbitmq.object_ref()));
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)(s)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, sub_resource)),
        lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)),
        lift_state(rmq_rely_conditions(cluster, controller_id))
    );

    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                lemma_api_request_other_than_pending_req_msg_maintains_resource_object(s, s_prime, rabbitmq, cluster, controller_id, sub_resource, input->0);
            },
            Step::ControllerStep(input) => {
                if input.0 == controller_id && input.2 == Some(rabbitmq.object_ref()) {
                    lemma_from_after_get_resource_step_to_after_update_resource_step_by_controller(
                        controller_id, cluster, spec, sub_resource, rabbitmq, resp_msg, s, s_prime
                    );
                } else {
                    assert(pre(s_prime));
                }
            }
            _ => {},
        }
    }

    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next,
        ControllerStep::ContinueReconcile, pre, post
    );
}

pub proof fn lemma_resource_object_is_stable(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, p: TempPred<ClusterState>
)
    requires
        // sub_resource != SubResource::VStatefulSetView,
        spec.entails(p.leads_to(lift_state(resource_state_matches(sub_resource, rabbitmq)))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)))),
    ensures spec.entails(p.leads_to(always(lift_state(resource_state_matches(sub_resource, rabbitmq))))),
{
    let post = resource_state_matches(sub_resource, rabbitmq);
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)(s)
        &&& helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)(s)
        &&& helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)(s)
        &&& helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)(s)
        &&& helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(helper_invariants::no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)),
        lift_state(helper_invariants::every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)),
        lift_state(helper_invariants::no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)),
        lift_state(helper_invariants::resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)),
        lift_state(helper_invariants::object_in_etcd_satisfies_unchangeable(sub_resource, rabbitmq))
    );

    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let req = input->0;
                assert(!resource_delete_request_msg(get_request(sub_resource, rabbitmq).key)(req));
                assert(!resource_update_status_request_msg(get_request(sub_resource, rabbitmq).key)(req));
                if resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(req) {} else {}
            },
            _ => {},
        }
        match sub_resource {
            SubResource::HeadlessService => ServiceView::marshal_preserves_integrity(),
            SubResource::Service => ServiceView::marshal_preserves_integrity(),
            SubResource::ErlangCookieSecret => SecretView::marshal_preserves_integrity(),
            SubResource::DefaultUserSecret => SecretView::marshal_preserves_integrity(),
            SubResource::PluginsConfigMap => ConfigMapView::marshal_preserves_integrity(),
            SubResource::ServerConfigMap => ConfigMapView::marshal_preserves_integrity(),
            SubResource::ServiceAccount => ServiceAccountView::marshal_preserves_integrity(),
            SubResource::Role => RoleView::marshal_preserves_integrity(),
            SubResource::RoleBinding => RoleBindingView::marshal_preserves_integrity(),
            _ => {}
        }
    }

    leads_to_stable(spec, lift_action(stronger_next), p, lift_state(post));
}

}
