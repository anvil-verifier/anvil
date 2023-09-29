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

// Thie file proves in a control flow pattern where the reconciler gets a type of resource, then creates/updates the resource,
// the system will reach the desired state for that resource and the reconciler enters the next state--get the next resource.
// proof fn lemma_from_after_get_resource_step_to_resource_matches(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, sub_resource: SubResource)
//     requires
//         rabbitmq.well_formed(),
//     ensures
//         spec.entails(
//             lift_state(pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq))
//                 .leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))
//         ),
// {
//     lemma_from_after_get_resource_step_and_key_not_exists_to_resource_matches(spec, rabbitmq);
//     lemma_from_after_get_resource_step_map_and_key_exists_to_resource_matches(spec, rabbitmq);
//     let key_not_exists = |s: RMQCluster| {
//         &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//         &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq)(s)
//     };
//     let key_exists = |s: RMQCluster| {
//         &&& !s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//         &&& pending_req_in_flight_at_after_get_resource_step(sub_resource, rabbitmq)(s)
//     };
//     or_leads_to_combine(spec, key_not_exists, key_exists, resource_state_matches(sub_resource, rabbitmq));
//     temp_pred_equality(
//         lift_state(key_not_exists).or(lift_state(key_exists)),
//         lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(after_get_k_request_step(sub_resource), rabbitmq))
//     );
// }

proof fn lemma_from_after_get_source_step_and_key_not_exists_to_resource_matches(
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
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(helper_invariants::every_resource_object_in_create_request_matches(sub_resource, rabbitmq)))),
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
        spec.entails(always(lift_state(helper_invariants::every_resource_object_in_create_request_matches(sub_resource, rabbitmq)))),
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
        &&& helper_invariants::every_resource_object_in_create_request_matches(sub_resource, rabbitmq)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_object_in_create_request_matches(sub_resource, rabbitmq))
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

// proof fn lemma_from_after_get_resource_step_and_key_exists_to_resource_matches(rabbitmq: RabbitmqClusterView)
//     requires
//         rabbitmq.well_formed(),
//     ensures
//         assumption_and_invariants_of_all_phases(rabbitmq)
//         .entails(
//             lift_state(|s: RMQCluster| {
//                 &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                 &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
//             }).leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))
//         ),
//         assumption_and_invariants_of_all_phases(rabbitmq)
//         .entails(
//             lift_state(|s: RMQCluster| {
//                 &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                 &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
//             }).leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServiceAccount, rabbitmq)))
//         ),
// {
//     let spec = assumption_and_invariants_of_all_phases(rabbitmq);
//     let pre = lift_state(|s: RMQCluster| {
//         &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//         &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
//     });
//     let pre_with_object = |object| lift_state(
//         |s: RMQCluster| {
//             &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//             &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//             &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
//         }
//     );
//     let post_with_object = |object| lift_state(
//         |s: RMQCluster| {
//             &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//             &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//             &&& pending_req_with_object_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, object)(s)
//         }
//     );
//     assert forall |object: DynamicObjectView| spec.entails(#[trigger] pre_with_object(object).leads_to(post_with_object(object))) by
//     {
//         let p1 = lift_state(|s: RMQCluster| {
//             &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//             &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//             &&& pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq)(s)
//         });
//         let p2 = lift_state(|s: RMQCluster| {
//             &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//             &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//             &&& pending_req_with_object_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, object)(s)
//         });

//         assert_by(
//             spec.entails(p1.leads_to(p2)),
//             {
//                 let pre_and_req_in_flight = |req_msg| lift_state(
//                     |s: RMQCluster| {
//                         &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                         &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//                         &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg)(s)
//                     }
//                 );
//                 let pre_and_exists_resp_in_flight = lift_state(
//                     |s: RMQCluster| {
//                         &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                         &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//                         &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_ok_resp_in_flight(rabbitmq, object)(s)
//                     }
//                 );
//                 let pre_and_resp_in_flight = |resp_msg| lift_state(
//                     |s: RMQCluster| {
//                         &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                         &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//                         &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg)(s)
//                         &&& resp_msg.content.get_get_response().res.is_Ok()
//                         &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
//                     }
//                 );

//                 assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(pre_and_exists_resp_in_flight))
//                 by {
//                     lemma_receives_ok_resp_at_after_get_server_config_map_step_with_rabbitmq(spec, rabbitmq, req_msg, object);
//                 }
//                 leads_to_exists_intro(spec, pre_and_req_in_flight, pre_and_exists_resp_in_flight);
//                 assert_by(
//                     tla_exists(pre_and_req_in_flight) == p1,
//                     {
//                         assert forall |ex| #[trigger] p1.satisfied_by(ex)
//                         implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
//                             let req_msg = ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
//                             assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
//                         }
//                         temp_pred_equality(tla_exists(pre_and_req_in_flight), p1);
//                     }
//                 );

//                 assert forall |resp_msg| spec.entails(#[trigger] pre_and_resp_in_flight(resp_msg).leads_to(p2))
//                 by {
//                     lemma_from_after_get_server_config_map_step_to_after_update_server_config_map_step(spec, rabbitmq, resp_msg, object);
//                 }
//                 leads_to_exists_intro(spec, pre_and_resp_in_flight, p2);
//                 assert_by(
//                     tla_exists(pre_and_resp_in_flight) == pre_and_exists_resp_in_flight,
//                     {
//                         assert forall |ex| #[trigger] pre_and_exists_resp_in_flight.satisfied_by(ex)
//                         implies tla_exists(pre_and_resp_in_flight).satisfied_by(ex) by {
//                             let resp_msg = choose |resp_msg| {
//                                 &&& #[trigger] ex.head().in_flight().contains(resp_msg)
//                                 &&& Message::resp_msg_matches_req_msg(resp_msg, ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
//                                 &&& resp_msg.content.get_get_response().res.is_Ok()
//                                 &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
//                             };
//                             assert(pre_and_resp_in_flight(resp_msg).satisfied_by(ex));
//                         }
//                         temp_pred_equality(tla_exists(pre_and_resp_in_flight), pre_and_exists_resp_in_flight);
//                     }
//                 );

//                 leads_to_trans_temp(spec, p1, pre_and_exists_resp_in_flight, p2);
//             }
//         );
//     }
//     assert forall |object: DynamicObjectView| spec.entails(#[trigger] pre_with_object(object).leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))) by {
//         assert(spec.entails(pre_with_object(object).leads_to(post_with_object(object))));
//         assert_by(
//             spec.entails(post_with_object(object).leads_to(lift_state(current_state_matches(sub_resource, rabbitmq)))),
//             {
//                 let pre_and_req_in_flight = |req_msg| lift_state(
//                     |s: RMQCluster| {
//                         &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                         &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//                         &&& req_msg_is_the_in_flight_pending_req_with_object_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, req_msg, object)(s)
//                     }
//                 );
//                 assert forall |req_msg| spec.entails(#[trigger] pre_and_req_in_flight(req_msg).leads_to(lift_state(current_state_matches(sub_resource, rabbitmq))))
//                 by {
//                     lemma_cm_is_updated_at_after_update_server_config_map_step_with_rabbitmq(spec, rabbitmq, req_msg, object);
//                 }
//                 leads_to_exists_intro(spec, pre_and_req_in_flight, lift_state(current_state_matches(sub_resource, rabbitmq)));
//                 assert_by(
//                     tla_exists(pre_and_req_in_flight) == post_with_object(object),
//                     {
//                         assert forall |ex| #[trigger] post_with_object(object).satisfied_by(ex)
//                         implies tla_exists(pre_and_req_in_flight).satisfied_by(ex) by {
//                             let req_msg = ex.head().ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
//                             assert(pre_and_req_in_flight(req_msg).satisfied_by(ex));
//                         }
//                         temp_pred_equality(tla_exists(pre_and_req_in_flight), post_with_object(object));
//                     }
//                 );
//             }
//         );
//         leads_to_trans_temp(spec, pre_with_object(object), post_with_object(object), lift_state(current_state_matches(sub_resource, rabbitmq)));
//     }
//     assert forall |object: DynamicObjectView| spec.entails(#[trigger] pre_with_object(object).leads_to(lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServiceAccount, rabbitmq)))) by {
//         valid_implies_implies_leads_to(spec, post_with_object(object), lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq)));
//         lemma_from_pending_req_in_flight_at_some_step_to_pending_req_in_flight_at_next_step(spec, rabbitmq, RabbitmqReconcileStep::AfterUpdateServerConfigMap, RabbitmqReconcileStep::AfterCreateServiceAccount);
//         leads_to_trans_n!(
//             spec, pre_with_object(object), post_with_object(object),
//             lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq)),
//             lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServiceAccount, rabbitmq))
//         );
//     }
//     leads_to_exists_intro(spec, pre_with_object, lift_state(current_state_matches(sub_resource, rabbitmq)));
//     leads_to_exists_intro(spec, pre_with_object, lift_state(pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterCreateServiceAccount, rabbitmq)));
//     assert_by(
//         tla_exists(pre_with_object) == pre,
//         {
//             assert forall |ex| #[trigger] pre.satisfied_by(ex)
//             implies tla_exists(pre_with_object).satisfied_by(ex) by {
//                 let object = ex.head().resources()[get_request(sub_resource, rabbitmq).key];
//                 assert(pre_with_object(object).satisfied_by(ex));
//             }
//             temp_pred_equality(tla_exists(pre_with_object), pre);
//         }
//     );
// }

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
        spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(helper_invariants::every_resource_object_in_create_request_matches(sub_resource, rabbitmq)))),
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
        &&& RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())(s)
        &&& RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())(s)
        &&& helper_invariants::every_resource_object_in_create_request_matches(sub_resource, rabbitmq)(s)
        &&& helper_invariants::cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
        lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
        lift_state(helper_invariants::every_resource_object_in_create_request_matches(sub_resource, rabbitmq)),
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
        spec.entails(always(lift_state(helper_invariants::every_resource_object_in_create_request_matches(sub_resource, rabbitmq)))),
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
        &&& helper_invariants::every_resource_object_in_create_request_matches(sub_resource, rabbitmq)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::crash_disabled()),
        lift_state(RMQCluster::busy_disabled()),
        lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
        lift_state(helper_invariants::every_resource_object_in_create_request_matches(sub_resource, rabbitmq))
    );

    RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, RMQCluster::handle_request(), pre, current_state_matches(sub_resource, rabbitmq)
    );
}

// proof fn lemma_receives_ok_resp_at_after_get_server_config_map_step_with_rabbitmq(
//     spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage, object: DynamicObjectView
// )
//     requires
//         spec.entails(always(lift_action(RMQCluster::next()))),
//         spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
//         spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
//         spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
//         spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
//         spec.entails(always(lift_state(helper_invariants::update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(rabbitmq.object_ref())))),
//         spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
//         rabbitmq.well_formed(),
//     ensures
//         spec.entails(
//             lift_state(
//                 |s: RMQCluster| {
//                     &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                     &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//                     &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg)(s)
//                 }
//             ).leads_to(lift_state(
//                 |s: RMQCluster| {
//                     &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                     &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//                     &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_ok_resp_in_flight(rabbitmq, object)(s)
//                 }
//             ))
//         ),
// {
//     let pre = |s: RMQCluster| {
//         &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//         &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//         &&& req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, req_msg)(s)
//     };
//     let post = |s: RMQCluster| {
//         &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//         &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//         &&& at_after_get_server_config_map_step_with_rabbitmq_and_exists_ok_resp_in_flight(rabbitmq, object)(s)
//     };
//     let input = Some(req_msg);
//     let stronger_next = |s, s_prime: RMQCluster| {
//         &&& RMQCluster::next()(s, s_prime)
//         &&& RMQCluster::crash_disabled()(s)
//         &&& RMQCluster::busy_disabled()(s)
//         &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
//         &&& helper_invariants::update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(rabbitmq.object_ref())(s)
//         &&& helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)(s)
//     };
//     combine_spec_entails_always_n!(
//         spec, lift_action(stronger_next),
//         lift_action(RMQCluster::next()),
//         lift_state(RMQCluster::crash_disabled()),
//         lift_state(RMQCluster::busy_disabled()),
//         lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
//         lift_state(helper_invariants::update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(rabbitmq.object_ref())),
//         lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key))
//     );

//     assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
//         let step = choose |step| RMQCluster::next_step(s, s_prime, step);
//         match step {
//             Step::KubernetesAPIStep(input) => {
//                 if input.get_Some_0() == req_msg {
//                     let resp_msg = RMQCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
//                     assert({
//                         &&& s_prime.in_flight().contains(resp_msg)
//                         &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
//                         &&& resp_msg.content.get_get_response().res.is_Ok()
//                         &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
//                     });
//                 }
//             },
//             _ => {}
//         }
//     }

//     assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime)
//     implies post(s_prime) by {
//         let resp_msg = RMQCluster::handle_get_request(req_msg, s.kubernetes_api_state).1;
//         assert({
//             &&& s_prime.in_flight().contains(resp_msg)
//             &&& Message::resp_msg_matches_req_msg(resp_msg, req_msg)
//             &&& resp_msg.content.get_get_response().res.is_Ok()
//             &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
//         });
//     }

//     RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
//         spec, input, stronger_next, RMQCluster::handle_request(), pre, post
//     );
// }

// proof fn lemma_cm_is_updated_at_after_update_server_config_map_step_with_rabbitmq(
//     spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage, object: DynamicObjectView
// )
//     requires
//         spec.entails(always(lift_action(RMQCluster::next()))),
//         spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
//         spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
//         spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
//         spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
//         spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
//         spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
//         spec.entails(always(lift_state(helper_invariants::update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(rabbitmq.object_ref())))),
//         spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
//         spec.entails(always(lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq)))),
//         rabbitmq.well_formed(),
//     ensures
//         spec.entails(
//             lift_state(
//                 |s: RMQCluster| {
//                     &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                     &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//                     &&& req_msg_is_the_in_flight_pending_req_with_object_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, req_msg, object)(s)
//                 }
//             )
//             .leads_to(lift_state(
//                 |s: RMQCluster| {
//                     &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                     &&& ConfigMapView::unmarshal(s.resources()[get_request(sub_resource, rabbitmq).key]).is_Ok()
//                     &&& ConfigMapView::unmarshal(s.resources()[get_request(sub_resource, rabbitmq).key]).get_Ok_0().data == make_server_config_map(rabbitmq).data
//                 }
//             ))
//         ),
// {
//     let pre = |s: RMQCluster| {
//         &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//         &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//         &&& req_msg_is_the_in_flight_pending_req_with_object_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, req_msg, object)(s)
//     };
//     let post = |s: RMQCluster| {
//         &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//         &&& ConfigMapView::unmarshal(s.resources()[get_request(sub_resource, rabbitmq).key]).is_Ok()
//         &&& ConfigMapView::unmarshal(s.resources()[get_request(sub_resource, rabbitmq).key]).get_Ok_0().data == make_server_config_map(rabbitmq).data
//     };
//     let input = Some(req_msg);
//     let stronger_next = |s, s_prime: RMQCluster| {
//         &&& RMQCluster::next()(s, s_prime)
//         &&& RMQCluster::crash_disabled()(s)
//         &&& RMQCluster::busy_disabled()(s)
//         &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
//         &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
//         &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
//         &&& helper_invariants::update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(rabbitmq.object_ref())(s)
//         &&& helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)(s)
//         &&& helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq)(s)
//     };
//     combine_spec_entails_always_n!(
//         spec, lift_action(stronger_next),
//         lift_action(RMQCluster::next()),
//         lift_state(RMQCluster::crash_disabled()),
//         lift_state(RMQCluster::busy_disabled()),
//         lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
//         lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
//         lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
//         lift_state(helper_invariants::update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(rabbitmq.object_ref())),
//         lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)),
//         lift_state(helper_invariants::object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(get_request(sub_resource, rabbitmq).key, rabbitmq))
//     );

//     assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
//         let step = choose |step| RMQCluster::next_step(s, s_prime, step);
//         match step {
//             Step::KubernetesAPIStep(input) => {
//                 ConfigMapView::marshal_spec_preserves_integrity();
//             },
//             _ => {}
//         }
//     }

//     assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && RMQCluster::kubernetes_api_next().forward(input)(s, s_prime)
//     implies post(s_prime) by {
//         ConfigMapView::marshal_spec_preserves_integrity();
//     }

//     RMQCluster::lemma_pre_leads_to_post_by_kubernetes_api(
//         spec, input, stronger_next, RMQCluster::handle_request(), pre, post
//     );
// }

// proof fn lemma_from_after_get_server_config_map_step_to_after_update_server_config_map_step(
//     spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView, resp_msg: RMQMessage, object: DynamicObjectView
// )
//     requires
//         spec.entails(always(lift_action(RMQCluster::next()))),
//         spec.entails(tla_forall(|i| RMQCluster::controller_next().weak_fairness(i))),
//         spec.entails(always(lift_state(RMQCluster::crash_disabled()))),
//         spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
//         spec.entails(always(lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())))),
//         spec.entails(always(lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())))),
//         spec.entails(always(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))),
//         spec.entails(always(lift_state(RMQCluster::every_in_flight_msg_has_unique_id()))),
//         spec.entails(always(lift_state(helper_invariants::update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(rabbitmq.object_ref())))),
//         spec.entails(always(lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)))),
//         rabbitmq.well_formed(),
//     ensures
//         spec.entails(
//             lift_state(|s: RMQCluster| {
//                 &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                 &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//                 &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg)(s)
//                 &&& resp_msg.content.get_get_response().res.is_Ok()
//                 &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
//             })
//                 .leads_to(lift_state(|s: RMQCluster| {
//                     &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//                     &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//                     &&& pending_req_with_object_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, object)(s)
//                 }))
//         ),
// {
//     let pre = |s: RMQCluster| {
//         &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//         &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//         &&& resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterGetServerConfigMap, rabbitmq, resp_msg)(s)
//         &&& resp_msg.content.get_get_response().res.is_Ok()
//         &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
//     };
//     let post = |s: RMQCluster| {
//         &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
//         &&& s.resources()[get_request(sub_resource, rabbitmq).key] == object
//         &&& pending_req_with_object_in_flight_at_rabbitmq_step_with_rabbitmq(RabbitmqReconcileStep::AfterUpdateServerConfigMap, rabbitmq, object)(s)
//     };
//     let input = (Some(resp_msg), Some(rabbitmq.object_ref()));
//     let stronger_next = |s, s_prime: RMQCluster| {
//         &&& RMQCluster::next()(s, s_prime)
//         &&& RMQCluster::crash_disabled()(s)
//         &&& RMQCluster::busy_disabled()(s)
//         &&& RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())(s)
//         &&& RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())(s)
//         &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
//         &&& RMQCluster::every_in_flight_msg_has_unique_id()(s)
//         &&& helper_invariants::update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(rabbitmq.object_ref())(s)
//         &&& helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key)(s)
//     };

//     combine_spec_entails_always_n!(
//         spec, lift_action(stronger_next),
//         lift_action(RMQCluster::next()),
//         lift_state(RMQCluster::crash_disabled()),
//         lift_state(RMQCluster::busy_disabled()),
//         lift_state(RMQCluster::each_resp_matches_at_most_one_pending_req(rabbitmq.object_ref())),
//         lift_state(RMQCluster::each_resp_if_matches_pending_req_then_no_other_resp_matches(rabbitmq.object_ref())),
//         lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
//         lift_state(RMQCluster::every_in_flight_msg_has_unique_id()),
//         lift_state(helper_invariants::update_server_cm_req_msg_in_flight_implies_at_after_update_server_cm_step(rabbitmq.object_ref())),
//         lift_state(helper_invariants::no_delete_request_msg_in_flight_with_key(get_request(sub_resource, rabbitmq).key))
//     );

//     RMQCluster::lemma_pre_leads_to_post_by_controller(
//         spec, input, stronger_next,
//         RMQCluster::continue_reconcile(), pre, post
//     );
// }

}
