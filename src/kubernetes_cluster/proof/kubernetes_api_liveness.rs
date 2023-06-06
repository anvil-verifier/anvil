// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, dynamic::*, error::*, resource::*};
use crate::kubernetes_cluster::{
    proof::wf1_assistant::kubernetes_api_action_pre_implies_next_pre,
    spec::{
        distributed_system::*,
        kubernetes_api::common::KubernetesAPIAction,
        kubernetes_api::state_machine::{handle_request, kubernetes_api},
        message::*,
    },
};
use crate::pervasive_ext::multiset_lemmas::*;
use crate::reconciler::spec::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::assert_multisets_equal;
use vstd::prelude::*;

verus! {

pub proof fn lemma_pre_leads_to_post_by_kubernetes_api<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, input: Option<Message>, next: ActionPred<State<K, T>>, action: KubernetesAPIAction, pre: StatePred<State<K, T>>, post: StatePred<State<K, T>>)
    requires
        kubernetes_api().actions.contains(action),
        forall |s, s_prime: State<K, T>| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<K, T>| pre(s) && #[trigger] next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<K, T>| #[trigger] pre(s) ==> kubernetes_api_action_pre(action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<K, T>, Option<Message>>(spec, |i| kubernetes_api_next().weak_fairness(i), input);

    kubernetes_api_action_pre_implies_next_pre::<K, T>(action, input);
    valid_implies_trans::<State<K, T>>(lift_state(pre), lift_state(kubernetes_api_action_pre(action, input)), lift_state(kubernetes_api_next().pre(input)));

    kubernetes_api_next().wf1(input, spec, next, pre, post);
}

pub proof fn lemma_pre_leads_to_post_with_assumption_by_kubernetes_api<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, input: Option<Message>, next: ActionPred<State<K, T>>, action: KubernetesAPIAction, assumption: StatePred<State<K, T>>, pre: StatePred<State<K, T>>, post: StatePred<State<K, T>>)
    requires
        kubernetes_api().actions.contains(action),
        forall |s, s_prime: State<K, T>| pre(s) && #[trigger] next(s, s_prime) && assumption(s) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<K, T>| pre(s) && #[trigger] next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<K, T>| #[trigger] pre(s) ==> kubernetes_api_action_pre(action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(lift_state(pre).and(always(lift_state(assumption))).leads_to(lift_state(post))),
{
    use_tla_forall::<State<K, T>, Option<Message>>(spec, |i| kubernetes_api_next().weak_fairness(i), input);

    kubernetes_api_action_pre_implies_next_pre::<K, T>(action, input);
    valid_implies_trans::<State<K, T>>(lift_state(pre), lift_state(kubernetes_api_action_pre(action, input)), lift_state(kubernetes_api_next().pre(input)));

    kubernetes_api_next().wf1_assume(input, spec, next, assumption, pre, post);
}

pub proof fn lemma_get_req_leads_to_some_resp<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, msg: Message, key: ObjectRef
)
    requires
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<K, T>| {
                    &&& s.message_in_flight(msg)
                    &&& msg.dst == HostId::KubernetesAPI
                    &&& msg.content.is_get_request()
                    &&& msg.content.get_get_request().key == key
                })
                .leads_to(
                    lift_state(|s: State<K, T>|
                        exists |resp_msg: Message| {
                            &&& #[trigger] s.message_in_flight(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, msg)
                        }
                    )
                )
        ),
{
    let input = Option::Some(msg);
    let pre = |s: State<K, T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_get_request()
        &&& msg.content.get_get_request().key == key
    };
    let post = |s: State<K, T>| exists |resp_msg: Message| {
        &&& #[trigger] s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
    };
    assert forall |s, s_prime: State<K, T>| pre(s) && #[trigger] next::<K, T, ReconcilerType>()(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        if s.resource_key_exists(key) {
            let ok_resp_msg = form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)));
            assert(s_prime.message_in_flight(ok_resp_msg));
            assert(resp_msg_matches_req_msg(ok_resp_msg, msg));
        } else {
            let err_resp_msg = form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound));
            assert(s_prime.message_in_flight(err_resp_msg));
            assert(resp_msg_matches_req_msg(err_resp_msg, msg));
        }
    };
    lemma_pre_leads_to_post_by_kubernetes_api::<K, T, ReconcilerType>(spec, input, next::<K, T, ReconcilerType>(), handle_request(), pre, post);
}

pub proof fn lemma_get_req_leads_to_ok_or_err_resp<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, msg: Message, key: ObjectRef
)
    requires
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<K, T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.content.is_get_request()
                &&& msg.content.get_get_request().key == key
            })
                .leads_to(
                    lift_state(|s: State<K, T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)))))
                    .or(lift_state(|s: State<K, T>| s.message_in_flight(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))))
                )
        ),
{
    let pre = |s: State<K, T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_get_request()
        &&& msg.content.get_get_request().key == key
    };
    let post = |s: State<K, T>| {
        ||| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key))))
        ||| s.message_in_flight(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))
    };
    lemma_pre_leads_to_post_by_kubernetes_api::<K, T, ReconcilerType>(spec, Option::Some(msg), next::<K, T, ReconcilerType>(), handle_request(), pre, post);
    temp_pred_equality::<State<K, T>>(
        lift_state(post),
        lift_state(|s: State<K, T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)))))
        .or(lift_state(|s: State<K, T>| s.message_in_flight(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))))
    );
}

pub proof fn lemma_create_req_leads_to_res_exists<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, msg: Message
)
    requires
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<K, T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.content.is_create_request()
                &&& msg.content.get_create_request().obj.metadata.namespace.is_None()
            })
                .leads_to(lift_state(|s: State<K, T>|
                    s.resource_key_exists(
                        msg.content.get_create_request().obj.set_namespace(
                            msg.content.get_create_request().namespace
                        ).object_ref()
                    )
                ))
        ),
{
    let pre = |s: State<K, T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_create_request()
        &&& msg.content.get_create_request().obj.metadata.namespace.is_None()
    };
    let post = |s: State<K, T>|
        s.resource_key_exists(
            msg.content.get_create_request().obj.set_namespace(msg.content.get_create_request().namespace).object_ref()
        );
    lemma_pre_leads_to_post_by_kubernetes_api::<K, T, ReconcilerType>(spec, Option::Some(msg), next::<K, T, ReconcilerType>(), handle_request(), pre, post);
}

pub proof fn lemma_delete_req_leads_to_res_not_exists<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(
    spec: TempPred<State<K, T>>, msg: Message, res: DynamicObjectView
)
    requires
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<K, T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.content.is_delete_request()
                &&& msg.content.get_delete_request().key == res.object_ref()
            })
                .leads_to(lift_state(|s: State<K, T>| !s.resource_obj_exists(res)))
        ),
{
    let pre = |s: State<K, T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_delete_request()
        &&& msg.content.get_delete_request().key == res.object_ref()
    };
    let post = |s: State<K, T>| {
        !s.resource_obj_exists(res)
    };
    lemma_pre_leads_to_post_by_kubernetes_api::<K, T, ReconcilerType>(spec, Option::Some(msg), next::<K, T, ReconcilerType>(), handle_request(), pre, post);
}

pub proof fn lemma_always_res_always_exists_implies_delete_never_sent<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(spec: TempPred<State<K, T>>, msg: Message, res: DynamicObjectView)
    requires
        spec.entails(always(lift_action(next::<K, T, ReconcilerType>()))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(always(
            always(lift_state(|s: State<K, T>| s.resource_obj_exists(res)))
                .implies(always(lift_state(|s: State<K, T>| {
                    !{
                        &&& s.message_in_flight(msg)
                        &&& msg.dst == HostId::KubernetesAPI
                        &&& msg.content.is_delete_request()
                        &&& msg.content.get_delete_request().key == res.object_ref()
                    }
                })))
        )),
{
    lemma_delete_req_leads_to_res_not_exists::<K, T, ReconcilerType>(spec, msg, res);
    leads_to_contraposition::<State<K, T>>(spec,
        |s: State<K, T>| {
            &&& s.message_in_flight(msg)
            &&& msg.dst == HostId::KubernetesAPI
            &&& msg.content.is_delete_request()
            &&& msg.content.get_delete_request().key == res.object_ref()
        },
        |s: State<K, T>| !s.resource_obj_exists(res)
    );
    temp_pred_equality::<State<K, T>>(
        not(lift_state(|s: State<K, T>| !s.resource_obj_exists(res))),
        lift_state(|s: State<K, T>| s.resource_obj_exists(res))
    );
    temp_pred_equality::<State<K, T>>(
        not(lift_state(|s: State<K, T>| {
            &&& s.message_in_flight(msg)
            &&& msg.dst == HostId::KubernetesAPI
            &&& msg.content.is_delete_request()
            &&& msg.content.get_delete_request().key == res.object_ref()
        })),
        lift_state(|s: State<K, T>| {
            !{
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.content.is_delete_request()
                &&& msg.content.get_delete_request().key == res.object_ref()
            }
        })
    );
}

pub open spec fn api_request_msg_before(chan_id: nat) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_APIRequest()
        && msg.content.get_msg_id() < chan_id
}

// All the APIRequest messages with a smaller id than chan_id will eventually leave the network.
// The intuition is that (1) The number of such APIRequest messages are bounded by chan_id,
// and (2) weak fairness assumption ensures each message will eventually be handled by Kubernetes.
pub proof fn lemma_pending_requests_are_eventually_consumed<K: ResourceView, T>(
    spec: TempPred<State<K, T>>, reconciler: Reconciler<K, T>, chan_id: nat,
)
    requires
        spec.entails(always(lift_state(|s: State<K, T>| s.chan_id_is_no_smaller_than(chan_id)))),
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            true_pred().leads_to(lift_state(|s: State<K, T>| {
                ! exists |msg: Message|
                    #[trigger] s.message_in_flight(msg)
                    && msg.dst.is_KubernetesAPI()
                    && msg.content.is_APIRequest()
                    && msg.content.get_msg_id() < chan_id
            }))
        )
{
    let pending_requests_num_is_n = |msg_num: nat| lift_state(|s: State<K, T>| {
        s.network_state.in_flight.filter(api_request_msg_before(chan_id)).len() == msg_num
    });
    let no_more_pending_requests = lift_state(|s: State<K, T>| {
        ! exists |msg: Message|
            #[trigger] s.message_in_flight(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_APIRequest()
            && msg.content.get_msg_id() < chan_id
    });

    // Here we split the cases on the number of pending request messages
    // and prove that for all number, all the messages will eventually leave the network.
    assert forall |msg_num: nat|
        spec.entails(#[trigger] pending_requests_num_is_n(msg_num).leads_to(no_more_pending_requests))
    by {
        lemma_pending_requests_number_is_n_leads_to_no_pending_requests(spec, reconciler, chan_id, msg_num);
    }
    leads_to_exists_intro(spec, pending_requests_num_is_n, no_more_pending_requests);

    // Now we merge all the cases on different message number together to get true_pred().
    // We only need to prove tla_exists(pending_requests_num_is_n) == true_pred::<State<K, T>>(),
    // which is obvious.
    assert_by(tla_exists(pending_requests_num_is_n) == true_pred::<State<K, T>>(), {
        assert forall |ex| #[trigger] true_pred().satisfied_by(ex) implies
        tla_exists(pending_requests_num_is_n).satisfied_by(ex) by {
            let current_msg_num = ex.head().network_state.in_flight.filter(api_request_msg_before(chan_id)).len();
            assert(pending_requests_num_is_n(current_msg_num).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pending_requests_num_is_n), true_pred());
    });
}

// This is an inductive proof to show that if there are msg_num requests with id lower than chan_id in the network,
// then eventually all of them will be gone.
proof fn lemma_pending_requests_number_is_n_leads_to_no_pending_requests<K: ResourceView, T>(
    spec: TempPred<State<K, T>>, reconciler: Reconciler<K, T>, chan_id: nat, msg_num: nat,
)
    requires
        spec.entails(always(lift_state(|s: State<K, T>| s.chan_id_is_no_smaller_than(chan_id)))),
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<K, T>| {
                s.network_state.in_flight.filter(api_request_msg_before(chan_id)).len() == msg_num
            }).leads_to(lift_state(|s: State<K, T>| {
                ! exists |msg: Message|
                    #[trigger] s.message_in_flight(msg)
                    && msg.dst.is_KubernetesAPI()
                    && msg.content.is_APIRequest()
                    && msg.content.get_msg_id() < chan_id
            }))
        ),
    decreases msg_num
{
    if msg_num == 0 {
        // The base case:
        // If there are 0 such requests, then all of them are gone. Seems trivial.
        let pending_requests_num_is_zero = lift_state(|s: State<K, T>| {
            s.network_state.in_flight.filter(api_request_msg_before(chan_id)).len() == 0
        });
        let no_more_pending_requests = lift_state(|s: State<K, T>| {
            ! exists |msg: Message|
                #[trigger] s.message_in_flight(msg)
                && msg.dst.is_KubernetesAPI()
                && msg.content.is_APIRequest()
                && msg.content.get_msg_id() < chan_id
        });

        // But it still takes some efforts to show these two things are the same.
        assert_by(pending_requests_num_is_zero == no_more_pending_requests, {
            assert forall |ex| pending_requests_num_is_zero.satisfied_by(ex)
            implies no_more_pending_requests.satisfied_by(ex) by {
                assert forall |msg| !
                    (#[trigger] ex.head().message_in_flight(msg)
                    && msg.dst.is_KubernetesAPI()
                    && msg.content.is_APIRequest()
                    && msg.content.get_msg_id() < chan_id)
                by {
                    assert(
                        ex.head().network_state.in_flight.filter(api_request_msg_before(chan_id)).count(msg) == 0
                    );
                }
            };

            assert forall |ex| no_more_pending_requests.satisfied_by(ex)
            implies pending_requests_num_is_zero.satisfied_by(ex) by {
                assert forall |msg|
                    ex.head().network_state.in_flight.filter(api_request_msg_before(chan_id)).count(msg) == 0
                by {
                    assert(!
                        (ex.head().message_in_flight(msg)
                        && msg.dst.is_KubernetesAPI()
                        && msg.content.is_APIRequest()
                        && msg.content.get_msg_id() < chan_id)
                    );
                };
                len_is_zero_if_count_for_each_value_is_zero::<Message>(
                    ex.head().network_state.in_flight.filter(api_request_msg_before(chan_id))
                );
            };

            temp_pred_equality(pending_requests_num_is_zero, no_more_pending_requests);
        });

        leads_to_self_temp(pending_requests_num_is_zero);
    } else {
        // The induction step:
        // If we already have "there are msg_num-1 such requests" ~> "all such requests are gone" (the inductive hypothesis),
        // then we only need to prove "there are msg_num such requests" ~> "there are msg_num-1 such requests",
        // which seems to be just one wf1 away.
        let pending_requests_num_is_msg_num = lift_state(|s: State<K, T>| {
            s.network_state.in_flight.filter(api_request_msg_before(chan_id)).len() == msg_num
        });
        let pending_requests_num_is_msg_num_minus_1 = lift_state(|s: State<K, T>| {
            s.network_state.in_flight.filter(api_request_msg_before(chan_id)).len() == (msg_num - 1) as nat
        });
        let no_more_pending_requests = lift_state(|s: State<K, T>| {
            ! exists |msg: Message|
                #[trigger] s.message_in_flight(msg)
                && msg.dst.is_KubernetesAPI()
                && msg.content.is_APIRequest()
                && msg.content.get_msg_id() < chan_id
        });
        let pending_req_in_flight = |msg: Message| lift_state(|s: State<K, T>| {
            s.network_state.in_flight.filter(api_request_msg_before(chan_id)).count(msg) > 0
        });
        let pending_requests_num_is_msg_num_and_pending_req_in_flight = |msg: Message| lift_state(|s: State<K, T>| {
            &&& s.network_state.in_flight.filter(api_request_msg_before(chan_id)).len() == msg_num
            &&& s.network_state.in_flight.filter(api_request_msg_before(chan_id)).count(msg) > 0
        });
        // But to apply wf1 to get "there are msg_num such requests" ~> "there are msg_num-1 such requests",
        // we need a concrete message to serve as the input of the forward action.
        // So here we split cases on different request messages in the network so that we have a concrete message
        // to reason about.
        assert forall |msg: Message| spec.entails(
            #[trigger] pending_requests_num_is_msg_num_and_pending_req_in_flight(msg)
                .leads_to(pending_requests_num_is_msg_num_minus_1)
        ) by {
            pending_requests_num_decreases(spec, reconciler, chan_id, msg_num, msg);
        }
        leads_to_exists_intro(
            spec, pending_requests_num_is_msg_num_and_pending_req_in_flight, pending_requests_num_is_msg_num_minus_1
        );
        // Now we merge all the splitted cases on different concrete messages.
        assert_by(tla_exists(pending_requests_num_is_msg_num_and_pending_req_in_flight) == pending_requests_num_is_msg_num, {
            assert forall |ex| #[trigger] pending_requests_num_is_msg_num.satisfied_by(ex)
            implies tla_exists(pending_requests_num_is_msg_num_and_pending_req_in_flight).satisfied_by(ex) by {
                let msg = ex.head().network_state.in_flight.filter(api_request_msg_before(chan_id)).choose();
                assert(ex.head().network_state.in_flight.filter(api_request_msg_before(chan_id)).count(msg) > 0);
                assert(pending_requests_num_is_msg_num_and_pending_req_in_flight(msg).satisfied_by(ex));
            }
            temp_pred_equality(
                tla_exists(pending_requests_num_is_msg_num_and_pending_req_in_flight), pending_requests_num_is_msg_num
            );
        });
        // We use the inductive hypothesis here.
        lemma_pending_requests_number_is_n_leads_to_no_pending_requests(spec, reconciler, chan_id, (msg_num - 1) as nat);
        leads_to_trans_temp(
            spec, pending_requests_num_is_msg_num, pending_requests_num_is_msg_num_minus_1, no_more_pending_requests
        );
    }
}

proof fn pending_requests_num_decreases<K: ResourceView, T>(
    spec: TempPred<State<K, T>>, reconciler: Reconciler<K, T>, chan_id: nat, msg_num: nat, msg: Message
)
    requires
        msg_num > 0,
        spec.entails(always(lift_state(|s: State<K, T>| s.chan_id_is_no_smaller_than(chan_id)))),
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<K, T>| {
                &&& s.network_state.in_flight.filter(api_request_msg_before(chan_id)).len() == msg_num
                &&& s.network_state.in_flight.filter(api_request_msg_before(chan_id)).count(msg) > 0
            })
                .leads_to(lift_state(|s: State<K, T>| {
                    s.network_state.in_flight.filter(api_request_msg_before(chan_id)).len() == (msg_num - 1) as nat
                }))
        ),
{
    let pre = |s: State<K, T>| {
        &&& s.network_state.in_flight.filter(api_request_msg_before(chan_id)).len() == msg_num
        &&& s.network_state.in_flight.filter(api_request_msg_before(chan_id)).count(msg) > 0
    };
    let post = |s: State<K, T>| {
        s.network_state.in_flight.filter(api_request_msg_before(chan_id)).len() == (msg_num - 1) as nat
    };
    let input = Option::Some(msg);
    let stronger_next = |s, s_prime: State<K, T>| {
        &&& next(reconciler)(s, s_prime)
        &&& s.chan_id_is_no_smaller_than(chan_id)
    };
    strengthen_next::<State<K, T>>(spec, next(reconciler), |s: State<K, T>| s.chan_id_is_no_smaller_than(chan_id), stronger_next);

    assert forall |s, s_prime: State<K, T>| pre(s) && #[trigger] stronger_next(s, s_prime)
    implies pre(s_prime) || post(s_prime) by {
        let pending_req_multiset = s.network_state.in_flight.filter(api_request_msg_before(chan_id));
        let pending_req_multiset_prime = s_prime.network_state.in_flight.filter(api_request_msg_before(chan_id));
        let step = choose |step| next_step(reconciler, s, s_prime, step);
        assert(next_step(reconciler, s, s_prime, step));
        match step {
            Step::KubernetesAPIStep(input) => {
                if pending_req_multiset.count(input.get_Some_0()) > 0 {
                    assert_multisets_equal!(pending_req_multiset.remove(input.get_Some_0()), pending_req_multiset_prime);
                } else {
                    assert_multisets_equal!(pending_req_multiset, pending_req_multiset_prime);
                }
            },
            Step::ControllerStep(input) => {
                assert_multisets_equal!(pending_req_multiset, pending_req_multiset_prime);
            },
            Step::ClientStep(input) => {
                assert_multisets_equal!(pending_req_multiset, pending_req_multiset_prime);
            },
            _ => {}
        }
    }
    assert forall |s, s_prime: State<K, T>| pre(s) && #[trigger] stronger_next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let pending_req_multiset = s.network_state.in_flight.filter(api_request_msg_before(chan_id));
        let pending_req_multiset_prime = s_prime.network_state.in_flight.filter(api_request_msg_before(chan_id));
        assert_multisets_equal!(pending_req_multiset.remove(msg), pending_req_multiset_prime);
    }
    lemma_pre_leads_to_post_by_kubernetes_api(
        spec, reconciler, input, stronger_next, handle_request(), pre, post
    );
}

}
