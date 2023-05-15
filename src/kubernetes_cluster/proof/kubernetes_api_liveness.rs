// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, dynamic::*, error::*};
use crate::kubernetes_cluster::{
    proof::wf1_assistant::kubernetes_api_action_pre_implies_next_pre,
    spec::{
        distributed_system::*,
        kubernetes_api::common::KubernetesAPIAction,
        kubernetes_api::state_machine::{handle_request, kubernetes_api},
        message::*,
    },
};
use crate::reconciler::spec::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use builtin::*;
use builtin_macros::*;
use vstd::{option::*, result::*};

verus! {

pub proof fn lemma_pre_leads_to_post_by_kubernetes_api<K: Marshalable, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, input: Option<Message>, next: ActionPred<State<T>>, action: KubernetesAPIAction, pre: StatePred<State<T>>, post: StatePred<State<T>>)
    requires
        kubernetes_api().actions.contains(action),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<T>| #[trigger] pre(s) ==> kubernetes_api_action_pre(action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<T>, Option<Message>>(spec, |i| kubernetes_api_next().weak_fairness(i), input);

    kubernetes_api_action_pre_implies_next_pre::<T>(action, input);
    valid_implies_trans::<State<T>>(lift_state(pre), lift_state(kubernetes_api_action_pre(action, input)), lift_state(kubernetes_api_next().pre(input)));

    kubernetes_api_next().wf1(input, spec, next, pre, post);
}

pub proof fn lemma_pre_leads_to_post_with_assumption_by_kubernetes_api<K: Marshalable, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, input: Option<Message>, next: ActionPred<State<T>>, action: KubernetesAPIAction, assumption: StatePred<State<T>>, pre: StatePred<State<T>>, post: StatePred<State<T>>)
    requires
        kubernetes_api().actions.contains(action),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && assumption(s) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<T>| #[trigger] pre(s) ==> kubernetes_api_action_pre(action, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(lift_state(pre).and(always(lift_state(assumption))).leads_to(lift_state(post))),
{
    use_tla_forall::<State<T>, Option<Message>>(spec, |i| kubernetes_api_next().weak_fairness(i), input);

    kubernetes_api_action_pre_implies_next_pre::<T>(action, input);
    valid_implies_trans::<State<T>>(lift_state(pre), lift_state(kubernetes_api_action_pre(action, input)), lift_state(kubernetes_api_next().pre(input)));

    kubernetes_api_next().wf1_assume(input, spec, next, assumption, pre, post);
}

pub proof fn lemma_get_req_leads_to_some_resp<K: Marshalable, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, msg: Message, key: ObjectRef)
    requires
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<T>| {
                    &&& s.message_in_flight(msg)
                    &&& msg.dst == HostId::KubernetesAPI
                    &&& msg.content.is_get_request()
                    &&& msg.content.get_get_request().key == key
                })
                .leads_to(
                    lift_state(|s: State<T>|
                        exists |resp_msg: Message| {
                            &&& #[trigger] s.message_in_flight(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, msg)
                        }
                    )
                )
        ),
{
    let input = Option::Some(msg);
    let pre = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_get_request()
        &&& msg.content.get_get_request().key == key
    };
    let post = |s: State<T>| exists |resp_msg: Message| {
        &&& #[trigger] s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
    };
    assert forall |s, s_prime: State<T>| pre(s) && #[trigger] next(reconciler)(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
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
    lemma_pre_leads_to_post_by_kubernetes_api(spec, reconciler, input, next(reconciler), handle_request(), pre, post);
}

pub proof fn lemma_get_req_leads_to_ok_or_err_resp<K: Marshalable, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, msg: Message, key: ObjectRef)
    requires
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.content.is_get_request()
                &&& msg.content.get_get_request().key == key
            })
                .leads_to(
                    lift_state(|s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)))))
                    .or(lift_state(|s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))))
                )
        ),
{
    let pre = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_get_request()
        &&& msg.content.get_get_request().key == key
    };
    let post = |s: State<T>| {
        ||| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key))))
        ||| s.message_in_flight(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))
    };
    lemma_pre_leads_to_post_by_kubernetes_api(spec, reconciler, Option::Some(msg), next(reconciler), handle_request(), pre, post);
    temp_pred_equality::<State<T>>(
        lift_state(post),
        lift_state(|s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)))))
        .or(lift_state(|s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))))
    );
}

pub proof fn lemma_get_req_leads_to_ok_resp_if_never_delete<K: Marshalable, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, msg: Message, res: DynamicObjectView)
    requires
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.content.is_get_request()
                &&& msg.content.get_get_request().key == res.object_ref()
                &&& s.resource_obj_exists(res)
            })
            .and(always(lift_state(|s: State<T>| {
                forall |other: Message|
                !{
                    &&& #[trigger] s.message_in_flight(other)
                    &&& other.dst == HostId::KubernetesAPI
                    &&& other.content.is_delete_request()
                    &&& other.content.get_delete_request().key == res.object_ref()
                }
            })))
                .leads_to(lift_state(|s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(res)))))
        ),
{
    let pre = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_get_request()
        &&& msg.content.get_get_request().key == res.object_ref()
        &&& s.resource_obj_exists(res)
    };
    let assumption = |s: State<T>| {
        forall |other: Message|
            !{
                &&& #[trigger] s.message_in_flight(other)
                &&& other.dst == HostId::KubernetesAPI
                &&& other.content.is_delete_request()
                &&& other.content.get_delete_request().key == res.object_ref()
            }
    };
    let post = |s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(res)));
    lemma_pre_leads_to_post_with_assumption_by_kubernetes_api(spec, reconciler, Option::Some(msg), next(reconciler), handle_request(), assumption, pre, post);
}

pub proof fn lemma_create_req_leads_to_res_exists<K: Marshalable, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, msg: Message, res: DynamicObjectView)
    requires
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.content.is_create_request()
                &&& msg.content.get_create_request().obj == res
            })
                .leads_to(lift_state(|s: State<T>| s.resource_key_exists(res.object_ref())))
        ),
{
    let pre = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_create_request()
        &&& msg.content.get_create_request().obj == res
    };
    let post = |s: State<T>| {
        s.resource_key_exists(res.object_ref())
    };
    lemma_pre_leads_to_post_by_kubernetes_api(spec, reconciler, Option::Some(msg), next(reconciler), handle_request(), pre, post);
}

pub proof fn lemma_delete_req_leads_to_res_not_exists<K: Marshalable, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, msg: Message, res: DynamicObjectView)
    requires
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.content.is_delete_request()
                &&& msg.content.get_delete_request().key == res.object_ref()
            })
                .leads_to(lift_state(|s: State<T>| !s.resource_obj_exists(res)))
        ),
{
    let pre = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_delete_request()
        &&& msg.content.get_delete_request().key == res.object_ref()
    };
    let post = |s: State<T>| {
        !s.resource_obj_exists(res)
    };
    lemma_pre_leads_to_post_by_kubernetes_api(spec, reconciler, Option::Some(msg), next(reconciler), handle_request(), pre, post);
}

pub proof fn lemma_always_res_always_exists_implies_delete_never_sent<K: Marshalable, T>(spec: TempPred<State<T>>, reconciler: Reconciler<K, T>, msg: Message, res: DynamicObjectView)
    requires
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(always(
            always(lift_state(|s: State<T>| s.resource_obj_exists(res)))
                .implies(always(lift_state(|s: State<T>| {
                    !{
                        &&& s.message_in_flight(msg)
                        &&& msg.dst == HostId::KubernetesAPI
                        &&& msg.content.is_delete_request()
                        &&& msg.content.get_delete_request().key == res.object_ref()
                    }
                })))
        )),
{
    lemma_delete_req_leads_to_res_not_exists(spec, reconciler, msg, res);
    leads_to_contraposition::<State<T>>(spec,
        |s: State<T>| {
            &&& s.message_in_flight(msg)
            &&& msg.dst == HostId::KubernetesAPI
            &&& msg.content.is_delete_request()
            &&& msg.content.get_delete_request().key == res.object_ref()
        },
        |s: State<T>| !s.resource_obj_exists(res)
    );
    temp_pred_equality::<State<T>>(
        not(lift_state(|s: State<T>| !s.resource_obj_exists(res))),
        lift_state(|s: State<T>| s.resource_obj_exists(res))
    );
    temp_pred_equality::<State<T>>(
        not(lift_state(|s: State<T>| {
            &&& s.message_in_flight(msg)
            &&& msg.dst == HostId::KubernetesAPI
            &&& msg.content.is_delete_request()
            &&& msg.content.get_delete_request().key == res.object_ref()
        })),
        lift_state(|s: State<T>| {
            !{
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.content.is_delete_request()
                &&& msg.content.get_delete_request().key == res.object_ref()
            }
        })
    );
}

}
