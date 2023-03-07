// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::{
    proof::wf1_assistant::kubernetes_api_action_pre_implies_next_pre,
    spec::{
        common::*,
        distributed_system::*,
        kubernetes_api::common::{KubernetesAPIAction, KubernetesAPIActionInput},
        kubernetes_api::state_machine::{handle_request, kubernetes_api},
        reconciler::Reconciler,
    },
};
use crate::pervasive::{option::*, result::*};
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_pre_leads_to_post_by_kubernetes_api<T>(reconciler: Reconciler<T>, input: KubernetesAPIActionInput, next: ActionPred<State<T>>, action: KubernetesAPIAction, pre: StatePred<State<T>>, post: StatePred<State<T>>)
    requires
        kubernetes_api().actions.contains(action),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<T>| #[trigger] pre(s) ==> kubernetes_api_action_pre(action, input)(s),
        sm_spec(reconciler).entails(always(lift_action(next))),
    ensures
        sm_spec(reconciler).entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<T>, KubernetesAPIActionInput>(sm_spec(reconciler), |i| kubernetes_api_next().weak_fairness(i), input);

    kubernetes_api_action_pre_implies_next_pre::<T>(action, input);
    valid_implies_trans::<State<T>>(lift_state(pre), lift_state(kubernetes_api_action_pre(action, input)), lift_state(kubernetes_api_next().pre(input)));

    kubernetes_api_next().wf1(input, sm_spec(reconciler), next, pre, post);
}

pub proof fn lemma_pre_leads_to_post_with_assumption_by_kubernetes_api<T>(reconciler: Reconciler<T>, input: KubernetesAPIActionInput, next: ActionPred<State<T>>, action: KubernetesAPIAction, assumption: StatePred<State<T>>, pre: StatePred<State<T>>, post: StatePred<State<T>>)
    requires
        kubernetes_api().actions.contains(action),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && assumption(s) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<T>| pre(s) && #[trigger] next(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<T>| #[trigger] pre(s) ==> kubernetes_api_action_pre(action, input)(s),
        sm_spec(reconciler).entails(always(lift_action(next))),
    ensures
        sm_spec(reconciler).entails(lift_state(pre).and(always(lift_state(assumption))).leads_to(lift_state(post))),
{
    use_tla_forall::<State<T>, KubernetesAPIActionInput>(sm_spec(reconciler), |i| kubernetes_api_next().weak_fairness(i), input);

    kubernetes_api_action_pre_implies_next_pre::<T>(action, input);
    valid_implies_trans::<State<T>>(lift_state(pre), lift_state(kubernetes_api_action_pre(action, input)), lift_state(kubernetes_api_next().pre(input)));

    kubernetes_api_next().wf1_assume(input, sm_spec(reconciler), next, assumption, pre, post);
}

pub proof fn lemma_create_req_leads_to_ok_resp<T>(reconciler: Reconciler<T>, msg: Message)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.is_create_request()
                &&& !s.resource_key_exists(msg.get_create_request().obj.key)
            })
            .and(always(lift_state(|s: State<T>| {
                forall |other: Message|
                    #[trigger] s.message_in_flight(other)
                    && other.is_create_request()
                    && other.get_create_request() == msg.get_create_request()
                    && other.dst == msg.dst
                        ==> other == msg
            })))
                .leads_to(
                    lift_state(|s: State<T>| {
                        &&& s.message_in_flight(form_msg(msg.dst, msg.src, create_resp_msg(Result::Ok(msg.get_create_request().obj), msg.get_req_id())))
                        &&& s.resource_key_exists(msg.get_create_request().obj.key)
                    })
                )
        ),
{
    let assumption = |s: State<T>| {
        forall |other: Message|
            #[trigger] s.message_in_flight(other)
            && other.is_create_request()
            && other.get_create_request() == msg.get_create_request()
            && other.dst == msg.dst
                ==> other == msg
    };
    let pre = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.is_create_request()
        &&& !s.resource_key_exists(msg.get_create_request().obj.key)
    };
    let post = |s: State<T>| {
        &&& s.message_in_flight(form_msg(msg.dst, msg.src, create_resp_msg(Result::Ok(msg.get_create_request().obj), msg.get_req_id())))
        &&& s.resource_key_exists(msg.get_create_request().obj.key)
    };
    lemma_pre_leads_to_post_with_assumption_by_kubernetes_api::<T>(reconciler, Option::Some(msg), next(reconciler), handle_request(), assumption, pre, post);
}

pub proof fn lemma_get_req_leads_to_some_resp<T>(reconciler: Reconciler<T>, msg: Message, key: ResourceKey)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<T>| {
                    &&& s.message_in_flight(msg)
                    &&& msg.dst == HostId::KubernetesAPI
                    &&& msg.is_get_request()
                    &&& msg.get_get_request().key == key
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
        &&& msg.is_get_request()
        &&& msg.get_get_request().key == key
    };
    let post = |s: State<T>| exists |resp_msg: Message| {
        &&& #[trigger] s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
    };
    assert forall |s, s_prime: State<T>| pre(s) && #[trigger] next(reconciler)(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        if s.resource_key_exists(key) {
            let ok_resp_msg = form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)), msg.get_req_id());
            assert(s_prime.message_in_flight(ok_resp_msg));
            assert(resp_msg_matches_req_msg(ok_resp_msg, msg));
        } else {
            let err_resp_msg = form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound), msg.get_req_id());
            assert(s_prime.message_in_flight(err_resp_msg));
            assert(resp_msg_matches_req_msg(err_resp_msg, msg));
        }
    };
    lemma_pre_leads_to_post_by_kubernetes_api::<T>(reconciler, input, next(reconciler), handle_request(), pre, post);
}

pub proof fn lemma_get_req_leads_to_ok_or_err_resp<T>(reconciler: Reconciler<T>, msg: Message, key: ResourceKey)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.is_get_request()
                &&& msg.get_get_request().key == key
            })
                .leads_to(
                    lift_state(|s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)), msg.get_req_id())))
                    .or(lift_state(|s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound), msg.get_req_id()))))
                )
        ),
{
    let pre = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key == key
    };
    let post = |s: State<T>| {
        ||| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)), msg.get_req_id()))
        ||| s.message_in_flight(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound), msg.get_req_id()))
    };
    lemma_pre_leads_to_post_by_kubernetes_api::<T>(reconciler, Option::Some(msg), next(reconciler), handle_request(), pre, post);
    temp_pred_equality::<State<T>>(
        lift_state(post),
        lift_state(|s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)), msg.get_req_id())))
        .or(lift_state(|s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound), msg.get_req_id()))))
    );
}

pub proof fn lemma_get_req_leads_to_ok_resp_if_never_delete<T>(reconciler: Reconciler<T>, msg: Message, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.is_get_request()
                &&& msg.get_get_request().key == res.key
                &&& s.resource_obj_exists(res)
            })
            .and(always(lift_state(|s: State<T>| {
                forall |other: Message|
                !{
                    &&& #[trigger] s.message_in_flight(other)
                    &&& other.dst == HostId::KubernetesAPI
                    &&& other.is_delete_request()
                    &&& other.get_delete_request().key == res.key
                }
            })))
                .leads_to(lift_state(|s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(res), msg.get_req_id()))))
        ),
{
    let pre = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key == res.key
        &&& s.resource_obj_exists(res)
    };
    let assumption = |s: State<T>| {
        forall |other: Message|
            !{
                &&& #[trigger] s.message_in_flight(other)
                &&& other.dst == HostId::KubernetesAPI
                &&& other.is_delete_request()
                &&& other.get_delete_request().key == res.key
            }
    };
    let post = |s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(res), msg.get_req_id()));
    lemma_pre_leads_to_post_with_assumption_by_kubernetes_api::<T>(reconciler, Option::Some(msg), next(reconciler), handle_request(), assumption, pre, post);
}

pub proof fn lemma_get_req_leads_to_ok_resp_if_res_always_exists<T>(reconciler: Reconciler<T>, msg: Message, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.is_get_request()
                &&& msg.get_get_request().key == res.key
            })
            .and(always(lift_state(|s: State<T>| s.resource_obj_exists(res))))
                .leads_to(lift_state(|s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(res), msg.get_req_id()))))
        ),
{
    leads_to_weaken_auto::<State<T>>(sm_spec(reconciler));

    let get_req_msg_sent = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key == res.key
    };
    let res_exists = |s: State<T>| s.resource_obj_exists(res);
    let get_req_msg_sent_and_res_exists = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key == res.key
        &&& s.resource_obj_exists(res)
    };
    let delete_req_never_sent = |s: State<T>| {
        forall |other: Message|
        !{
            &&& #[trigger] s.message_in_flight(other)
            &&& other.dst == HostId::KubernetesAPI
            &&& other.is_delete_request()
            &&& other.get_delete_request().key == res.key
        }
    };
    let ok_resp_msg_sent = |s: State<T>| s.message_in_flight(form_get_resp_msg(msg, Result::Ok(res), msg.get_req_id()));

    lemma_always_res_always_exists_implies_forall_delete_never_sent::<T>(reconciler, res);
    // Now we have spec.entails(always(always(lift_state(res_exists)).implies(always(lift_state(delete_req_never_sent)))))
    // We want to add get_req_msg_sent_and_res_exists to both ends by using sandwich_always_implies_temp
    sandwich_always_implies_temp::<State<T>>(sm_spec(reconciler),
        lift_state(get_req_msg_sent_and_res_exists),
        always(lift_state(res_exists)),
        always(lift_state(delete_req_never_sent))
    );

    lemma_get_req_leads_to_ok_resp_if_never_delete::<T>(reconciler, msg, res);
    // Use the assert to trigger leads_to_weaken_auto
    // The always-implies formula required by leads_to_weaken_auto is given by the above sandwich_always_implies_temp
    assert(sm_spec(reconciler).entails(
        lift_state(get_req_msg_sent_and_res_exists).and(always(lift_state(res_exists)))
            .leads_to(lift_state(ok_resp_msg_sent))
    ));

    temp_pred_equality::<State<T>>(
        lift_state(get_req_msg_sent_and_res_exists).and(always(lift_state(res_exists))),
        lift_state(get_req_msg_sent).and(lift_state(res_exists).and(always(lift_state(res_exists))))
    );

    assert(sm_spec(reconciler).entails(
        lift_state(get_req_msg_sent).and(lift_state(res_exists)).and(always(lift_state(res_exists)))
            .leads_to(lift_state(ok_resp_msg_sent))
    ));
    // Last step: use p_and_always_p_equals_always_p to remove the .and(lift_state(res_exists)) from the premise
    p_and_always_p_equals_always_p::<State<T>>(lift_state(res_exists));
}

pub proof fn lemma_create_req_leads_to_res_exists<T>(reconciler: Reconciler<T>, msg: Message, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.is_create_request()
                &&& msg.get_create_request().obj == res
            })
                .leads_to(lift_state(|s: State<T>| s.resource_key_exists(res.key)))
        ),
{
    let pre = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.is_create_request()
        &&& msg.get_create_request().obj == res
    };
    let post = |s: State<T>| {
        s.resource_key_exists(res.key)
    };
    lemma_pre_leads_to_post_by_kubernetes_api::<T>(reconciler, Option::Some(msg), next(reconciler), handle_request(), pre, post);
}

pub proof fn lemma_delete_req_leads_to_res_not_exists<T>(reconciler: Reconciler<T>, msg: Message, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<T>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.is_delete_request()
                &&& msg.get_delete_request().key == res.key
            })
                .leads_to(lift_state(|s: State<T>| !s.resource_obj_exists(res)))
        ),
{
    let pre = |s: State<T>| {
        &&& s.message_in_flight(msg)
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.is_delete_request()
        &&& msg.get_delete_request().key == res.key
    };
    let post = |s: State<T>| {
        !s.resource_obj_exists(res)
    };
    lemma_pre_leads_to_post_by_kubernetes_api::<T>(reconciler, Option::Some(msg), next(reconciler), handle_request(), pre, post);
}

pub proof fn lemma_always_res_always_exists_implies_delete_never_sent<T>(reconciler: Reconciler<T>, msg: Message, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(always(
            always(lift_state(|s: State<T>| s.resource_obj_exists(res)))
                .implies(always(lift_state(|s: State<T>| {
                    !{
                        &&& s.message_in_flight(msg)
                        &&& msg.dst == HostId::KubernetesAPI
                        &&& msg.is_delete_request()
                        &&& msg.get_delete_request().key == res.key
                    }
                })))
        )),
{
    lemma_delete_req_leads_to_res_not_exists::<T>(reconciler, msg, res);
    leads_to_contraposition::<State<T>>(sm_spec(reconciler),
        |s: State<T>| {
            &&& s.message_in_flight(msg)
            &&& msg.dst == HostId::KubernetesAPI
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key == res.key
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
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key == res.key
        })),
        lift_state(|s: State<T>| {
            !{
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.is_delete_request()
                &&& msg.get_delete_request().key == res.key
            }
        })
    );
}

/// How to prove this? It is obvious according to lemma_always_res_always_exists_implies_delete_never_sent
pub proof fn lemma_always_res_always_exists_implies_forall_delete_never_sent<T>(reconciler: Reconciler<T>, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(always(
            always(lift_state(|s: State<T>| s.resource_obj_exists(res)))
                .implies(always(lift_state(|s: State<T>| {
                    forall |msg: Message|
                    !{
                        &&& #[trigger] s.message_in_flight(msg)
                        &&& msg.dst == HostId::KubernetesAPI
                        &&& msg.is_delete_request()
                        &&& msg.get_delete_request().key == res.key
                    }
                })))
        )),
{
    let pre = always(lift_state(|s: State<T>| s.resource_obj_exists(res)));
    let m_to_always_m_not_sent = |msg: Message| always(lift_state(|s: State<T>| {
        !{
            &&& s.message_in_flight(msg)
            &&& msg.dst == HostId::KubernetesAPI
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key == res.key
        }
    }));
    assert forall |msg: Message| sm_spec(reconciler).entails(#[trigger] always(pre.implies(m_to_always_m_not_sent(msg)))) by {
        lemma_always_res_always_exists_implies_delete_never_sent(reconciler, msg, res);
    };
    always_implies_forall_intro::<State<T>, Message>(sm_spec(reconciler), pre, m_to_always_m_not_sent);

    let m_to_m_not_sent = |msg: Message| lift_state(|s: State<T>| {
        !{
            &&& s.message_in_flight(msg)
            &&& msg.dst == HostId::KubernetesAPI
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key == res.key
        }
    });
    tla_forall_always_equality_variant::<State<T>, Message>(m_to_always_m_not_sent, m_to_m_not_sent);

    let forall_m_to_m_not_sent = lift_state(|s: State<T>| {
        forall |msg: Message|
        !{
            &&& #[trigger] s.message_in_flight(msg)
            &&& msg.dst == HostId::KubernetesAPI
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key == res.key
        }
    });
    assert forall |ex| #[trigger] tla_forall(m_to_m_not_sent).satisfied_by(ex) implies forall_m_to_m_not_sent.satisfied_by(ex) by {
        assert forall |msg: Message|
            !{
                &&& #[trigger] ex.head().message_in_flight(msg)
                &&& msg.dst == HostId::KubernetesAPI
                &&& msg.is_delete_request()
                &&& msg.get_delete_request().key == res.key
            }
        by {
            assert(m_to_m_not_sent(msg).satisfied_by(ex));
        };
    };
    temp_pred_equality::<State<T>>(tla_forall(m_to_m_not_sent), forall_m_to_m_not_sent);
}

}
