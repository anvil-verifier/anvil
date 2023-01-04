// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::kubernetes_cluster::{
    proof::wf1_assistant::kubernetes_api_action_pre_implies_next_pre,
    spec::{
        common::*, distributed_system::*, kubernetes_api, kubernetes_api::KubernetesAPIActionInput,
    },
};
use crate::pervasive::{option::*, result::*};
use crate::temporal_logic::*;
use crate::temporal_logic_rules;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_pre_leads_to_post_by_kubernetes_api(input: KubernetesAPIActionInput, action: kubernetes_api::KubernetesAPIAction, pre: StatePred<State>, post: StatePred<State>)
    requires
        kubernetes_api::kubernetes_api().actions.contains(action),
        forall |s, s_prime: State| pre(s) && action_pred_call(next(), s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State| pre(s) && action_pred_call(next(), s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State| state_pred_call(pre, s) ==> kubernetes_api_action_pre(action, input)(s),
    ensures
        sm_spec().entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State, KubernetesAPIActionInput>(sm_spec(), |r| kubernetes_api_next().weak_fairness(r), input);

    kubernetes_api_action_pre_implies_next_pre(action, input);
    valid_implies_trans::<State>(lift_state(pre), lift_state(kubernetes_api_action_pre(action, input)), lift_state(kubernetes_api_next().pre(input)));

    kubernetes_api_next().wf1(input, sm_spec(), next(), pre, post);
}

pub proof fn lemma_pre_leads_to_post_with_asm_by_kubernetes_api(input: KubernetesAPIActionInput, action: kubernetes_api::KubernetesAPIAction, asm: StatePred<State>, pre: StatePred<State>, post: StatePred<State>)
    requires
        kubernetes_api::kubernetes_api().actions.contains(action),
        forall |s, s_prime: State| pre(s) && action_pred_call(next(), s, s_prime) && asm(s) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State| pre(s) && action_pred_call(next(), s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State| state_pred_call(pre, s) ==> kubernetes_api_action_pre(action, input)(s),
    ensures
        sm_spec().entails(lift_state(pre).and(always(lift_state(asm))).leads_to(lift_state(post))),
{
    use_tla_forall::<State, KubernetesAPIActionInput>(sm_spec(), |r| kubernetes_api_next().weak_fairness(r), input);

    kubernetes_api_action_pre_implies_next_pre(action, input);
    valid_implies_trans::<State>(lift_state(pre), lift_state(kubernetes_api_action_pre(action, input)), lift_state(kubernetes_api_next().pre(input)));

    kubernetes_api_next().wf1_assume(input, sm_spec(), next(), asm, pre, post);
}

pub proof fn lemma_create_req_leads_to_ok_resp(msg: Message)
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_create_request()
                &&& !s.resource_key_exists(msg.get_create_request().obj.key)
            })
            .and(always(lift_state(|s: State| {
                forall |other: Message|
                    #[trigger] s.message_sent(other) && other.content === msg.content && other.dst === msg.dst
                        ==> other === msg
            })))
                .leads_to(
                    lift_state(|s: State| {
                        &&& s.message_sent(form_msg(msg.dst, msg.src, create_resp_msg(Result::Ok(msg.get_create_request().obj), msg.get_create_request())))
                        &&& s.resource_key_exists(msg.get_create_request().obj.key)
                    })
                )
        ),
{
    let asm = |s: State| {
        forall |other: Message|
            #[trigger] s.message_sent(other) && other.content === msg.content && other.dst === msg.dst
                ==> other === msg
    };
    let pre = |s: State| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_create_request()
        &&& !s.resource_key_exists(msg.get_create_request().obj.key)
    };
    let post = |s: State| {
        &&& s.message_sent(form_msg(msg.dst, msg.src, create_resp_msg(Result::Ok(msg.get_create_request().obj), msg.get_create_request())))
        &&& s.resource_key_exists(msg.get_create_request().obj.key)
    };
    lemma_pre_leads_to_post_with_asm_by_kubernetes_api(Option::Some(msg), kubernetes_api::handle_request(), asm, pre, post);
}

pub proof fn lemma_get_req_leads_to_some_resp(msg: Message, key: ResourceKey)
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                    &&& s.message_sent(msg)
                    &&& msg.dst === HostId::KubernetesAPI
                    &&& msg.is_get_request()
                    &&& msg.get_get_request().key === key
                })
                .leads_to(
                    lift_state(|s: State|
                        exists |resp_msg: Message| {
                            &&& #[trigger] s.message_sent(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, msg)
                        }
                    )
                )
        ),
{
    let input = Option::Some(msg);
    let pre = |s: State| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key === key
    };
    let post = |s: State| exists |resp_msg: Message| {
        &&& #[trigger] s.message_sent(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
    };
    assert forall |s, s_prime: State| pre(s) && action_pred_call(next(), s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        if s.resource_key_exists(key) {
            let ok_resp_msg = form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)));
            assert(s_prime.message_sent(ok_resp_msg));
            assert(resp_msg_matches_req_msg(ok_resp_msg, msg));
        } else {
            let err_resp_msg = form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound));
            assert(s_prime.message_sent(err_resp_msg));
            assert(resp_msg_matches_req_msg(err_resp_msg, msg));
        }
    };
    lemma_pre_leads_to_post_by_kubernetes_api(input, kubernetes_api::handle_request(), pre, post);
}

pub proof fn lemma_get_req_leads_to_ok_or_err_resp(msg: Message, key: ResourceKey)
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_get_request()
                &&& msg.get_get_request().key === key
            })
                .leads_to(
                    lift_state(|s: State| s.message_sent(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)))))
                    .or(lift_state(|s: State| s.message_sent(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))))
                )
        ),
{
    let pre = |s: State| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key === key
    };
    let post = |s: State| {
        ||| s.message_sent(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key))))
        ||| s.message_sent(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))
    };
    lemma_pre_leads_to_post_by_kubernetes_api(Option::Some(msg), kubernetes_api::handle_request(), pre, post);
    temp_pred_equality::<State>(
        lift_state(post),
        lift_state(|s: State| s.message_sent(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)))))
        .or(lift_state(|s: State| s.message_sent(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))))
    );
}

pub proof fn lemma_get_req_leads_to_ok_resp_if_never_delete(msg: Message, res: ResourceObj)
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_get_request()
                &&& msg.get_get_request().key === res.key
                &&& s.resource_obj_exists(res)
            })
            .and(always(lift_state(|s: State| {
                forall |other: Message|
                !{
                    &&& #[trigger] s.message_sent(other)
                    &&& other.dst === HostId::KubernetesAPI
                    &&& other.is_delete_request()
                    &&& other.get_delete_request().key === res.key
                }
            })))
                .leads_to(lift_state(|s: State| s.message_sent(form_get_resp_msg(msg, Result::Ok(res)))))
        ),
{
    let pre = |s: State| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key === res.key
        &&& s.resource_obj_exists(res)
    };
    let asm = |s: State| {
        forall |other: Message|
            !{
                &&& #[trigger] s.message_sent(other)
                &&& other.dst === HostId::KubernetesAPI
                &&& other.is_delete_request()
                &&& other.get_delete_request().key === res.key
            }
    };
    let post = |s: State| s.message_sent(form_msg(
        msg.dst,
        msg.src,
        get_resp_msg(
            Result::Ok(res),
            msg.get_get_request()
        )
    ));
    lemma_pre_leads_to_post_with_asm_by_kubernetes_api(Option::Some(msg), kubernetes_api::handle_request(), asm, pre, post);
}

pub proof fn lemma_get_req_leads_to_ok_resp_if_res_always_exists(msg: Message, res: ResourceObj)
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_get_request()
                &&& msg.get_get_request().key === res.key
            })
            .and(always(lift_state(|s: State| s.resource_obj_exists(res))))
                .leads_to(lift_state(|s: State| s.message_sent(form_get_resp_msg(msg, Result::Ok(res)))))
        ),
{
    leads_to_weaken_auto::<State>(sm_spec());

    let get_req_msg_sent = |s: State| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key === res.key
    };
    let res_exists = |s: State| s.resource_obj_exists(res);
    let get_req_msg_sent_and_res_exists = |s: State| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key === res.key
        &&& s.resource_obj_exists(res)
    };
    let delete_req_never_sent = |s: State| {
        forall |other: Message|
        !{
            &&& #[trigger] s.message_sent(other)
            &&& other.dst === HostId::KubernetesAPI
            &&& other.is_delete_request()
            &&& other.get_delete_request().key === res.key
        }
    };
    let ok_resp_msg_sent = |s: State| s.message_sent(form_get_resp_msg(msg, Result::Ok(res)));

    lemma_always_res_always_exists_implies_all_delete_never_sent(res);
    // Now we have spec.entails(always(always(lift_state(res_exists)).implies(always(lift_state(delete_req_never_sent)))))
    // We want to add get_req_msg_sent_and_res_exists to both ends by using sandwich_always_implies_temp
    sandwich_always_implies_temp::<State>(sm_spec(),
        lift_state(get_req_msg_sent_and_res_exists),
        always(lift_state(res_exists)),
        always(lift_state(delete_req_never_sent))
    );

    lemma_get_req_leads_to_ok_resp_if_never_delete(msg, res);
    // Use the assert to trigger leads_to_weaken_auto
    // The always-implies formula required by leads_to_weaken_auto is given by the above sandwich_always_implies_temp
    assert(sm_spec().entails(
        lift_state(get_req_msg_sent_and_res_exists).and(always(lift_state(res_exists)))
            .leads_to(lift_state(ok_resp_msg_sent))
    ));

    temp_pred_equality::<State>(
        lift_state(get_req_msg_sent_and_res_exists).and(always(lift_state(res_exists))),
        lift_state(get_req_msg_sent).and(lift_state(res_exists).and(always(lift_state(res_exists))))
    );

    assert(sm_spec().entails(
        lift_state(get_req_msg_sent).and(lift_state(res_exists)).and(always(lift_state(res_exists)))
            .leads_to(lift_state(ok_resp_msg_sent))
    ));
    // Last step: use p_and_always_p_equals_always_p to remove the .and(lift_state(res_exists)) from the premise
    p_and_always_p_equals_always_p::<State>(lift_state(res_exists));
}

pub proof fn lemma_create_req_leads_to_res_exists(msg: Message, res: ResourceObj)
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_create_request()
                &&& msg.get_create_request().obj === res
            })
                .leads_to(lift_state(|s: State| s.resource_key_exists(res.key)))
        ),
{
    let pre = |s: State| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_create_request()
        &&& msg.get_create_request().obj === res
    };
    let post = |s: State| {
        s.resource_key_exists(res.key)
    };
    lemma_pre_leads_to_post_by_kubernetes_api(Option::Some(msg), kubernetes_api::handle_request(), pre, post);
}

pub proof fn lemma_delete_req_leads_to_res_not_exists(msg: Message, res: ResourceObj)
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_delete_request()
                &&& msg.get_delete_request().key === res.key
            })
                .leads_to(lift_state(|s: State| !s.resource_obj_exists(res)))
        ),
{
    let pre = |s: State| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_delete_request()
        &&& msg.get_delete_request().key === res.key
    };
    let post = |s: State| {
        !s.resource_obj_exists(res)
    };
    lemma_pre_leads_to_post_by_kubernetes_api(Option::Some(msg), kubernetes_api::handle_request(), pre, post);
}

pub proof fn lemma_always_res_always_exists_implies_delete_never_sent(msg: Message, res: ResourceObj)
    ensures
        sm_spec().entails(always(
            always(lift_state(|s: State| s.resource_obj_exists(res)))
                .implies(always((|m: Message| lift_state(|s: State| {
                    !{
                        &&& s.message_sent(m)
                        &&& m.dst === HostId::KubernetesAPI
                        &&& m.is_delete_request()
                        &&& m.get_delete_request().key === res.key
                    }
                }))(msg)))
        )),
{
    lemma_delete_req_leads_to_res_not_exists(msg, res);
    leads_to_contraposition::<State>(sm_spec(),
        |s: State| {
            &&& s.message_sent(msg)
            &&& msg.dst === HostId::KubernetesAPI
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key === res.key
        },
        |s: State| !s.resource_obj_exists(res)
    );
    temp_pred_equality::<State>(
        not(lift_state(|s: State| !s.resource_obj_exists(res))),
        lift_state(|s: State| s.resource_obj_exists(res))
    );
    temp_pred_equality::<State>(
        not(lift_state(|s: State| {
            &&& s.message_sent(msg)
            &&& msg.dst === HostId::KubernetesAPI
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key === res.key
        })),
        (|m: Message| lift_state(|s: State| {
            !{
                &&& s.message_sent(m)
                &&& m.dst === HostId::KubernetesAPI
                &&& m.is_delete_request()
                &&& m.get_delete_request().key === res.key
            }
        }))(msg)
    );
}

/// How to prove this? It is obvious according to lemma_always_res_always_exists_implies_delete_never_sent
#[verifier(external_body)]
pub proof fn lemma_always_res_always_exists_implies_all_delete_never_sent(res: ResourceObj)
    ensures
        sm_spec().entails(always(
            always(lift_state(|s: State| s.resource_obj_exists(res)))
                .implies(always(lift_state(|s: State| {
                    forall |msg: Message|
                    !{
                        &&& #[trigger] s.message_sent(msg)
                        &&& msg.dst === HostId::KubernetesAPI
                        &&& msg.is_delete_request()
                        &&& msg.get_delete_request().key === res.key
                    }
                })))
        )),
{}

}
