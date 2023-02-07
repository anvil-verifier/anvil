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

pub proof fn lemma_pre_leads_to_post_by_kubernetes_api<RS>(reconciler: Reconciler<RS>, input: KubernetesAPIActionInput, action: KubernetesAPIAction, pre: StatePred<State<RS>>, post: StatePred<State<RS>>)
    requires
        kubernetes_api().actions.contains(action),
        forall |s, s_prime: State<RS>| pre(s) && #[trigger] next(reconciler)(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<RS>| pre(s) && #[trigger] next(reconciler)(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<RS>| #[trigger] pre(s) ==> kubernetes_api_action_pre(action, input)(s),
    ensures
        sm_spec(reconciler).entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<State<RS>, KubernetesAPIActionInput>(sm_spec(reconciler), |i| kubernetes_api_next().weak_fairness(i), input);

    kubernetes_api_action_pre_implies_next_pre::<RS>(action, input);
    valid_implies_trans::<State<RS>>(lift_state(pre), lift_state(kubernetes_api_action_pre(action, input)), lift_state(kubernetes_api_next().pre(input)));

    kubernetes_api_next().wf1(input, sm_spec(reconciler), next(reconciler), pre, post);
}

pub proof fn lemma_pre_leads_to_post_with_assumption_by_kubernetes_api<RS>(reconciler: Reconciler<RS>, input: KubernetesAPIActionInput, action: KubernetesAPIAction, assumption: StatePred<State<RS>>, pre: StatePred<State<RS>>, post: StatePred<State<RS>>)
    requires
        kubernetes_api().actions.contains(action),
        forall |s, s_prime: State<RS>| pre(s) && #[trigger] next(reconciler)(s, s_prime) && assumption(s) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime: State<RS>| pre(s) && #[trigger] next(reconciler)(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s: State<RS>| #[trigger] pre(s) ==> kubernetes_api_action_pre(action, input)(s),
    ensures
        sm_spec(reconciler).entails(lift_state(pre).and(always(lift_state(assumption))).leads_to(lift_state(post))),
{
    use_tla_forall::<State<RS>, KubernetesAPIActionInput>(sm_spec(reconciler), |i| kubernetes_api_next().weak_fairness(i), input);

    kubernetes_api_action_pre_implies_next_pre::<RS>(action, input);
    valid_implies_trans::<State<RS>>(lift_state(pre), lift_state(kubernetes_api_action_pre(action, input)), lift_state(kubernetes_api_next().pre(input)));

    kubernetes_api_next().wf1_assume(input, sm_spec(reconciler), next(reconciler), assumption, pre, post);
}

pub proof fn lemma_create_req_leads_to_ok_resp<RS>(reconciler: Reconciler<RS>, msg: Message)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<RS>| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_create_request()
                &&& !s.resource_key_exists(msg.get_create_request().obj.key)
            })
            .and(always(lift_state(|s: State<RS>| {
                forall |other: Message|
                    #[trigger] s.message_sent(other) && other.content === msg.content && other.dst === msg.dst
                        ==> other === msg
            })))
                .leads_to(
                    lift_state(|s: State<RS>| {
                        &&& s.message_sent(form_msg(msg.dst, msg.src, create_resp_msg(Result::Ok(msg.get_create_request().obj), msg.get_create_request())))
                        &&& s.resource_key_exists(msg.get_create_request().obj.key)
                    })
                )
        ),
{
    let assumption = |s: State<RS>| {
        forall |other: Message|
            #[trigger] s.message_sent(other) && other.content === msg.content && other.dst === msg.dst
                ==> other === msg
    };
    let pre = |s: State<RS>| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_create_request()
        &&& !s.resource_key_exists(msg.get_create_request().obj.key)
    };
    let post = |s: State<RS>| {
        &&& s.message_sent(form_msg(msg.dst, msg.src, create_resp_msg(Result::Ok(msg.get_create_request().obj), msg.get_create_request())))
        &&& s.resource_key_exists(msg.get_create_request().obj.key)
    };
    lemma_pre_leads_to_post_with_assumption_by_kubernetes_api::<RS>(reconciler, Option::Some(msg), handle_request(), assumption, pre, post);
}

pub proof fn lemma_get_req_leads_to_some_resp<RS>(reconciler: Reconciler<RS>, msg: Message, key: ResourceKey)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<RS>| {
                    &&& s.message_sent(msg)
                    &&& msg.dst === HostId::KubernetesAPI
                    &&& msg.is_get_request()
                    &&& msg.get_get_request().key === key
                })
                .leads_to(
                    lift_state(|s: State<RS>|
                        exists |resp_msg: Message| {
                            &&& #[trigger] s.message_sent(resp_msg)
                            &&& resp_msg_matches_req_msg(resp_msg, msg)
                        }
                    )
                )
        ),
{
    let input = Option::Some(msg);
    let pre = |s: State<RS>| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key === key
    };
    let post = |s: State<RS>| exists |resp_msg: Message| {
        &&& #[trigger] s.message_sent(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
    };
    assert forall |s, s_prime: State<RS>| pre(s) && #[trigger] next(reconciler)(s, s_prime) && kubernetes_api_next().forward(input)(s, s_prime)
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
    lemma_pre_leads_to_post_by_kubernetes_api::<RS>(reconciler, input, handle_request(), pre, post);
}

pub proof fn lemma_get_req_leads_to_ok_or_err_resp<RS>(reconciler: Reconciler<RS>, msg: Message, key: ResourceKey)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<RS>| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_get_request()
                &&& msg.get_get_request().key === key
            })
                .leads_to(
                    lift_state(|s: State<RS>| s.message_sent(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)))))
                    .or(lift_state(|s: State<RS>| s.message_sent(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))))
                )
        ),
{
    let pre = |s: State<RS>| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key === key
    };
    let post = |s: State<RS>| {
        ||| s.message_sent(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key))))
        ||| s.message_sent(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))
    };
    lemma_pre_leads_to_post_by_kubernetes_api::<RS>(reconciler, Option::Some(msg), handle_request(), pre, post);
    temp_pred_equality::<State<RS>>(
        lift_state(post),
        lift_state(|s: State<RS>| s.message_sent(form_get_resp_msg(msg, Result::Ok(s.resource_obj_of(key)))))
        .or(lift_state(|s: State<RS>| s.message_sent(form_get_resp_msg(msg, Result::Err(APIError::ObjectNotFound)))))
    );
}

pub proof fn lemma_get_req_leads_to_ok_resp_if_never_delete<RS>(reconciler: Reconciler<RS>, msg: Message, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<RS>| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_get_request()
                &&& msg.get_get_request().key === res.key
                &&& s.resource_obj_exists(res)
            })
            .and(always(lift_state(|s: State<RS>| {
                forall |other: Message|
                !{
                    &&& #[trigger] s.message_sent(other)
                    &&& other.dst === HostId::KubernetesAPI
                    &&& other.is_delete_request()
                    &&& other.get_delete_request().key === res.key
                }
            })))
                .leads_to(lift_state(|s: State<RS>| s.message_sent(form_get_resp_msg(msg, Result::Ok(res)))))
        ),
{
    let pre = |s: State<RS>| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key === res.key
        &&& s.resource_obj_exists(res)
    };
    let assumption = |s: State<RS>| {
        forall |other: Message|
            !{
                &&& #[trigger] s.message_sent(other)
                &&& other.dst === HostId::KubernetesAPI
                &&& other.is_delete_request()
                &&& other.get_delete_request().key === res.key
            }
    };
    let post = |s: State<RS>| s.message_sent(form_msg(
        msg.dst,
        msg.src,
        get_resp_msg(
            Result::Ok(res),
            msg.get_get_request()
        )
    ));
    lemma_pre_leads_to_post_with_assumption_by_kubernetes_api::<RS>(reconciler, Option::Some(msg), handle_request(), assumption, pre, post);
}

pub proof fn lemma_get_req_leads_to_ok_resp_if_res_always_exists<RS>(reconciler: Reconciler<RS>, msg: Message, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<RS>| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_get_request()
                &&& msg.get_get_request().key === res.key
            })
            .and(always(lift_state(|s: State<RS>| s.resource_obj_exists(res))))
                .leads_to(lift_state(|s: State<RS>| s.message_sent(form_get_resp_msg(msg, Result::Ok(res)))))
        ),
{
    leads_to_weaken_auto::<State<RS>>(sm_spec(reconciler));

    let get_req_msg_sent = |s: State<RS>| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key === res.key
    };
    let res_exists = |s: State<RS>| s.resource_obj_exists(res);
    let get_req_msg_sent_and_res_exists = |s: State<RS>| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_get_request()
        &&& msg.get_get_request().key === res.key
        &&& s.resource_obj_exists(res)
    };
    let delete_req_never_sent = |s: State<RS>| {
        forall |other: Message|
        !{
            &&& #[trigger] s.message_sent(other)
            &&& other.dst === HostId::KubernetesAPI
            &&& other.is_delete_request()
            &&& other.get_delete_request().key === res.key
        }
    };
    let ok_resp_msg_sent = |s: State<RS>| s.message_sent(form_get_resp_msg(msg, Result::Ok(res)));

    lemma_always_res_always_exists_implies_forall_delete_never_sent::<RS>(reconciler, res);
    // Now we have spec.entails(always(always(lift_state(res_exists)).implies(always(lift_state(delete_req_never_sent)))))
    // We want to add get_req_msg_sent_and_res_exists to both ends by using sandwich_always_implies_temp
    sandwich_always_implies_temp::<State<RS>>(sm_spec(reconciler),
        lift_state(get_req_msg_sent_and_res_exists),
        always(lift_state(res_exists)),
        always(lift_state(delete_req_never_sent))
    );

    lemma_get_req_leads_to_ok_resp_if_never_delete::<RS>(reconciler, msg, res);
    // Use the assert to trigger leads_to_weaken_auto
    // The always-implies formula required by leads_to_weaken_auto is given by the above sandwich_always_implies_temp
    assert(sm_spec(reconciler).entails(
        lift_state(get_req_msg_sent_and_res_exists).and(always(lift_state(res_exists)))
            .leads_to(lift_state(ok_resp_msg_sent))
    ));

    temp_pred_equality::<State<RS>>(
        lift_state(get_req_msg_sent_and_res_exists).and(always(lift_state(res_exists))),
        lift_state(get_req_msg_sent).and(lift_state(res_exists).and(always(lift_state(res_exists))))
    );

    assert(sm_spec(reconciler).entails(
        lift_state(get_req_msg_sent).and(lift_state(res_exists)).and(always(lift_state(res_exists)))
            .leads_to(lift_state(ok_resp_msg_sent))
    ));
    // Last step: use p_and_always_p_equals_always_p to remove the .and(lift_state(res_exists)) from the premise
    p_and_always_p_equals_always_p::<State<RS>>(lift_state(res_exists));
}

pub proof fn lemma_create_req_leads_to_res_exists<RS>(reconciler: Reconciler<RS>, msg: Message, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<RS>| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_create_request()
                &&& msg.get_create_request().obj === res
            })
                .leads_to(lift_state(|s: State<RS>| s.resource_key_exists(res.key)))
        ),
{
    let pre = |s: State<RS>| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_create_request()
        &&& msg.get_create_request().obj === res
    };
    let post = |s: State<RS>| {
        s.resource_key_exists(res.key)
    };
    lemma_pre_leads_to_post_by_kubernetes_api::<RS>(reconciler, Option::Some(msg), handle_request(), pre, post);
}

pub proof fn lemma_delete_req_leads_to_res_not_exists<RS>(reconciler: Reconciler<RS>, msg: Message, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(
            lift_state(|s: State<RS>| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_delete_request()
                &&& msg.get_delete_request().key === res.key
            })
                .leads_to(lift_state(|s: State<RS>| !s.resource_obj_exists(res)))
        ),
{
    let pre = |s: State<RS>| {
        &&& s.message_sent(msg)
        &&& msg.dst === HostId::KubernetesAPI
        &&& msg.is_delete_request()
        &&& msg.get_delete_request().key === res.key
    };
    let post = |s: State<RS>| {
        !s.resource_obj_exists(res)
    };
    lemma_pre_leads_to_post_by_kubernetes_api::<RS>(reconciler, Option::Some(msg), handle_request(), pre, post);
}

pub proof fn lemma_always_res_always_exists_implies_delete_never_sent<RS>(reconciler: Reconciler<RS>, msg: Message, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(always(
            always(lift_state(|s: State<RS>| s.resource_obj_exists(res)))
                .implies(always(lift_state(|s: State<RS>| {
                    !{
                        &&& s.message_sent(msg)
                        &&& msg.dst === HostId::KubernetesAPI
                        &&& msg.is_delete_request()
                        &&& msg.get_delete_request().key === res.key
                    }
                })))
        )),
{
    lemma_delete_req_leads_to_res_not_exists::<RS>(reconciler, msg, res);
    leads_to_contraposition::<State<RS>>(sm_spec(reconciler),
        |s: State<RS>| {
            &&& s.message_sent(msg)
            &&& msg.dst === HostId::KubernetesAPI
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key === res.key
        },
        |s: State<RS>| !s.resource_obj_exists(res)
    );
    temp_pred_equality::<State<RS>>(
        not(lift_state(|s: State<RS>| !s.resource_obj_exists(res))),
        lift_state(|s: State<RS>| s.resource_obj_exists(res))
    );
    temp_pred_equality::<State<RS>>(
        not(lift_state(|s: State<RS>| {
            &&& s.message_sent(msg)
            &&& msg.dst === HostId::KubernetesAPI
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key === res.key
        })),
        lift_state(|s: State<RS>| {
            !{
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_delete_request()
                &&& msg.get_delete_request().key === res.key
            }
        })
    );
}

/// How to prove this? It is obvious according to lemma_always_res_always_exists_implies_delete_never_sent
pub proof fn lemma_always_res_always_exists_implies_forall_delete_never_sent<RS>(reconciler: Reconciler<RS>, res: ResourceObj)
    ensures
        sm_spec(reconciler).entails(always(
            always(lift_state(|s: State<RS>| s.resource_obj_exists(res)))
                .implies(always(lift_state(|s: State<RS>| {
                    forall |msg: Message|
                    !{
                        &&& #[trigger] s.message_sent(msg)
                        &&& msg.dst === HostId::KubernetesAPI
                        &&& msg.is_delete_request()
                        &&& msg.get_delete_request().key === res.key
                    }
                })))
        )),
{
    let pre = always(lift_state(|s: State<RS>| s.resource_obj_exists(res)));
    let m_to_always_m_not_sent = |msg: Message| always(lift_state(|s: State<RS>| {
        !{
            &&& s.message_sent(msg)
            &&& msg.dst === HostId::KubernetesAPI
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key === res.key
        }
    }));
    assert forall |msg: Message| sm_spec(reconciler).entails(#[trigger] always(pre.implies(m_to_always_m_not_sent(msg)))) by {
        lemma_always_res_always_exists_implies_delete_never_sent(reconciler, msg, res);
    };
    always_implies_forall_intro::<State<RS>, Message>(sm_spec(reconciler), pre, m_to_always_m_not_sent);

    let m_to_m_not_sent = |msg: Message| lift_state(|s: State<RS>| {
        !{
            &&& s.message_sent(msg)
            &&& msg.dst === HostId::KubernetesAPI
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key === res.key
        }
    });
    tla_forall_always_equality_variant::<State<RS>, Message>(m_to_always_m_not_sent, m_to_m_not_sent);

    let forall_m_to_m_not_sent = lift_state(|s: State<RS>| {
        forall |msg: Message|
        !{
            &&& #[trigger] s.message_sent(msg)
            &&& msg.dst === HostId::KubernetesAPI
            &&& msg.is_delete_request()
            &&& msg.get_delete_request().key === res.key
        }
    });
    assert forall |ex| #[trigger] tla_forall(m_to_m_not_sent).satisfied_by(ex) implies forall_m_to_m_not_sent.satisfied_by(ex) by {
        assert forall |msg: Message|
            !{
                &&& #[trigger] ex.head().message_sent(msg)
                &&& msg.dst === HostId::KubernetesAPI
                &&& msg.is_delete_request()
                &&& msg.get_delete_request().key === res.key
            }
        by {
            assert(m_to_m_not_sent(msg).satisfied_by(ex));
        };
    };
    temp_pred_equality::<State<RS>>(tla_forall(m_to_m_not_sent), forall_m_to_m_not_sent);
}

}
