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
use crate::reconciler::spec::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use builtin::*;
use builtin_macros::*;
use vstd::{option::*, result::*};

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

pub proof fn lemma_pending_requests_are_eventually_consumed<K: ResourceView, T>(
    spec: TempPred<State<K, T>>, reconciler: Reconciler<K, T>, chan_id: nat,
)
    requires
        spec.entails(lift_state(|s: State<K, T>| s.chan_manager.cur_chan_id == chan_id)),
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
    let pending_requests_num_are_no_more_than_n = |msg_num: nat| lift_state(|s: State<K, T>| {
        s.network_state.in_flight.filter(
            |msg: Message|
                msg.dst.is_KubernetesAPI()
                && msg.content.is_APIRequest()
                && msg.content.get_msg_id() < chan_id
        ).len() <= msg_num
    });
    let no_more_pending_requests = lift_state(|s: State<K, T>| {
        ! exists |msg: Message|
            #[trigger] s.message_in_flight(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_APIRequest()
            && msg.content.get_msg_id() < chan_id
    });
    assert forall |msg_num: nat|
    spec.entails(#[trigger] pending_requests_num_are_no_more_than_n(msg_num).leads_to(no_more_pending_requests)) by {
        lemma_pending_requests_number_is_eventually_zero(spec, reconciler, chan_id, msg_num);
    }
    leads_to_exists_intro(spec, pending_requests_num_are_no_more_than_n, no_more_pending_requests);
    there_exists_n_that_pending_requests_num_are_no_more_than_n::<K, T>(chan_id);
}

proof fn there_exists_n_that_pending_requests_num_are_no_more_than_n<K: ResourceView, T>(chan_id: nat)
    ensures
        tla_exists(|msg_num: nat| lift_state(|s: State<K, T>| {
            s.network_state.in_flight.filter(
                |msg: Message|
                    msg.dst.is_KubernetesAPI()
                    && msg.content.is_APIRequest()
                    && msg.content.get_msg_id() < chan_id
            ).len() <= msg_num
        })) == true_pred::<State<K, T>>(),
{
    let pending_requests_num_are_no_more_than_n = |msg_num: nat| lift_state(|s: State<K, T>| {
        s.network_state.in_flight.filter(
            |msg: Message|
                msg.dst.is_KubernetesAPI()
                && msg.content.is_APIRequest()
                && msg.content.get_msg_id() < chan_id
        ).len() <= msg_num
    });
    assert forall |ex| #[trigger] true_pred().satisfied_by(ex) implies
    tla_exists(pending_requests_num_are_no_more_than_n).satisfied_by(ex) by {
        let current_msg_num = ex.head().network_state.in_flight.filter(
            |msg: Message|
                msg.dst.is_KubernetesAPI()
                && msg.content.is_APIRequest()
                && msg.content.get_msg_id() < chan_id
        ).len();
        assert(pending_requests_num_are_no_more_than_n(current_msg_num).satisfied_by(ex));
    }
    temp_pred_equality(tla_exists(pending_requests_num_are_no_more_than_n), true_pred());
}

#[verifier(external_body)]
proof fn lemma_pending_requests_number_is_eventually_zero<K: ResourceView, T>(
    spec: TempPred<State<K, T>>, reconciler: Reconciler<K, T>, chan_id: nat, msg_num: nat,
)
    requires
        spec.entails(lift_state(|s: State<K, T>| s.chan_manager.cur_chan_id == chan_id)),
        spec.entails(always(lift_action(next(reconciler)))),
        spec.entails(tla_forall(|i| kubernetes_api_next().weak_fairness(i))),
    ensures
        spec.entails(
            lift_state(|s: State<K, T>| {
                s.network_state.in_flight.filter(
                    |msg: Message|
                        msg.dst.is_KubernetesAPI()
                        && msg.content.is_APIRequest()
                        && msg.content.get_msg_id() < chan_id
                ).len() <= msg_num
            }).leads_to(lift_state(|s: State<K, T>| {
                ! exists |msg: Message|
                    #[trigger] s.message_in_flight(msg)
                    && msg.dst.is_KubernetesAPI()
                    && msg.content.is_APIRequest()
                    && msg.content.get_msg_id() < chan_id
            }))
        )
    decreases
        msg_num
{}

}
