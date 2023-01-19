// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::compound_state_machine::{
    common::*,
    distributed_system,
    distributed_system::{
        kubernetes_api_action_pre, kubernetes_api_action_pre_implies_next_pre, kubernetes_api_next,
        message_sent, next, resource_exists, sm_spec, State,
    },
    kubernetes_api,
};
use crate::pervasive::option::*;
use crate::temporal_logic::*;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {


pub proof fn lemma_msg_sent_leads_to_post_by_kubernetes_api(msg: Message, action: kubernetes_api::KubernetesAPIAction, post: StatePred<State>)
    requires
        kubernetes_api::kubernetes_api().actions.contains(action),
        forall |s, s_prime: State| kubernetes_api_next().pre(Option::Some(msg))(s) && #[trigger] next()(s, s_prime) ==> kubernetes_api_next().pre(Option::Some(msg))(s_prime) || post(s_prime),
        forall |s, s_prime: State| kubernetes_api_next().pre(Option::Some(msg))(s) && #[trigger] next()(s, s_prime) && kubernetes_api_next().forward(Option::Some(msg))(s, s_prime) ==> post(s_prime),
        forall |s: State| #[trigger] message_sent(msg)(s) ==> kubernetes_api_action_pre(action, Option::Some(msg))(s),
    ensures
        sm_spec().entails(lift_state(message_sent(msg)).leads_to(lift_state(post))),
{
    let recv = Option::Some(msg);
    let pre = kubernetes_api_action_pre(action, recv);

    leads_to_weaken_auto::<State>(sm_spec());
    use_tla_forall::<State, Option<Message>>(sm_spec(), |r| kubernetes_api_next().weak_fairness(r), recv);

    kubernetes_api_action_pre_implies_next_pre(action, recv);
    valid_implies_trans::<State>(lift_state(message_sent(msg)), lift_state(kubernetes_api_action_pre(action, recv)), lift_state(kubernetes_api_next().pre(recv)));

    kubernetes_api_next().wf1(recv, sm_spec(), next(), message_sent(msg), post);

    assert(sm_spec().entails(lift_state(pre).leads_to(lift_state(post))));
}

pub proof fn lemma_create_req_leads_to_create_resp(msg: Message)
    requires
        msg.is_CreateRequest(),
    ensures
        sm_spec().entails(lift_state(message_sent(msg)).leads_to(lift_state(message_sent(create_resp_msg(msg.get_CreateRequest_0().obj.key))))),
{
    lemma_msg_sent_leads_to_post_by_kubernetes_api(msg, kubernetes_api::handle_request(), message_sent(create_resp_msg(msg.get_CreateRequest_0().obj.key)));
}

pub proof fn lemma_delete_req_leads_to_res_not_exists(msg: Message)
    requires
        msg.is_DeleteRequest(),
    ensures
        sm_spec().entails(lift_state(message_sent(msg)).leads_to(lift_state(|s| !resource_exists(msg.get_DeleteRequest_0().key)(s)))),
{
    lemma_msg_sent_leads_to_post_by_kubernetes_api(msg, kubernetes_api::handle_request(), |s| !resource_exists(msg.get_DeleteRequest_0().key)(s));
}

pub proof fn lemma_create_sts_req_sent_leads_to_pod_exists_and_vol_exists(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().obj.key.kind.is_StatefulSetKind(),
    ensures
        sm_spec()
            .entails(lift_state(message_sent(msg))
                .leads_to(lift_state(resource_exists(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind})))),
        sm_spec()
            .entails(lift_state(message_sent(msg))
                .leads_to(lift_state(resource_exists(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind})))),
{
    let create_pod_req_msg = create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind});
    lemma_msg_sent_leads_to_post_by_kubernetes_api(msg, kubernetes_api::handle_request(), message_sent(create_pod_req_msg));
    lemma_msg_sent_leads_to_post_by_kubernetes_api(create_pod_req_msg, kubernetes_api::handle_request(), resource_exists(create_pod_req_msg.get_CreateRequest_0().obj.key));
    leads_to_trans::<State>(sm_spec(), message_sent(msg), message_sent(create_pod_req_msg), resource_exists(create_pod_req_msg.get_CreateRequest_0().obj.key));

    let create_vol_req_msg = create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind});
    lemma_msg_sent_leads_to_post_by_kubernetes_api(msg, kubernetes_api::handle_request(), message_sent(create_vol_req_msg));
    lemma_msg_sent_leads_to_post_by_kubernetes_api(create_vol_req_msg, kubernetes_api::handle_request(), resource_exists(create_vol_req_msg.get_CreateRequest_0().obj.key));
    leads_to_trans::<State>(sm_spec(), message_sent(msg), message_sent(create_vol_req_msg), resource_exists(create_vol_req_msg.get_CreateRequest_0().obj.key));
}

}
