// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::compound_state_machine::{
    common::*,
    distributed_system,
    distributed_system::{message_sent, next, resource_exists, sm_spec, State},
    kubernetes_api,
};
use crate::pervasive::option::*;
use crate::temporal_logic::*;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_create_req_leads_to_create_resp(msg: Message)
    requires
        msg.is_CreateRequest(),
    ensures
        sm_spec().entails(
            lift_state(message_sent(msg)).leads_to(lift_state(message_sent(create_resp_msg(msg.get_CreateRequest_0().obj.key))))
        ),
{
    let recv = Option::Some(msg);
    let pre = distributed_system::kubernetes_api_action_pre(kubernetes_api::handle_request(), recv);
    let post = message_sent(create_resp_msg(msg.get_CreateRequest_0().obj.key));

    leads_to_weaken_auto::<State>(sm_spec());
    use_tla_forall::<State, Option<Message>>(sm_spec(), |r| weak_fairness(distributed_system::kubernetes_api_next().forward(r)), recv);

    distributed_system::kubernetes_api_action_pre_implies_next_pre(kubernetes_api::handle_request(), recv);
    distributed_system::kubernetes_api_next().wf1(recv, sm_spec(), next(), post);

    assert(sm_spec().entails(lift_state(pre).leads_to(lift_state(post))));
}

pub proof fn lemma_delete_req_leads_to_res_not_exists(msg: Message)
    requires
        msg.is_DeleteRequest(),
    ensures
        sm_spec().entails(
            lift_state(message_sent(msg)).leads_to(lift_state(|s| !resource_exists(msg.get_DeleteRequest_0().key)(s)))
        ),
{
    let recv = Option::Some(msg);
    let pre = distributed_system::kubernetes_api_action_pre(kubernetes_api::handle_request(), recv);
    let post = |s| !resource_exists(msg.get_DeleteRequest_0().key)(s);

    leads_to_weaken_auto::<State>(sm_spec());
    use_tla_forall::<State, Option<Message>>(sm_spec(), |r| weak_fairness(distributed_system::kubernetes_api_next().forward(r)), recv);

    distributed_system::kubernetes_api_action_pre_implies_next_pre(kubernetes_api::handle_request(), recv);
    distributed_system::kubernetes_api_next().wf1(recv, sm_spec(), next(), post);

    assert(sm_spec().entails(lift_state(pre).leads_to(lift_state(post))));
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
    lemma_create_sts_req_sent_leads_to(msg, create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind}));
    lemma_create_sts_req_sent_leads_to(msg, create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind}));
}

proof fn lemma_create_sts_req_sent_leads_to(msg: Message, sub_res_msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().obj.key.kind.is_StatefulSetKind(),
        sub_res_msg.is_CreateRequest(),
        sub_res_msg.get_CreateRequest_0().obj.key === (ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind})
        || sub_res_msg.get_CreateRequest_0().obj.key === (ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind}),
    ensures
        sm_spec()
            .entails(lift_state(message_sent(msg))
                .leads_to(lift_state(resource_exists(sub_res_msg.get_CreateRequest_0().obj.key)))),
{
    let recv_msg = Option::Some(msg);
    let recv_sub_res_msg = Option::Some(sub_res_msg);
    let pre = distributed_system::kubernetes_api_action_pre(kubernetes_api::handle_request(), recv_msg);
    let post = resource_exists(sub_res_msg.get_CreateRequest_0().obj.key);

    leads_to_weaken_auto::<State>(sm_spec());
    use_tla_forall::<State, Option<Message>>(sm_spec(), |r| weak_fairness(distributed_system::kubernetes_api_next().forward(r)), recv_msg);
    use_tla_forall::<State, Option<Message>>(sm_spec(), |r| weak_fairness(distributed_system::kubernetes_api_next().forward(r)), recv_sub_res_msg);

    distributed_system::kubernetes_api_action_pre_implies_next_pre(kubernetes_api::handle_request(), recv_msg);
    distributed_system::kubernetes_api_next().wf1(recv_msg, sm_spec(), next(), message_sent(sub_res_msg));
    assert(sm_spec().entails(lift_state(pre).leads_to(lift_state(message_sent(sub_res_msg)))));

    distributed_system::kubernetes_api_action_pre_implies_next_pre(kubernetes_api::handle_request(), recv_sub_res_msg);
    distributed_system::kubernetes_api_next().wf1(recv_sub_res_msg, sm_spec(), next(), post);
    assert(sm_spec().entails(lift_state(message_sent(sub_res_msg)).leads_to(lift_state(post))));

    leads_to_trans::<State>(sm_spec(), pre, message_sent(sub_res_msg), post);
}

}
