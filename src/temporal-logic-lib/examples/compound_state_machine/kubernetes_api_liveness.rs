// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::compound_state_machine::{common::*, compound::*, kubernetes_api};
use crate::pervasive::option::*;
use crate::temporal_logic::*;
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
    leads_to_eq_auto::<CompoundState>(sm_spec());
    use_tla_forall::<CompoundState, Option<Message>>(sm_spec(), |recv| weak_fairness(kubernetes_api_action(recv)), Option::Some(msg));

    kubernetes_api_action_enabled(Option::Some(msg), kubernetes_api::handle_request());
    wf1::<CompoundState>(sm_spec(),
        next(),
        kubernetes_api_action(Option::Some(msg)),
        kubernetes_api_action_pre(Option::Some(msg), kubernetes_api::handle_request()),
        message_sent(create_resp_msg(msg.get_CreateRequest_0().obj.key)),
    );
}

pub proof fn lemma_delete_req_leads_to_res_not_exists(msg: Message)
    requires
        msg.is_DeleteRequest(),
    ensures
        sm_spec().entails(
            lift_state(message_sent(msg)).leads_to(lift_state(|s| !resource_exists(msg.get_DeleteRequest_0().key)(s)))
        ),
{
    leads_to_eq_auto::<CompoundState>(sm_spec());
    use_tla_forall::<CompoundState, Option<Message>>(sm_spec(), |recv| weak_fairness(kubernetes_api_action(recv)), Option::Some(msg));

    kubernetes_api_action_enabled(Option::Some(msg), kubernetes_api::handle_request());
    wf1::<CompoundState>(sm_spec(),
        next(),
        kubernetes_api_action(Option::Some(msg)),
        kubernetes_api_action_pre(Option::Some(msg), kubernetes_api::handle_request()),
        |s| !resource_exists(msg.get_DeleteRequest_0().key)(s)
    );
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
    let sub_res_key = sub_res_msg.get_CreateRequest_0().obj.key;

    leads_to_eq_auto::<CompoundState>(sm_spec());
    use_tla_forall::<CompoundState, Option<Message>>(sm_spec(), |recv| weak_fairness(kubernetes_api_action(recv)), Option::Some(msg));
    use_tla_forall::<CompoundState, Option<Message>>(sm_spec(), |recv| weak_fairness(kubernetes_api_action(recv)), Option::Some(sub_res_msg));

    kubernetes_api_action_enabled(Option::Some(msg), kubernetes_api::handle_request());
    wf1::<CompoundState>(sm_spec(),
        next(),
        kubernetes_api_action(Option::Some(msg)),
        kubernetes_api_action_pre(Option::Some(msg), kubernetes_api::handle_request()),
        message_sent(sub_res_msg)
    );

    kubernetes_api_action_enabled(Option::Some(sub_res_msg), kubernetes_api::handle_request());
    wf1::<CompoundState>(sm_spec(),
        next(),
        kubernetes_api_action(Option::Some(sub_res_msg)),
        kubernetes_api_action_pre(Option::Some(sub_res_msg), kubernetes_api::handle_request()),
        resource_exists(sub_res_key)
    );

    leads_to_trans::<CompoundState>(sm_spec(),
        message_sent(msg),
        message_sent(sub_res_msg),
        resource_exists(sub_res_key)
    );
}

}
