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
    leads_to_eq_auto::<State>(sm_spec());
    use_tla_forall::<State, Option<Message>>(sm_spec(), |recv| weak_fairness(distributed_system::kubernetes_api_next().forward(recv)), Option::Some(msg));

    distributed_system::kubernetes_api_step_enabled(kubernetes_api::Step::HandleRequest, Option::Some(msg));
    wf1::<State>(sm_spec(),
        next(),
        distributed_system::kubernetes_api_next().forward(Option::Some(msg)),
        distributed_system::kubernetes_api_next().step_pre(kubernetes_api::Step::HandleRequest, Option::Some(msg)),
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
    leads_to_eq_auto::<State>(sm_spec());
    use_tla_forall::<State, Option<Message>>(sm_spec(), |recv| weak_fairness(distributed_system::kubernetes_api_next().forward(recv)), Option::Some(msg));

    distributed_system::kubernetes_api_step_enabled(kubernetes_api::Step::HandleRequest, Option::Some(msg));
    wf1::<State>(sm_spec(),
        next(),
        distributed_system::kubernetes_api_next().forward(Option::Some(msg)),
        distributed_system::kubernetes_api_next().step_pre(kubernetes_api::Step::HandleRequest, Option::Some(msg)),
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

    leads_to_eq_auto::<State>(sm_spec());
    use_tla_forall::<State, Option<Message>>(sm_spec(), |recv| weak_fairness(distributed_system::kubernetes_api_next().forward(recv)), Option::Some(msg));
    use_tla_forall::<State, Option<Message>>(sm_spec(), |recv| weak_fairness(distributed_system::kubernetes_api_next().forward(recv)), Option::Some(sub_res_msg));

    distributed_system::kubernetes_api_step_enabled(kubernetes_api::Step::HandleRequest, Option::Some(msg));
    wf1::<State>(sm_spec(),
        next(),
        distributed_system::kubernetes_api_next().forward(Option::Some(msg)),
        distributed_system::kubernetes_api_next().step_pre(kubernetes_api::Step::HandleRequest, Option::Some(msg)),
        message_sent(sub_res_msg)
    );

    distributed_system::kubernetes_api_step_enabled(kubernetes_api::Step::HandleRequest, Option::Some(sub_res_msg));
    wf1::<State>(sm_spec(),
        next(),
        distributed_system::kubernetes_api_next().forward(Option::Some(sub_res_msg)),
        distributed_system::kubernetes_api_next().step_pre(kubernetes_api::Step::HandleRequest, Option::Some(sub_res_msg)),
        resource_exists(sub_res_key)
    );

    leads_to_trans::<State>(sm_spec(),
        message_sent(msg),
        message_sent(sub_res_msg),
        resource_exists(sub_res_key)
    );
}

}
