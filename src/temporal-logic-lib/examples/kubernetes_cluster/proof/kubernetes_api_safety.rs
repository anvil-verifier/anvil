// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::common::*;
use crate::examples::kubernetes_cluster::spec::{
    common::*, controller::common::Reconciler, distributed_system::*,
};
use crate::pervasive::seq::*;
use crate::temporal_logic::*;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_always_res_exists_implies_added_event_sent(r: Reconciler, res: ResourceObj)
    ensures
        sm_spec(r).entails(
            always(
                lift_state(|s: State| s.resource_obj_exists(res))
                    .implies(lift_state(|s: State| s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(res)))))
            )
        ),
{
    init_invariant::<State>(sm_spec(r),
        init(r),
        next(r),
        |s: State| s.resource_obj_exists(res) ==> s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(res)))
    );
    temp_pred_equality::<State>(
        lift_state(|s: State| s.resource_obj_exists(res) ==> s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(res)))),
        lift_state(|s: State| s.resource_obj_exists(res)).implies(lift_state(|s: State| s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(res)))))
    );
}

pub proof fn lemma_always_req_not_sent_implies_resp_not_sent(r: Reconciler, req_msg: Message, resp_msg: Message)
    requires
        req_msg.dst === HostId::KubernetesAPI,
        req_msg.content.is_APIRequest(),
        resp_msg.content.is_APIResponse(),
        resp_msg_matches_req_msg(resp_msg, req_msg),
    ensures
        sm_spec(r).entails(always(
            lift_state(|s: State| !s.message_sent(req_msg))
                .implies(lift_state(|s: State| !s.message_sent(resp_msg)))
        )),
{
    init_invariant::<State>(sm_spec(r),
        init(r),
        next(r),
        |s: State| !s.message_sent(req_msg) ==> !s.message_sent(resp_msg)
    );
    temp_pred_equality::<State>(
        lift_state(|s: State| !s.message_sent(req_msg) ==> !s.message_sent(resp_msg)),
        lift_state(|s: State| !s.message_sent(req_msg)).implies(lift_state(|s: State| !s.message_sent(resp_msg)))
    );
}

}
