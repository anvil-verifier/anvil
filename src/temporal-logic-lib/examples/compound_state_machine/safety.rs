// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::common::*;
use crate::examples::compound_state_machine::{
    common::*,
    distributed_system::{init, message_sent, next, resource_exists, sm_spec, State},
};
use crate::pervasive::seq::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_always_res_exists_implies_create_req_sent(res: ResourceObj)
    ensures
        sm_spec().entails(always(
            lift_state(resource_exists(res.key))
                .implies(lift_state(message_sent(create_req_msg(res.key))))
        )),
{
    init_invariant::<State>(sm_spec(),
        init(),
        next(),
        |s| resource_exists(res.key)(s) ==> message_sent(create_req_msg(res.key))(s)
    );
    implies_preserved_by_always_auto::<State>();
    entails_weaken_auto::<State>(sm_spec());
}

pub proof fn lemma_always_delete_req_not_sent_implies_delete_resp_not_sent(delete_req_msg: Message)
    requires
        delete_req_msg.is_DeleteRequest(),
    ensures
        sm_spec().entails(always(
            lift_state(|s| !message_sent(delete_req_msg)(s))
                .implies(lift_state(|s| !message_sent(delete_resp_msg(delete_req_msg.get_DeleteRequest_0().key))(s)))
        )),
{
    init_invariant::<State>(sm_spec(),
        init(),
        next(),
        |s| !message_sent(delete_req_msg)(s) ==> !message_sent(delete_resp_msg(delete_req_msg.get_DeleteRequest_0().key))(s)
    );
    implies_preserved_by_always_auto::<State>();
    entails_weaken_auto::<State>(sm_spec());
}

pub proof fn lemma_always_delete_cr_resp_not_sent_implies_delete_sts_req_not_sent(delete_cr_resp_msg: Message)
    requires
        delete_cr_resp_msg.is_DeleteResponse(),
        delete_cr_resp_msg.get_DeleteResponse_0().key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(always(
            lift_state(|s| !message_sent(delete_cr_resp_msg)(s))
                .implies(lift_state(|s| !message_sent(delete_req_msg(ResourceKey{
                    name: delete_cr_resp_msg.get_DeleteResponse_0().key.name + sts_suffix(),
                    kind: ResourceKind::StatefulSetKind
                }))(s)))
        )),
{
    seq_unequal_preserved_by_add_auto::<char>(sts_suffix());
    init_invariant::<State>(sm_spec(),
        init(),
        next(),
        |s| !message_sent(delete_cr_resp_msg)(s) ==> !message_sent(delete_req_msg(ResourceKey{
            name: delete_cr_resp_msg.get_DeleteResponse_0().key.name + sts_suffix(),
            kind: ResourceKind::StatefulSetKind
        }))(s)
    );
    implies_preserved_by_always_auto::<State>();
    entails_weaken_auto::<State>(sm_spec());
}

pub proof fn lemma_always_delete_sts_req_not_sent_implies_delete_pod_and_vol_req_not_sent(delete_sts_req_msg: Message)
    requires
        delete_sts_req_msg.is_DeleteRequest(),
        delete_sts_req_msg.get_DeleteRequest_0().key.kind.is_StatefulSetKind(),
    ensures
        sm_spec().entails(always(
            lift_state(|s| !message_sent(delete_sts_req_msg)(s))
            .implies(lift_state(
                |s| !message_sent(delete_req_msg(ResourceKey{
                    name: delete_sts_req_msg.get_DeleteRequest_0().key.name + pod_suffix(),
                    kind: ResourceKind::PodKind
                }))(s)
                && !message_sent(delete_req_msg(ResourceKey{
                    name: delete_sts_req_msg.get_DeleteRequest_0().key.name + vol_suffix(),
                    kind: ResourceKind::VolumeKind
                }))(s))
            )
        )),
{
    seq_unequal_preserved_by_add_auto::<char>(pod_suffix());
    seq_unequal_preserved_by_add_auto::<char>(vol_suffix());
    init_invariant::<State>(sm_spec(),
        init(),
        next(),
        |s| !message_sent(delete_sts_req_msg)(s)
        ==> !message_sent(delete_req_msg(ResourceKey{
                name: delete_sts_req_msg.get_DeleteRequest_0().key.name + pod_suffix(),
                kind: ResourceKind::PodKind
            }))(s)
            && !message_sent(delete_req_msg(ResourceKey{
                name: delete_sts_req_msg.get_DeleteRequest_0().key.name + vol_suffix(),
                kind: ResourceKind::VolumeKind
            }))(s)
    );
    implies_preserved_by_always_auto::<State>();
    entails_weaken_auto::<State>(sm_spec());
}

}
