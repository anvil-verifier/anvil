// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::concurrent::state_machine::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::vstd_ext::seq_lib::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub proof fn lemma_always_res_exists_implies_create_req_sent(res: ResourceObj)
    ensures
        sm_spec().entails(always(
            lift_state(|s| resource_exists(s, res.key))
                .implies(lift_state(|s| message_sent(s, create_req_msg(res.key))))
        )),
{
    init_invariant::<CState>(sm_spec(),
        init(),
        next(),
        |s: CState| resource_exists(s, res.key) ==> message_sent(s, create_req_msg(res.key))
    );
    implies_preserved_by_always_auto::<CState>();
    entails_weaken_auto::<CState>(sm_spec());
}

pub proof fn lemma_always_delete_req_not_sent_implies_delete_resp_not_sent(delete_req_msg: Message)
    requires
        delete_req_msg.is_DeleteRequest(),
    ensures
        sm_spec().entails(always(
            lift_state(|s| !message_sent(s, delete_req_msg))
                .implies(lift_state(|s| !message_sent(s, delete_resp_msg(delete_req_msg.get_DeleteRequest_0().key))))
        )),
{
    init_invariant::<CState>(sm_spec(),
        init(),
        next(),
        |s: CState| !message_sent(s, delete_req_msg) ==> !message_sent(s, delete_resp_msg(delete_req_msg.get_DeleteRequest_0().key))
    );
    implies_preserved_by_always_auto::<CState>();
    entails_weaken_auto::<CState>(sm_spec());
}

pub proof fn lemma_always_delete_cr_resp_not_sent_implies_delete_sts_req_not_sent(delete_cr_resp_msg: Message)
    requires
        delete_cr_resp_msg.is_DeleteResponse(),
        delete_cr_resp_msg.get_DeleteResponse_0().key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(always(
            lift_state(|s: CState| !message_sent(s, delete_cr_resp_msg))
                .implies(lift_state(|s| !message_sent(s, delete_req_msg(ResourceKey{
                    name: delete_cr_resp_msg.get_DeleteResponse_0().key.name + new_strlit("-sts")@,
                    kind: ResourceKind::StatefulSetKind
                }))))
        )),
{
    seq_unequal_preserved_by_add_auto::<char>(new_strlit("-sts")@);
    init_invariant::<CState>(sm_spec(),
        init(),
        next(),
        |s: CState| !message_sent(s, delete_cr_resp_msg) ==> !message_sent(s, delete_req_msg(ResourceKey{
            name: delete_cr_resp_msg.get_DeleteResponse_0().key.name + new_strlit("-sts")@,
            kind: ResourceKind::StatefulSetKind
        }))
    );
    implies_preserved_by_always_auto::<CState>();
    entails_weaken_auto::<CState>(sm_spec());
}

pub proof fn lemma_always_delete_sts_req_not_sent_implies_delete_pod_and_vol_req_not_sent(delete_sts_req_msg: Message)
    requires
        delete_sts_req_msg.is_DeleteRequest(),
        delete_sts_req_msg.get_DeleteRequest_0().key.kind.is_StatefulSetKind(),
    ensures
        sm_spec().entails(always(
            lift_state(|s: CState| !message_sent(s, delete_sts_req_msg))
            .implies(lift_state(
                |s| !message_sent(s, delete_req_msg(ResourceKey{
                    name: delete_sts_req_msg.get_DeleteRequest_0().key.name + new_strlit("-pod")@,
                    kind: ResourceKind::PodKind
                }))
                && !message_sent(s, delete_req_msg(ResourceKey{
                    name: delete_sts_req_msg.get_DeleteRequest_0().key.name + new_strlit("-vol")@,
                    kind: ResourceKind::VolumeKind
                })))
            )
        )),
{
    seq_unequal_preserved_by_add_auto::<char>(new_strlit("-pod")@);
    seq_unequal_preserved_by_add_auto::<char>(new_strlit("-vol")@);
    init_invariant::<CState>(sm_spec(),
        init(),
        next(),
        |s: CState| !message_sent(s, delete_sts_req_msg)
        ==> !message_sent(s, delete_req_msg(ResourceKey{
                name: delete_sts_req_msg.get_DeleteRequest_0().key.name + new_strlit("-pod")@,
                kind: ResourceKind::PodKind
            }))
            && !message_sent(s, delete_req_msg(ResourceKey{
                name: delete_sts_req_msg.get_DeleteRequest_0().key.name + new_strlit("-vol")@,
                kind: ResourceKind::VolumeKind
            }))
    );
    implies_preserved_by_always_auto::<CState>();
    entails_weaken_auto::<CState>(sm_spec());
}

pub proof fn lemma_always_attached_and_delete_req_not_sent_implies_res_exists(sts_name: Seq<char>)
    ensures
        sm_spec().entails(always(lift_state(
            |s: CState| {
                s.attached.contains(sts_name)
                && !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + new_strlit("-pod")@, kind: ResourceKind::PodKind}))
                && !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + new_strlit("-vol")@, kind: ResourceKind::VolumeKind}))
                ==> resource_exists(s, ResourceKey{name: sts_name + new_strlit("-pod")@, kind: ResourceKind::PodKind})
                    && resource_exists(s, ResourceKey{name: sts_name + new_strlit("-vol")@, kind: ResourceKind::VolumeKind})
            }
        ))),
{
    init_invariant::<CState>(sm_spec(),
        init(),
        next(),
        |s: CState| {
            s.attached.contains(sts_name)
            && !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + new_strlit("-pod")@, kind: ResourceKind::PodKind}))
            && !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + new_strlit("-vol")@, kind: ResourceKind::VolumeKind}))
            ==> resource_exists(s, ResourceKey{name: sts_name + new_strlit("-pod")@, kind: ResourceKind::PodKind})
                && resource_exists(s, ResourceKey{name: sts_name + new_strlit("-vol")@, kind: ResourceKind::VolumeKind})
        }
    );
}



}
