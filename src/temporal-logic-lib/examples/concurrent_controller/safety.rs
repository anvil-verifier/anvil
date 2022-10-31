// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::concurrent_controller::state_machine::*;
use crate::pervasive::seq::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

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


pub proof fn lemma_always_delete_cr_req_not_sent_implies_delete_pod_and_vol_req_not_sent(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(always(
            lift_state(|s| !message_sent(s, delete_req_msg(cr.key)))
                .implies(lift_state(
                    |s| !message_sent(s, delete_req_msg(ResourceKey{
                        name: cr.key.name + sts_suffix() + pod_suffix(),
                        kind: ResourceKind::PodKind
                    }))
                    && !message_sent(s, delete_req_msg(ResourceKey{
                        name: cr.key.name + sts_suffix() + vol_suffix(),
                        kind: ResourceKind::VolumeKind
                    }))
                ))
        )),
{
    let delete_cr_req_msg = delete_req_msg(cr.key);
    let delete_cr_resp_msg = delete_resp_msg(cr.key);
    let delete_sts_req_msg = delete_req_msg(ResourceKey{
        name: cr.key.name + sts_suffix(),
        kind: ResourceKind::StatefulSetKind,
    });
    lemma_always_delete_req_not_sent_implies_delete_resp_not_sent(delete_cr_req_msg);
    lemma_always_delete_cr_resp_not_sent_implies_delete_sts_req_not_sent(delete_cr_resp_msg);
    lemma_always_delete_sts_req_not_sent_implies_delete_pod_and_vol_req_not_sent(delete_sts_req_msg);

    always_implies_trans_auto::<CState>(sm_spec());
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
                    name: delete_cr_resp_msg.get_DeleteResponse_0().key.name + sts_suffix(),
                    kind: ResourceKind::StatefulSetKind
                }))))
        )),
{
    seq_unequal_preserved_by_add_auto::<char>(sts_suffix());
    init_invariant::<CState>(sm_spec(),
        init(),
        next(),
        |s: CState| !message_sent(s, delete_cr_resp_msg) ==> !message_sent(s, delete_req_msg(ResourceKey{
            name: delete_cr_resp_msg.get_DeleteResponse_0().key.name + sts_suffix(),
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
                    name: delete_sts_req_msg.get_DeleteRequest_0().key.name + pod_suffix(),
                    kind: ResourceKind::PodKind
                }))
                && !message_sent(s, delete_req_msg(ResourceKey{
                    name: delete_sts_req_msg.get_DeleteRequest_0().key.name + vol_suffix(),
                    kind: ResourceKind::VolumeKind
                })))
            )
        )),
{
    seq_unequal_preserved_by_add_auto::<char>(pod_suffix());
    seq_unequal_preserved_by_add_auto::<char>(vol_suffix());
    init_invariant::<CState>(sm_spec(),
        init(),
        next(),
        |s: CState| !message_sent(s, delete_sts_req_msg)
        ==> !message_sent(s, delete_req_msg(ResourceKey{
                name: delete_sts_req_msg.get_DeleteRequest_0().key.name + pod_suffix(),
                kind: ResourceKind::PodKind
            }))
            && !message_sent(s, delete_req_msg(ResourceKey{
                name: delete_sts_req_msg.get_DeleteRequest_0().key.name + vol_suffix(),
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
                && !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + pod_suffix(), kind: ResourceKind::PodKind}))
                && !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + vol_suffix(), kind: ResourceKind::VolumeKind}))
                ==> resource_exists(s, ResourceKey{name: sts_name + pod_suffix(), kind: ResourceKind::PodKind})
                    && resource_exists(s, ResourceKey{name: sts_name + vol_suffix(), kind: ResourceKind::VolumeKind})
            }
        ))),
{
    reveal_strlit("_pod");
    reveal_strlit("_vol");
    assert(pod_suffix()[1] !== vol_suffix()[1]);
    assert(!pod_suffix().ext_equal(vol_suffix()));
    seq_unequal_introduced_by_add_auto::<char>(pod_suffix(), vol_suffix());
    init_invariant::<CState>(sm_spec(),
        init(),
        next(),
        |s: CState| {
            s.attached.contains(sts_name)
            && !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + pod_suffix(), kind: ResourceKind::PodKind}))
            && !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + vol_suffix(), kind: ResourceKind::VolumeKind}))
            ==> resource_exists(s, ResourceKey{name: sts_name + pod_suffix(), kind: ResourceKind::PodKind})
                && resource_exists(s, ResourceKey{name: sts_name + vol_suffix(), kind: ResourceKind::VolumeKind})
        }
    );
}

pub proof fn seq_unequal_preserved_by_add<A>(s1: Seq<A>, s2: Seq<A>, suffix: Seq<A>)
    requires
        s1 !== s2
    ensures
        s1 + suffix !== s2 + suffix
{
    assert(!s1.ext_equal(s2));
    if s1.len() === s2.len() {
        let witness_idx = choose |i: int| 0 <= i < s1.len() && s1[i] !== s2[i];
        assert((s1 + suffix)[witness_idx] !== (s2 + suffix)[witness_idx]);
    } else {
        assert((s1 + suffix).len() !== (s2 + suffix).len());
    }
}

pub proof fn seq_unequal_preserved_by_add_auto<A>(suffix: Seq<A>)
    ensures
        forall |s1, s2: Seq<A>| s1 !== s2 ==> s1 + suffix !== s2 + suffix
{
    assert forall |s1, s2: Seq<A>| s1 !== s2 implies s1 + suffix !== s2 + suffix by {
        seq_unequal_preserved_by_add(s1, s2, suffix);
    };
}

pub proof fn seq_unequal_introduced_by_add<A>(s: Seq<A>, suffix1: Seq<A>, suffix2: Seq<A>)
    requires
        suffix1 !== suffix2
    ensures
        s + suffix1 !== s + suffix2
{
    assert(!suffix1.ext_equal(suffix2));
    if suffix1.len() === suffix2.len() {
        let witness_idx = choose |i: int| 0 <= i < suffix1.len() && suffix1[i] !== suffix2[i];
        assert((s + suffix1)[witness_idx + s.len()] !== (s + suffix2)[witness_idx + s.len()]);
    } else {
        assert((s + suffix1).len() !== (s + suffix2).len());
    }
}

pub proof fn seq_unequal_introduced_by_add_auto<A>(suffix1: Seq<A>, suffix2: Seq<A>)
    ensures
        forall |s: Seq<A>| suffix1 !== suffix2 ==> s + suffix1 !== s + suffix2
{
    assert forall |s: Seq<A>| suffix1 !== suffix2 implies s + suffix1 !== s + suffix2 by {
        seq_unequal_introduced_by_add(s, suffix1, suffix2);
    };
}

}
