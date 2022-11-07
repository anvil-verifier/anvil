// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::concurrent_controller::safety::*;
use crate::examples::concurrent_controller::state_machine::*;
use crate::pervasive::seq::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

spec fn liveness_property(cr: ResourceObj) -> TempPred<CState>
    recommends
        cr.key.kind.is_CustomResourceKind(),
{
    let cr_name = cr.key.name;
    let sts_name = cr_name + sts_suffix();
    let pod_name = sts_name + pod_suffix();
    let vol_name = sts_name + vol_suffix();

    always(lift_state(|s| resource_exists(s, cr.key)))
    .leads_to(always(lift_state(
        |s: CState| {
            &&& resource_exists(s, ResourceKey{name: pod_name, kind: ResourceKind::PodKind})
            &&& resource_exists(s, ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind})
        }
    )))
}

proof fn liveness_proof_for_all_cr()
    ensures
        forall |cr: ResourceObj| cr.key.kind.is_CustomResourceKind()
          ==> sm_spec().entails(#[trigger] liveness_property(cr)),
{
    assert forall |cr: ResourceObj| cr.key.kind.is_CustomResourceKind()
    implies sm_spec().entails(#[trigger] liveness_property(cr)) by {
        liveness_proof(cr);
    };
}

proof fn liveness_proof(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(liveness_property(cr)),
{
    let cr_name = cr.key.name;
    let sts_name = cr_name + sts_suffix();
    let pod_name = sts_name + pod_suffix();
    let vol_name = sts_name + vol_suffix();

    leads_to_weaken_auto::<CState>(sm_spec());

    lemma_cr_exists_leads_to_pod_exists_and_vol_exists(cr);
    lemma_always_cr_always_exists_implies_delete_pod_vol_req_never_sent(cr);
    leads_to_stable_assume_p_combine::<CState>(sm_spec(),
        next(),
        |s| {
            &&& !message_sent(s, delete_req_msg(ResourceKey{name: pod_name, kind: ResourceKind::PodKind}))
            &&& !message_sent(s, delete_req_msg(ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind}))
        },
        |s| resource_exists(s, cr.key),
        |s| resource_exists(s, ResourceKey{name: pod_name, kind: ResourceKind::PodKind}),
        |s| resource_exists(s, ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind})
    );

    // We can also use the auto version, which takes 1500ms more in smt-run
    implies_preserved_by_always_temp::<CState>(
        lift_state(|s: CState| resource_exists(s, ResourceKey{name: pod_name, kind: ResourceKind::PodKind}))
            .and(lift_state(|s: CState| resource_exists(s, ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind}))),
        lift_state(
            |s: CState| {
                &&& resource_exists(s, ResourceKey{name: pod_name, kind: ResourceKind::PodKind})
                &&& resource_exists(s, ResourceKey{name: vol_name, kind: ResourceKind::VolumeKind})
            }
        )
    );
}

proof fn lemma_cr_exists_leads_to_pod_exists_and_vol_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s| resource_exists(s, cr.key))
                .leads_to(lift_state(|s| resource_exists(s, ResourceKey{name: cr.key.name + sts_suffix() + pod_suffix(), kind: ResourceKind::PodKind})))
        ),
        sm_spec().entails(
            lift_state(|s| resource_exists(s, cr.key))
                .leads_to(lift_state(|s| resource_exists(s, ResourceKey{name: cr.key.name + sts_suffix() + vol_suffix(), kind: ResourceKind::VolumeKind})))
        ),
{
    let cr_name = cr.key.name;
    let sts_name = cr_name + sts_suffix();

    leads_to_trans_auto::<CState>(sm_spec());
    leads_to_weaken_auto::<CState>(sm_spec());

    lemma_always_res_exists_implies_create_req_sent(cr);

    lemma_k8s_create_cr_req_leads_to_create_cr_resp(create_req_msg(cr.key));
    lemma_controller_create_cr_resp_leads_to_create_sts_req(create_resp_msg(cr.key));
    lemma_k8s_create_sts_req_sent_leads_to_pod_exists_and_vol_exists(create_req_msg(ResourceKey{name: sts_name, kind: ResourceKind::StatefulSetKind}));
}

proof fn lemma_always_delete_cr_req_not_sent_implies_delete_pod_and_vol_req_not_sent(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(always(
            lift_state(|s| !message_sent(s, delete_req_msg(cr.key)))
                .implies(lift_state(|s| {
                    &&& !message_sent(s, delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + pod_suffix(), kind: ResourceKind::PodKind}))
                    &&& !message_sent(s, delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + vol_suffix(), kind: ResourceKind::VolumeKind}))
                }))
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

proof fn lemma_always_cr_always_exists_implies_delete_pod_vol_req_never_sent(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            always(
                always(lift_state(|s| resource_exists(s, cr.key)))
                .implies(always(lift_state(|s| {
                    &&& !message_sent(s, delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + pod_suffix(), kind: ResourceKind::PodKind}))
                    &&& !message_sent(s, delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + vol_suffix(), kind: ResourceKind::VolumeKind}))
                })))
            )
        ),
{
    lemma_k8s_delete_cr_req_leads_to_cr_not_exists(delete_req_msg(cr.key));
    leads_to_contradiction::<CState>(sm_spec(),
        |s| message_sent(s, delete_req_msg(cr.key)),
        |s| !resource_exists(s, cr.key),
    );

    lemma_always_delete_cr_req_not_sent_implies_delete_pod_and_vol_req_not_sent(cr);
    always_implies_preserved_by_always::<CState>(sm_spec(),
        |s| !message_sent(s, delete_req_msg(cr.key)),
        |s| {
            &&& !message_sent(s, delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + pod_suffix(), kind: ResourceKind::PodKind}))
            &&& !message_sent(s, delete_req_msg(ResourceKey{name: cr.key.name + sts_suffix() + vol_suffix(), kind: ResourceKind::VolumeKind}))
        }
    );

    implies_preserved_by_always_auto::<CState>();
    always_implies_weaken_auto::<CState>(sm_spec());
}

proof fn lemma_controller_create_cr_resp_leads_to_create_sts_req(msg: Message)
    requires
        msg.is_CreateResponse(),
        msg.get_CreateResponse_0().obj.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| message_sent(s, create_req_msg(
                    ResourceKey {
                        name: msg.get_CreateResponse_0().obj.key.name + sts_suffix(),
                        kind: ResourceKind::StatefulSetKind
                    }
                ))))),
{
    let cr_name = msg.get_CreateResponse_0().obj.key.name;

    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(controller_send_create_sts(m)), msg);

    controller_send_create_sts_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        controller_send_create_sts(msg),
        controller_send_create_sts_pre(msg),
        |s| message_sent(s, create_req_msg(ResourceKey{name: cr_name + sts_suffix(), kind: ResourceKind::StatefulSetKind}))
    );
}

/// All the proofs below are supposed to be part of the Anvil framework,
/// and the user should only reason about the controller related execution.

proof fn lemma_k8s_create_cr_req_leads_to_create_cr_resp(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().obj.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| message_sent(s, create_resp_msg(msg.get_CreateRequest_0().obj.key))))),
{
    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_request(m)), msg);

    k8s_handle_request_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_request(msg),
        k8s_handle_request_pre(msg),
        |s| message_sent(s, create_resp_msg(msg.get_CreateRequest_0().obj.key))
    );
}

proof fn lemma_k8s_delete_cr_req_leads_to_cr_not_exists(msg: Message)
    requires
        msg.is_DeleteRequest(),
        msg.get_DeleteRequest_0().key.kind.is_CustomResourceKind(),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| !resource_exists(s, msg.get_DeleteRequest_0().key)))),
{
    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_request(m)), msg);

    k8s_handle_request_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_request(msg),
        k8s_handle_request_pre(msg),
        |s| !resource_exists(s, msg.get_DeleteRequest_0().key)
    );
}

proof fn lemma_k8s_create_sts_req_sent_leads_to_pod_exists_and_vol_exists(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().obj.key.kind.is_StatefulSetKind(),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| resource_exists(s, ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind})))),
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| resource_exists(s, ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind})))),
{
    lemma_k8s_create_sts_req_sent_leads_to(msg, create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind}));
    lemma_k8s_create_sts_req_sent_leads_to(msg, create_req_msg(ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind}));
}

proof fn lemma_k8s_create_sts_req_sent_leads_to(msg: Message, sub_res_msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().obj.key.kind.is_StatefulSetKind(),
        sub_res_msg.is_CreateRequest(),
        sub_res_msg.get_CreateRequest_0().obj.key === (ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + pod_suffix(), kind: ResourceKind::PodKind})
        || sub_res_msg.get_CreateRequest_0().obj.key === (ResourceKey{name: msg.get_CreateRequest_0().obj.key.name + vol_suffix(), kind: ResourceKind::VolumeKind}),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| resource_exists(s, sub_res_msg.get_CreateRequest_0().obj.key)))),
{
    let sub_res_key = sub_res_msg.get_CreateRequest_0().obj.key;

    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_request(m)), msg);
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_request(m)), sub_res_msg);

    k8s_handle_request_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_request(msg),
        k8s_handle_request_pre(msg),
        |s| message_sent(s, sub_res_msg)
    );

    k8s_handle_request_enabled(sub_res_msg);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_request(sub_res_msg),
        k8s_handle_request_pre(sub_res_msg),
        |s| resource_exists(s, sub_res_key)
    );
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| message_sent(s, sub_res_msg),
        |s| resource_exists(s, sub_res_key)
    );
}

proof fn lemma_k8s_pod_exists_and_vol_exists_leads_to_attached(sts_name: Seq<char>)
    ensures
        sm_spec()
            .entails(lift_state(|s| {
                &&& resource_exists(s, ResourceKey{name: sts_name + pod_suffix(), kind: ResourceKind::PodKind})
                &&& resource_exists(s, ResourceKey{name: sts_name + vol_suffix(), kind: ResourceKind::VolumeKind})
            }).and(always(lift_state(|s| {
                &&& !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + pod_suffix(), kind: ResourceKind::PodKind}))
                &&& !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + vol_suffix(), kind: ResourceKind::VolumeKind}))
            })))
                .leads_to(lift_state(|s: CState| s.attached.contains(sts_name)))),
{
    use_tla_forall::<CState, Seq<char>>(sm_spec(), |name| weak_fairness(k8s_attach_vol_to_pod(name)), sts_name);

    k8s_attach_vol_to_pod_enabled(sts_name);
    wf1_assume::<CState>(sm_spec(),
        next(),
        k8s_attach_vol_to_pod(sts_name),
        |s| {
            &&& !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + pod_suffix(), kind: ResourceKind::PodKind}))
            &&& !message_sent(s, delete_req_msg(ResourceKey{name: sts_name + vol_suffix(), kind: ResourceKind::VolumeKind}))
        },
        |s| {
            &&& resource_exists(s, ResourceKey{name: sts_name + pod_suffix(), kind: ResourceKind::PodKind})
            &&& resource_exists(s, ResourceKey{name: sts_name + vol_suffix(), kind: ResourceKind::VolumeKind})
        },
        |s: CState| s.attached.contains(sts_name)
    );
}

/// This is only useful when we want to prove:
/// strlit_new("a")@ + strlit_new("b")@ === strlit_new("ab")@
proof fn strlit_concat_equality(s1: Seq<char>, s2: Seq<char>, s: Seq<char>)
    requires
        s1.len() + s2.len() === s.len(),
        forall |i:int| 0 <= i < s1.len() ==> s1.index(i) === s.index(i),
        forall |i:int| 0 <= i < s2.len() ==> s2.index(i) === s.index(i + s1.len()),
    ensures
        s1 + s2 === s,
{
    assert(s.ext_equal(s1 + s2));
}

}
