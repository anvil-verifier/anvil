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

spec fn liveness_property(cr_name: Seq<char>) -> TempPred<CState> {
    eventually(lift_state(
        |s: CState| {
            &&& resource_exists(s, cr_name + sts_suffix() + pod_suffix())
            &&& resource_exists(s, cr_name + vol_suffix())
            &&& s.attached.contains(cr_name)
        }
    ))
}

proof fn liveness_proof_for_all_cr()
    ensures
        forall |cr_name| sm_spec().entails(#[trigger] liveness_property(cr_name)),
{
    assert forall |cr_name: Seq<char>| sm_spec().entails(#[trigger] liveness_property(cr_name)) by {
        liveness_proof(cr_name);
    };
}

proof fn liveness_proof(cr_name: Seq<char>)
    ensures
        sm_spec().entails(liveness_property(cr_name)),
{
    eventually_eq_auto::<CState>(sm_spec());

    lemma_eventually_attached(cr_name);
    lemma_always_attach_after_create(cr_name);
    always_and_eventually::<CState>(sm_spec(),
        |s: CState| {
            &&& s.attached.contains(cr_name) ==> resource_exists(s, cr_name + sts_suffix() + pod_suffix())
            &&& s.attached.contains(cr_name) ==> resource_exists(s, cr_name + vol_suffix())
        },
        |s: CState| s.attached.contains(cr_name)
    );

    eventually_weaken::<CState>(sm_spec(),
        |s: CState| {
            &&& s.attached.contains(cr_name) ==> resource_exists(s, cr_name + sts_suffix() + pod_suffix())
            &&& s.attached.contains(cr_name) ==> resource_exists(s, cr_name + vol_suffix())
            &&& s.attached.contains(cr_name)
        },
        |s: CState| {
            &&& resource_exists(s, cr_name + sts_suffix() + pod_suffix())
            &&& resource_exists(s, cr_name + vol_suffix())
            &&& s.attached.contains(cr_name)
        }
    );
}

proof fn lemma_eventually_attached(cr_name: Seq<char>)
    ensures
        sm_spec()
            .entails(eventually(lift_state(|s: CState| s.attached.contains(cr_name)))),
{
    leads_to_eq_auto::<CState>(sm_spec());

    lemma_user_init_leads_to_create_cr_req(cr_name);
    lemma_k8s_create_cr_req_leads_to_create_cr_resp(create_cr_req_msg(cr_name));
    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| message_sent(s, create_cr_req_msg(cr_name)),
        |s| message_sent(s, create_cr_resp_msg(cr_name))
    );

    lemma_controller_create_cr_resp_leads_to_create_sts_req(cr_name);
    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| message_sent(s, create_cr_resp_msg(cr_name)),
        |s| message_sent(s, create_sts_req_msg(cr_name + sts_suffix()))
    );

   lemma_k8s_create_sts_req_sent_leads_to_pod_exists(create_sts_req_msg(cr_name + sts_suffix()));
   leads_to_trans::<CState>(sm_spec(),
       init(),
       |s| message_sent(s, create_sts_req_msg(cr_name + sts_suffix())),
       |s| resource_exists(s, cr_name + sts_suffix() + pod_suffix())
    );

    lemma_controller_create_cr_resp_leads_to_create_vol_req(cr_name);
    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| message_sent(s, create_cr_resp_msg(cr_name)),
        |s| message_sent(s, create_vol_req_msg(cr_name + vol_suffix()))
    );

    lemma_k8s_create_vol_req_sent_leads_to_vol_exists(create_vol_req_msg(cr_name + vol_suffix()));
    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| message_sent(s, create_vol_req_msg(cr_name + vol_suffix())),
        |s| resource_exists(s, cr_name + vol_suffix())
    );

    leads_to_stable::<CState>(sm_spec(),
        next(),
        init(),
        |s| resource_exists(s, cr_name + sts_suffix() + pod_suffix())
    );
    leads_to_stable::<CState>(sm_spec(),
        next(),
        init(),
        |s| resource_exists(s, cr_name + vol_suffix())
    );
    leads_to_always_combine_then_weaken::<CState>(sm_spec(),
        init(),
        |s| resource_exists(s, cr_name + sts_suffix() + pod_suffix()),
        |s| resource_exists(s, cr_name + vol_suffix())
    );

    lemma_controller_pod_exists_and_vol_exists_leads_to_attached(cr_name);
    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| {
            &&& resource_exists(s, cr_name + sts_suffix() + pod_suffix())
            &&& resource_exists(s, cr_name + vol_suffix())
        },
        |s: CState| s.attached.contains(cr_name)
    );

    leads_to_apply::<CState>(sm_spec(),
        init(),
        |s: CState| s.attached.contains(cr_name)
    );
}

proof fn lemma_controller_create_cr_resp_leads_to_create_sts_req(cr_name: Seq<char>)
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, create_cr_resp_msg(cr_name)))
                .leads_to(lift_state(|s| message_sent(s, create_sts_req_msg(cr_name + sts_suffix()))))),
{
    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(controller_send_create_sts(msg)), create_cr_resp_msg(cr_name));

    controller_send_create_sts_enabled(create_cr_resp_msg(cr_name));
    wf1::<CState>(sm_spec(),
        next(),
        controller_send_create_sts(create_cr_resp_msg(cr_name)),
        controller_send_create_sts_pre(create_cr_resp_msg(cr_name)),
        |s| message_sent(s, create_sts_req_msg(cr_name + sts_suffix()))
    );
}

proof fn lemma_controller_create_cr_resp_leads_to_create_vol_req(cr_name: Seq<char>)
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, create_cr_resp_msg(cr_name)))
                .leads_to(lift_state(|s| message_sent(s, create_vol_req_msg(cr_name + vol_suffix()))))),
{
    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(controller_send_create_vol(msg)), create_cr_resp_msg(cr_name));

    controller_send_create_vol_enabled(create_cr_resp_msg(cr_name));
    wf1::<CState>(sm_spec(),
        next(),
        controller_send_create_vol(create_cr_resp_msg(cr_name)),
        controller_send_create_vol_pre(create_cr_resp_msg(cr_name)),
        |s| message_sent(s, create_vol_req_msg(cr_name + vol_suffix()))
    );
}

proof fn lemma_controller_pod_exists_and_vol_exists_leads_to_attached(cr_name: Seq<char>)
    ensures
        sm_spec()
            .entails(lift_state(|s| {
                &&& resource_exists(s, cr_name + sts_suffix() + pod_suffix())
                &&& resource_exists(s, cr_name + vol_suffix())
            })
                .leads_to(lift_state(|s: CState| s.attached.contains(cr_name)))),
{
    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Seq<char>>(sm_spec(), |name| weak_fairness(controller_attach_vol_to_pod(name)), cr_name);

    controller_attach_vol_to_pod_enabled(cr_name);
    wf1::<CState>(sm_spec(),
        next(),
        controller_attach_vol_to_pod(cr_name),
        |s| {
            &&& resource_exists(s, cr_name + sts_suffix() + pod_suffix())
            &&& resource_exists(s, cr_name + vol_suffix())
        },
        |s: CState| s.attached.contains(cr_name)
    );
}


/// All the proofs below are supposed to be part of the Anvil framework,
/// and the user should only reason about the controller related execution.

proof fn lemma_user_init_leads_to_create_cr_req(cr_name: Seq<char>)
    ensures
        sm_spec()
            .entails(lift_state(init())
                .leads_to(lift_state(|s| message_sent(s, create_cr_req_msg(cr_name))))),
{
    use_tla_forall::<CState, Seq<char>>(sm_spec(), |name| weak_fairness(user_send_create_cr(name)), cr_name);

    user_send_create_cr_enabled(cr_name);
    wf1::<CState>(sm_spec(),
        next(),
        user_send_create_cr(cr_name),
        user_send_create_cr_pre(),
        |s| message_sent(s, create_cr_req_msg(cr_name))
    );

    leads_to_weaken_left::<CState>(sm_spec(),
        user_send_create_cr_pre(),
        init(),
        |s| message_sent(s, create_cr_req_msg(cr_name))
    );
}

proof fn lemma_k8s_create_cr_req_leads_to_create_cr_resp(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().kind.is_CustomResourceKind(),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| message_sent(s, create_cr_resp_msg(msg.get_CreateRequest_0().name))))),
{
    let cr_name = msg.get_CreateRequest_0().name;

    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_create(m)), msg);

    k8s_handle_create_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(msg),
        k8s_handle_create_pre(msg),
        |s| message_sent(s, create_cr_resp_msg(cr_name))
    );
}

proof fn lemma_k8s_create_sts_req_sent_leads_to_pod_exists(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().kind.is_StatefulSetKind(),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| resource_exists(s, msg.get_CreateRequest_0().name + pod_suffix())))),
{
    let sts_name = msg.get_CreateRequest_0().name;

    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_create(m)), msg);
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_create(m)), create_pod_req_msg(sts_name + pod_suffix()));

    k8s_handle_create_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(msg),
        k8s_handle_create_pre(msg),
        |s| message_sent(s, create_pod_req_msg(sts_name + pod_suffix()))
    );

    k8s_handle_create_enabled(create_pod_req_msg(sts_name + pod_suffix()));
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_pod_req_msg(sts_name + pod_suffix())),
        k8s_handle_create_pre(create_pod_req_msg(sts_name + pod_suffix())),
        |s| resource_exists(s, sts_name + pod_suffix())
    );
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_pod_req_msg(sts_name + pod_suffix())),
        |s| resource_exists(s, sts_name + pod_suffix())
    );
}

proof fn lemma_k8s_create_vol_req_sent_leads_to_vol_exists(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().kind.is_VolumeKind(),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| resource_exists(s, msg.get_CreateRequest_0().name)))),
{
    let vol_name = msg.get_CreateRequest_0().name;

    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_create(m)), msg);

    k8s_handle_create_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(msg),
        k8s_handle_create_pre(msg),
        |s| resource_exists(s, vol_name)
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
