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

spec fn liveness_property(msg: Message) -> TempPred<CState>
    recommends
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().kind.is_CustomResourceKind(),
{
    let cr_name = msg.get_CreateRequest_0().name;
    lift_state(
        |s| message_sent(s, msg)
    )
    .leads_to(
        always(lift_state(
            |s: CState| {
                &&& message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix()))
                &&& message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
                &&& s.attached.contains(cr_name)
            }
        ))
    )
}

proof fn liveness_proof_for_all_cr()
    ensures
        forall |msg: Message| msg.is_CreateRequest() && msg.get_CreateRequest_0().kind.is_CustomResourceKind()
          ==> sm_spec().entails(#[trigger] liveness_property(msg)),
{
    assert forall |msg: Message| msg.is_CreateRequest() && msg.get_CreateRequest_0().kind.is_CustomResourceKind()
    implies sm_spec().entails(#[trigger] liveness_property(msg)) by {
        liveness_proof(msg);
    };
}

proof fn liveness_proof(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(liveness_property(msg)),
{
    let cr_name = msg.get_CreateRequest_0().name;

    lemma_leads_to_always_attached(msg);

    lemma_always_attach_after_create(cr_name);
    always_to_leads_to_always::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s: CState| {
            &&& s.attached.contains(cr_name) ==> message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix()))
            &&& s.attached.contains(cr_name) ==> message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
        },
    );

    leads_to_always_combine::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s: CState| s.attached.contains(cr_name),
        |s: CState| {
            &&& s.attached.contains(cr_name) ==> message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix()))
            &&& s.attached.contains(cr_name) ==> message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
        },
    );

    leads_to_always_weaken_auto::<CState>(sm_spec());
}

proof fn lemma_leads_to_always_attached(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s| message_sent(s, msg))
                .leads_to(always(lift_state(|s: CState| s.attached.contains(msg.get_CreateRequest_0().name))))
        ),
{
    let cr_name = msg.get_CreateRequest_0().name;

    leads_to_eq_auto::<CState>(sm_spec());

    lemma_k8s_create_cr_req_leads_to_create_cr_resp(msg);
    lemma_controller_create_cr_resp_leads_to_create_sts_req(create_cr_resp_msg(cr_name));
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_cr_resp_msg(cr_name)),
        |s| message_sent(s, create_sts_req_msg(cr_name + sts_suffix()))
    );

   lemma_k8s_create_sts_req_sent_leads_to_pod_exists(create_sts_req_msg(cr_name + sts_suffix()));
   leads_to_trans::<CState>(sm_spec(),
       |s| message_sent(s, msg),
       |s| message_sent(s, create_sts_req_msg(cr_name + sts_suffix())),
       |s| message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix()))
    );

    lemma_controller_create_cr_resp_leads_to_create_vol_req(create_cr_resp_msg(cr_name));
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_cr_resp_msg(cr_name)),
        |s| message_sent(s, create_vol_req_msg(cr_name + vol_suffix()))
    );

    lemma_k8s_create_vol_req_sent_leads_to_vol_exists(create_vol_req_msg(cr_name + vol_suffix()));
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_vol_req_msg(cr_name + vol_suffix())),
        |s| message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
    );

    leads_to_stable::<CState>(sm_spec(),
        next(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix()))
    );
    leads_to_stable::<CState>(sm_spec(),
        next(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
    );
    leads_to_always_combine_then_drop_always::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix())),
        |s| message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
    );

    lemma_controller_pod_exists_and_vol_exists_leads_to_attached(cr_name);
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| {
            &&& message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix()))
            &&& message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
        },
        |s: CState| s.attached.contains(cr_name)
    );

    leads_to_stable::<CState>(sm_spec(),
        next(),
        |s| message_sent(s, msg),
        |s: CState| s.attached.contains(cr_name)
    );
}

proof fn lemma_controller_create_cr_resp_leads_to_create_sts_req(msg: Message)
    requires
        msg.is_CreateResponse(),
        msg.get_CreateResponse_0().kind.is_CustomResourceKind(),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| message_sent(s, create_sts_req_msg(msg.get_CreateResponse_0().name + sts_suffix()))))),
{
    let cr_name = msg.get_CreateResponse_0().name;

    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(controller_send_create_sts(m)), msg);

    controller_send_create_sts_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        controller_send_create_sts(msg),
        controller_send_create_sts_pre(msg),
        |s| message_sent(s, create_sts_req_msg(cr_name + sts_suffix()))
    );
}

proof fn lemma_controller_create_cr_resp_leads_to_create_vol_req(msg: Message)
    requires
        msg.is_CreateResponse(),
        msg.get_CreateResponse_0().kind.is_CustomResourceKind(),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| message_sent(s, create_vol_req_msg(msg.get_CreateResponse_0().name + vol_suffix()))))),
{
    let cr_name = msg.get_CreateResponse_0().name;

    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(controller_send_create_vol(m)), msg);

    controller_send_create_vol_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        controller_send_create_vol(msg),
        controller_send_create_vol_pre(msg),
        |s| message_sent(s, create_vol_req_msg(cr_name + vol_suffix()))
    );
}

/// TODO: this lemma should also take a Message, or two, since the action is waiting for two messages
/// This is not realistic because actual controllers won't wait for two messages at the same time
/// A controller typically sends out a message, receives the response, and sends out another message...
proof fn lemma_controller_pod_exists_and_vol_exists_leads_to_attached(cr_name: Seq<char>)
    ensures
        sm_spec()
            .entails(lift_state(|s| {
                &&& message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix()))
                &&& message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
            })
                .leads_to(lift_state(|s: CState| s.attached.contains(cr_name)))),
{
    use_tla_forall::<CState, Seq<char>>(sm_spec(), |name| weak_fairness(controller_attach_vol_to_pod(name)), cr_name);

    controller_attach_vol_to_pod_enabled(cr_name);
    wf1::<CState>(sm_spec(),
        next(),
        controller_attach_vol_to_pod(cr_name),
        |s| {
            &&& message_sent(s, create_pod_resp_msg(cr_name + sts_suffix() + pod_suffix()))
            &&& message_sent(s, create_vol_resp_msg(cr_name + vol_suffix()))
        },
        |s: CState| s.attached.contains(cr_name)
    );
}


/// All the proofs below are supposed to be part of the Anvil framework,
/// and the user should only reason about the controller related execution.

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
                .leads_to(lift_state(|s| message_sent(s, create_pod_resp_msg(msg.get_CreateRequest_0().name + pod_suffix()))))),
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
        |s| message_sent(s, create_pod_resp_msg(sts_name + pod_suffix()))
    );
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_pod_req_msg(sts_name + pod_suffix())),
        |s| message_sent(s, create_pod_resp_msg(sts_name + pod_suffix()))
    );
}

proof fn lemma_k8s_create_vol_req_sent_leads_to_vol_exists(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().kind.is_VolumeKind(),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| message_sent(s, create_vol_resp_msg(msg.get_CreateRequest_0().name))))),
{
    let vol_name = msg.get_CreateRequest_0().name;

    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_create(m)), msg);

    k8s_handle_create_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(msg),
        k8s_handle_create_pre(msg),
        |s| message_sent(s, create_vol_resp_msg(vol_name))
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
