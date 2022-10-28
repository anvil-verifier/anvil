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
    let sts_name = cr_name + sts_suffix();
    let pod_name = sts_name + pod_suffix();
    let vol_name = sts_name + vol_suffix();

    lift_state(
        |s| message_sent(s, msg)
    )
    .leads_to(
        always(lift_state(
            |s: CState| {
                &&& resource_exists(s, pod_name)
                &&& resource_exists(s, vol_name)
                &&& s.attached.contains(sts_name)
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
    let sts_name = cr_name + sts_suffix();
    let pod_name = sts_name + pod_suffix();
    let vol_name = sts_name + vol_suffix();

    lemma_leads_to_always_attached(msg);

    lemma_always_attach_after_create(sts_name);
    always_to_leads_to_always::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s: CState| {
            &&& s.attached.contains(sts_name) ==> resource_exists(s, pod_name)
            &&& s.attached.contains(sts_name) ==> resource_exists(s, vol_name)
        },
    );

    leads_to_always_combine::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s: CState| s.attached.contains(sts_name),
        |s: CState| {
            &&& s.attached.contains(sts_name) ==> resource_exists(s, pod_name)
            &&& s.attached.contains(sts_name) ==> resource_exists(s, vol_name)
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
                .leads_to(always(lift_state(|s: CState| s.attached.contains(msg.get_CreateRequest_0().name + sts_suffix()))))
        ),
{
    let cr_name = msg.get_CreateRequest_0().name;
    let sts_name = cr_name + sts_suffix();
    let pod_name = sts_name + pod_suffix();
    let vol_name = sts_name + vol_suffix();

    leads_to_eq_auto::<CState>(sm_spec());

    lemma_k8s_create_cr_req_leads_to_create_cr_resp(msg);
    lemma_controller_create_cr_resp_leads_to_create_sts_req(create_cr_resp_msg(cr_name));
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_cr_resp_msg(cr_name)),
        |s| message_sent(s, create_sts_req_msg(sts_name))
    );

   lemma_k8s_create_sts_req_sent_leads_to_pod_exists(create_sts_req_msg(sts_name));
   leads_to_trans::<CState>(sm_spec(),
       |s| message_sent(s, msg),
       |s| message_sent(s, create_sts_req_msg(sts_name)),
       |s| resource_exists(s, pod_name)
    );

    lemma_k8s_create_sts_req_sent_leads_to_vol_exists(create_sts_req_msg(sts_name));
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_sts_req_msg(sts_name)),
        |s| resource_exists(s, vol_name)
     );

    leads_to_stable::<CState>(sm_spec(),
        next(),
        |s| message_sent(s, msg),
        |s| resource_exists(s, pod_name)
    );
    leads_to_stable::<CState>(sm_spec(),
        next(),
        |s| message_sent(s, msg),
        |s| resource_exists(s, vol_name)
    );
    leads_to_always_combine_then_drop_always::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| resource_exists(s, pod_name),
        |s| resource_exists(s, vol_name)
    );

    lemma_k8s_pod_exists_and_vol_exists_leads_to_attached(sts_name);
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| {
            &&& resource_exists(s, pod_name)
            &&& resource_exists(s, vol_name)
        },
        |s: CState| s.attached.contains(sts_name)
    );

    leads_to_stable::<CState>(sm_spec(),
        next(),
        |s| message_sent(s, msg),
        |s: CState| s.attached.contains(sts_name)
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

/// All the proofs below are supposed to be part of the Anvil framework,
/// and the user should only reason about the controller related execution.

/// TODO: this lemma should also take a Message, or two, since the action is waiting for two messages
/// This is not realistic because actual controllers won't wait for two messages at the same time
/// A controller typically sends out a message, receives the response, and sends out another message...
proof fn lemma_k8s_pod_exists_and_vol_exists_leads_to_attached(sts_name: Seq<char>)
    ensures
        sm_spec()
            .entails(lift_state(|s| {
                &&& resource_exists(s, sts_name + pod_suffix())
                &&& resource_exists(s, sts_name + vol_suffix())
            })
                .leads_to(lift_state(|s: CState| s.attached.contains(sts_name)))),
{
    let pod_name = sts_name + pod_suffix();
    let vol_name = sts_name + vol_suffix();

    use_tla_forall::<CState, Seq<char>>(sm_spec(), |name| weak_fairness(k8s_attach_vol_to_pod(name)), sts_name);

    k8s_attach_vol_to_pod_enabled(sts_name);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_attach_vol_to_pod(sts_name),
        |s| {
            &&& resource_exists(s, pod_name)
            &&& resource_exists(s, vol_name)
        },
        |s: CState| s.attached.contains(sts_name)
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
    let pod_name = sts_name + pod_suffix();

    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_create(m)), msg);
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_create(m)), create_pod_req_msg(pod_name));

    k8s_handle_create_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(msg),
        k8s_handle_create_pre(msg),
        |s| message_sent(s, create_pod_req_msg(pod_name))
    );

    k8s_handle_create_enabled(create_pod_req_msg(pod_name));
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_pod_req_msg(pod_name)),
        k8s_handle_create_pre(create_pod_req_msg(pod_name)),
        |s| resource_exists(s, pod_name)
    );
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_pod_req_msg(pod_name)),
        |s| resource_exists(s, pod_name)
    );
}

proof fn lemma_k8s_create_sts_req_sent_leads_to_vol_exists(msg: Message)
    requires
        msg.is_CreateRequest(),
        msg.get_CreateRequest_0().kind.is_StatefulSetKind(),
    ensures
        sm_spec()
            .entails(lift_state(|s| message_sent(s, msg))
                .leads_to(lift_state(|s| resource_exists(s, msg.get_CreateRequest_0().name + vol_suffix())))),
{
    let sts_name = msg.get_CreateRequest_0().name;
    let vol_name = sts_name + vol_suffix();

    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_create(m)), msg);
    use_tla_forall::<CState, Message>(sm_spec(), |m| weak_fairness(k8s_handle_create(m)), create_vol_req_msg(vol_name));

    k8s_handle_create_enabled(msg);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(msg),
        k8s_handle_create_pre(msg),
        |s| message_sent(s, create_vol_req_msg(vol_name))
    );

    k8s_handle_create_enabled(create_vol_req_msg(vol_name));
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_vol_req_msg(vol_name)),
        k8s_handle_create_pre(create_vol_req_msg(vol_name)),
        |s| resource_exists(s, vol_name)
    );
    leads_to_trans::<CState>(sm_spec(),
        |s| message_sent(s, msg),
        |s| message_sent(s, create_vol_req_msg(vol_name)),
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
