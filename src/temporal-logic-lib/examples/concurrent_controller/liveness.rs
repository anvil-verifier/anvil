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


proof fn lemma_init_leads_to_pod_exists(cr_name: Seq<char>)
    ensures
        sm_spec()
            .entails(lift_state(init())
                .leads_to(lift_state(|s| resource_exists(s, cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)))),
{
    leads_to_eq_auto::<CState>(sm_spec());

    use_tla_forall::<CState, Seq<char>>(sm_spec(), |name| weak_fairness(user_send_create_cr(name)), cr_name);

    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(controller_send_create_sts(msg)), create_cr_resp_msg(cr_name));

    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_cr_req_msg(cr_name));
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_sts_req_msg(cr_name + new_strlit("_sts")@));
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_pod_req_msg(cr_name + new_strlit("_sts")@ + new_strlit("_pod")@));

    user_send_create_cr_enabled(cr_name);
    k8s_handle_create_enabled(create_cr_req_msg(cr_name));
    wf1_chain::<CState>(sm_spec(),
        next(),
        user_send_create_cr(cr_name),
        k8s_handle_create(create_cr_req_msg(cr_name)),
        user_send_create_cr_pre(),
        k8s_handle_create_pre(create_cr_req_msg(cr_name)),
        |s| message_sent(s, create_cr_resp_msg(cr_name))
    );

    leads_to_weaken_left::<CState>(sm_spec(),
        user_send_create_cr_pre(),
        init(),
        |s| message_sent(s, create_cr_resp_msg(cr_name))
    );

    reveal_strlit("app");
    reveal_strlit("_sts");
    reveal_strlit("app_sts");
    strlit_concat_equality(cr_name, new_strlit("_sts")@, cr_name + new_strlit("_sts")@);

    controller_send_create_sts_enabled(create_cr_resp_msg(cr_name));
    wf1::<CState>(sm_spec(),
        next(),
        controller_send_create_sts(create_cr_resp_msg(cr_name)),
        controller_send_create_sts_pre(create_cr_resp_msg(cr_name)),
        |s| message_sent(s, create_sts_req_msg(cr_name + new_strlit("_sts")@))
    );

    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| message_sent(s, create_cr_resp_msg(cr_name)),
        |s| message_sent(s, create_sts_req_msg(cr_name + new_strlit("_sts")@))
    );

    k8s_handle_create_enabled(create_sts_req_msg(cr_name + new_strlit("_sts")@));
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_sts_req_msg(cr_name + new_strlit("_sts")@)),
        k8s_handle_create_pre(create_sts_req_msg(cr_name + new_strlit("_sts")@)),
        |s| message_sent(s, create_pod_req_msg(cr_name + new_strlit("_sts")@ + new_strlit("_pod")@))
    );

    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| message_sent(s, create_sts_req_msg(cr_name + new_strlit("_sts")@)),
        |s| message_sent(s, create_pod_req_msg(cr_name + new_strlit("_sts")@ + new_strlit("_pod")@))
    );

    k8s_handle_create_enabled(create_pod_req_msg(cr_name + new_strlit("_sts")@ + new_strlit("_pod")@));
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_pod_req_msg(cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)),
        k8s_handle_create_pre(create_pod_req_msg(cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)),
        |s| resource_exists(s, cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)
    );
    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| message_sent(s, create_pod_req_msg(cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)),
        |s| resource_exists(s, cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)
    );
}

proof fn lemma_init_leads_to_vol_exists(cr_name: Seq<char>)
    ensures
        sm_spec()
            .entails(lift_state(init())
                .leads_to(lift_state(|s| resource_exists(s, cr_name + new_strlit("_vol")@)))),
{
    leads_to_eq_auto::<CState>(sm_spec());

    use_tla_forall::<CState, Seq<char>>(sm_spec(), |name| weak_fairness(user_send_create_cr(name)), cr_name);

    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(controller_send_create_vol(msg)), create_cr_resp_msg(cr_name));

    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_cr_req_msg(cr_name));
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_vol_req_msg(cr_name + new_strlit("_vol")@));

    user_send_create_cr_enabled(cr_name);
    k8s_handle_create_enabled(create_cr_req_msg(cr_name));
    wf1_chain::<CState>(sm_spec(),
        next(),
        user_send_create_cr(cr_name),
        k8s_handle_create(create_cr_req_msg(cr_name)),
        user_send_create_cr_pre(),
        k8s_handle_create_pre(create_cr_req_msg(cr_name)),
        |s| message_sent(s, create_cr_resp_msg(cr_name))
    );

    leads_to_weaken_left::<CState>(sm_spec(),
        user_send_create_cr_pre(),
        init(),
        |s| message_sent(s, create_cr_resp_msg(cr_name))
    );

    controller_send_create_vol_enabled(create_cr_resp_msg(cr_name));
    wf1::<CState>(sm_spec(),
        next(),
        controller_send_create_vol(create_cr_resp_msg(cr_name)),
        controller_send_create_vol_pre(create_cr_resp_msg(cr_name)),
        |s| message_sent(s, create_vol_req_msg(cr_name + new_strlit("_vol")@))
    );

    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| message_sent(s, create_cr_resp_msg(cr_name)),
        |s| message_sent(s, create_vol_req_msg(cr_name + new_strlit("_vol")@)),
    );

    k8s_handle_create_enabled(create_vol_req_msg(cr_name + new_strlit("_vol")@));
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_vol_req_msg(cr_name + new_strlit("_vol")@)),
        k8s_handle_create_pre(create_vol_req_msg(cr_name + new_strlit("_vol")@)),
        |s| resource_exists(s, cr_name + new_strlit("_vol")@)
    );

    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| message_sent(s, create_vol_req_msg(cr_name + new_strlit("_vol")@)),
        |s| resource_exists(s, cr_name + new_strlit("_vol")@)
    );
}

proof fn lemma_eventually_attached(cr_name: Seq<char>)
    ensures
        sm_spec().entails(eventually(lift_state(|s: CState| s.attached.contains(cr_name)))),
{
    leads_to_eq_auto::<CState>(sm_spec());

    use_tla_forall::<CState, Seq<char>>(sm_spec(), |name| weak_fairness(k8s_attach_vol_to_pod(name)), cr_name);

    lemma_init_leads_to_pod_exists(cr_name);
    leads_to_stable::<CState>(sm_spec(),
        next(),
        init(),
        |s| resource_exists(s, cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)
    );

    lemma_init_leads_to_vol_exists(cr_name);
    leads_to_stable::<CState>(sm_spec(),
        next(),
        init(),
        |s| resource_exists(s, cr_name + new_strlit("_vol")@)
    );

    leads_to_always_combine_then_weaken::<CState>(sm_spec(),
        init(),
        |s| resource_exists(s, cr_name + new_strlit("_sts")@ + new_strlit("_pod")@),
        |s| resource_exists(s, cr_name + new_strlit("_vol")@)
    );

    k8s_attach_vol_to_pod_enabled(cr_name);
    wf1::<CState>(sm_spec(),
        next(),
        k8s_attach_vol_to_pod(cr_name),
        |s| {
            &&& resource_exists(s, cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)
            &&& resource_exists(s, cr_name + new_strlit("_vol")@)
        },
        |s: CState| s.attached.contains(cr_name)
    );

    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| {
            &&& resource_exists(s, cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)
            &&& resource_exists(s, cr_name + new_strlit("_vol")@)
        },
        |s: CState| s.attached.contains(cr_name)
    );

    leads_to_apply::<CState>(sm_spec(),
        init(),
        |s: CState| s.attached.contains(cr_name)
    );
}

// Is it better to give a more descriptive name rather than liveness_property?
// Similar for the two following proof fn
spec fn liveness_property(cr_name: Seq<char>) -> TempPred<CState> {
    eventually(lift_state(
        |s: CState| {
            &&& resource_exists(s, cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)
            &&& resource_exists(s, cr_name + new_strlit("_vol")@)
            &&& s.attached.contains(cr_name)
        }
    ))
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
            &&& s.attached.contains(cr_name) ==> resource_exists(s, cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)
            &&& s.attached.contains(cr_name) ==> resource_exists(s, cr_name + new_strlit("_vol")@)
        },
        |s: CState| s.attached.contains(cr_name)
    );

    eventually_weaken::<CState>(sm_spec(),
        |s: CState| {
            &&& s.attached.contains(cr_name) ==> resource_exists(s, cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)
            &&& s.attached.contains(cr_name) ==> resource_exists(s, cr_name + new_strlit("_vol")@)
            &&& s.attached.contains(cr_name)
        },
        |s: CState| {
            &&& resource_exists(s, cr_name + new_strlit("_sts")@ + new_strlit("_pod")@)
            &&& resource_exists(s, cr_name + new_strlit("_vol")@)
            &&& s.attached.contains(cr_name)
        }
    );
}

proof fn liveness_proof_for_all_cr()
    ensures
        forall |cr_name| sm_spec().entails(#[trigger] liveness_property(cr_name)),
{
    assert forall |cr_name: Seq<char>| sm_spec().entails(#[trigger] liveness_property(cr_name)) by {
        liveness_proof(cr_name);
    };
}

}
