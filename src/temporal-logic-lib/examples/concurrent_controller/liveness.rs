// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::concurrent_controller::safety::*;
use crate::examples::concurrent_controller::state_machine::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn create_cr_msg() -> Message {
    Message::CreateCR
}

pub open spec fn create_sts_msg() -> Message {
    Message::CreateStatefulSet{replica: 1}
}

pub open spec fn create_vol_msg() -> Message {
    Message::CreateVolume{id: 1}
}

proof fn lemma_init_leads_to_pod1_exists()
    ensures
        sm_spec()
            .entails(lift_state(init())
                .leads_to(lift_state(|s| resource_exists(s, new_strlit("my_pod1")@)))),
{
    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_cr_msg());
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_sts_msg());

    send_create_cr_enabled();
    k8s_handle_create_enabled(create_cr_msg());
    wf1_chain::<CState>(sm_spec(),
        next(),
        send_create_cr(),
        k8s_handle_create(create_cr_msg()),
        init(),
        k8s_handle_create_pre(create_cr_msg()),
        |s| resource_exists(s, new_strlit("my_cr")@),
    );

    send_create_sts_enabled();
    wf1::<CState>(sm_spec(),
        next(),
        send_create_sts(),
        |s| {
            &&& resource_exists(s, new_strlit("my_cr")@)
            &&& !message_sent(s, Message::CreateStatefulSet{replica: 1})
        },
        |s| message_sent(s, Message::CreateStatefulSet{replica: 1})
    );
    leads_to_assume_not::<CState>(sm_spec(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| message_sent(s, Message::CreateStatefulSet{replica: 1})
    );

    k8s_handle_create_enabled(create_sts_msg());
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_sts_msg()),
        k8s_handle_create_pre(create_sts_msg()),
        |s| resource_exists(s, new_strlit("my_statefulset")@)
    );

    leads_to_trans::<CState>(sm_spec(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| message_sent(s, Message::CreateStatefulSet{replica: 1}),
        |s| resource_exists(s, new_strlit("my_statefulset")@)
    );

    k8s_create_pod_enabled();
    wf1::<CState>(sm_spec(),
        next(),
        k8s_create_pod(),
        |s| resource_exists(s, new_strlit("my_statefulset")@),
        |s| resource_exists(s, new_strlit("my_pod1")@)
    );
    leads_to_trans::<CState>(sm_spec(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| resource_exists(s, new_strlit("my_statefulset")@),
        |s| resource_exists(s, new_strlit("my_pod1")@)
    );

    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| resource_exists(s, new_strlit("my_pod1")@)
    );
}

proof fn lemma_init_leads_to_vol1_exists()
    ensures
        sm_spec()
            .entails(lift_state(init())
                .leads_to(lift_state(|s| resource_exists(s, new_strlit("my_volume1")@)))),
{
    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_cr_msg());
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_vol_msg());

    send_create_cr_enabled();
    k8s_handle_create_enabled(create_cr_msg());
    wf1_chain::<CState>(sm_spec(),
        next(),
        send_create_cr(),
        k8s_handle_create(create_cr_msg()),
        init(),
        k8s_handle_create_pre(create_cr_msg()),
        |s| resource_exists(s, new_strlit("my_cr")@),
    );

    send_create_vol_enabled();
    wf1::<CState>(sm_spec(),
        next(),
        send_create_vol(),
        |s| {
            &&& resource_exists(s, new_strlit("my_cr")@)
            &&& !message_sent(s, Message::CreateVolume{id: 1})
        },
        |s| message_sent(s, Message::CreateVolume{id: 1})
    );
    leads_to_assume_not::<CState>(sm_spec(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| message_sent(s, Message::CreateVolume{id: 1})
    );

    k8s_handle_create_enabled(create_vol_msg());
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_vol_msg()),
        k8s_handle_create_pre(create_vol_msg()),
        |s| resource_exists(s, new_strlit("my_volume1")@)
    );

    leads_to_trans::<CState>(sm_spec(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| message_sent(s, Message::CreateVolume{id: 1}),
        |s| resource_exists(s, new_strlit("my_volume1")@)
    );

    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| resource_exists(s, new_strlit("my_volume1")@)
    );
}

proof fn lemma_eventually_vol_attached()
    ensures
        sm_spec().entails(eventually(lift_state(|s: CState| s.vol_attached))),
{
    leads_to_eq_auto::<CState>(sm_spec());

    lemma_init_leads_to_pod1_exists();
    leads_to_stable::<CState>(sm_spec(),
        next(),
        init(),
        |s| resource_exists(s, new_strlit("my_pod1")@)
    );

    lemma_init_leads_to_vol1_exists();
    leads_to_stable::<CState>(sm_spec(),
        next(),
        init(),
        |s| resource_exists(s, new_strlit("my_volume1")@)
    );

    leads_to_always_combine_then_weaken::<CState>(sm_spec(),
        init(),
        |s| resource_exists(s, new_strlit("my_pod1")@),
        |s| resource_exists(s, new_strlit("my_volume1")@)
    );

    k8s_attach_vol_to_pod_enabled();
    wf1::<CState>(sm_spec(),
        next(),
        k8s_attach_vol_to_pod(),
        |s| {
            &&& resource_exists(s, new_strlit("my_pod1")@)
            &&& resource_exists(s, new_strlit("my_volume1")@)
        },
        |s: CState| s.vol_attached
    );

    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| {
            &&& resource_exists(s, new_strlit("my_pod1")@)
            &&& resource_exists(s, new_strlit("my_volume1")@)
        },
        |s: CState| s.vol_attached
    );

    leads_to_apply::<CState>(sm_spec(),
        init(),
        |s: CState| s.vol_attached
    );
}

proof fn liveness()
    ensures
        sm_spec().entails(
            eventually(lift_state(
                |s: CState| {
                    &&& resource_exists(s, new_strlit("my_pod1")@)
                    &&& resource_exists(s, new_strlit("my_volume1")@)
                    &&& s.vol_attached
                }
            ))),
{
    eventually_eq_auto::<CState>(sm_spec());

    lemma_eventually_vol_attached();
    lemma_always_attach_after_create();
    always_and_eventually::<CState>(sm_spec(),
        |s: CState| {
            &&& s.vol_attached ==> resource_exists(s, new_strlit("my_pod1")@)
            &&& s.vol_attached ==> resource_exists(s, new_strlit("my_volume1")@)
        },
        |s: CState| s.vol_attached
    );

    eventually_weaken::<CState>(sm_spec(),
        |s: CState| {
            &&& s.vol_attached ==> resource_exists(s, new_strlit("my_pod1")@)
            &&& s.vol_attached ==> resource_exists(s, new_strlit("my_volume1")@)
            &&& s.vol_attached
        },
        |s: CState| {
            &&& resource_exists(s, new_strlit("my_pod1")@)
            &&& resource_exists(s, new_strlit("my_volume1")@)
            &&& s.vol_attached
        }
    );
}

}
