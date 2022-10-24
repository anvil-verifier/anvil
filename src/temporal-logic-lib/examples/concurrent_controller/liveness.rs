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


proof fn lemma_init_leads_to_pod1_exists()
    ensures
        sm_spec()
            .entails(lift_state(init())
                .leads_to(lift_state(|s| resource_exists(s, new_strlit("my_statefulset_pod1")@)))),
{
    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_cr_msg(new_strlit("my_cr")@));
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_sts_msg(new_strlit("my_statefulset")@));
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_pod_msg(new_strlit("my_statefulset_pod1")@));

    user_send_create_cr_enabled();
    k8s_handle_create_enabled(create_cr_msg(new_strlit("my_cr")@));
    wf1_chain::<CState>(sm_spec(),
        next(),
        user_send_create_cr(),
        k8s_handle_create(create_cr_msg(new_strlit("my_cr")@)),
        init(),
        k8s_handle_create_pre(create_cr_msg(new_strlit("my_cr")@)),
        |s| resource_exists(s, new_strlit("my_cr")@),
    );

    controller_send_create_sts_enabled();
    wf1::<CState>(sm_spec(),
        next(),
        controller_send_create_sts(),
        |s| {
            &&& resource_exists(s, new_strlit("my_cr")@)
            &&& !message_sent(s, create_sts_msg(new_strlit("my_statefulset")@))
        },
        |s| message_sent(s, create_sts_msg(new_strlit("my_statefulset")@))
    );
    leads_to_assume_not::<CState>(sm_spec(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| message_sent(s, create_sts_msg(new_strlit("my_statefulset")@))
    );

    reveal_strlit("my_statefulset");
    reveal_strlit("_pod1");
    reveal_strlit("my_statefulset_pod1");
    strlit_concat_equality(new_strlit("my_statefulset")@, new_strlit("_pod1")@, new_strlit("my_statefulset_pod1")@);

    k8s_handle_create_enabled(create_sts_msg(new_strlit("my_statefulset")@));
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_sts_msg(new_strlit("my_statefulset")@)),
        k8s_handle_create_pre(create_sts_msg(new_strlit("my_statefulset")@)),
        |s| {
            &&& resource_exists(s, new_strlit("my_statefulset")@)
            &&& message_sent(s, create_pod_msg(new_strlit("my_statefulset_pod1")@))
        }
    );

    leads_to_trans::<CState>(sm_spec(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| message_sent(s, create_sts_msg(new_strlit("my_statefulset")@)),
        |s| {
            &&& resource_exists(s, new_strlit("my_statefulset")@)
            &&& message_sent(s, create_pod_msg(new_strlit("my_statefulset_pod1")@))
        }
    );

    leads_to_weaken_right::<CState>(sm_spec(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| {
            &&& resource_exists(s, new_strlit("my_statefulset")@)
            &&& message_sent(s, create_pod_msg(new_strlit("my_statefulset_pod1")@))
        },
        |s| message_sent(s, create_pod_msg(new_strlit("my_statefulset_pod1")@))
    );

    k8s_handle_create_enabled(create_pod_msg(new_strlit("my_statefulset_pod1")@));
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_pod_msg(new_strlit("my_statefulset_pod1")@)),
        k8s_handle_create_pre(create_pod_msg(new_strlit("my_statefulset_pod1")@)),
        |s| resource_exists(s, new_strlit("my_statefulset_pod1")@)
    );
    leads_to_trans::<CState>(sm_spec(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        // |s| resource_exists(s, new_strlit("my_statefulset")@),
        |s| message_sent(s, create_pod_msg(new_strlit("my_statefulset_pod1")@)),
        |s| resource_exists(s, new_strlit("my_statefulset_pod1")@)
    );

    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| resource_exists(s, new_strlit("my_statefulset_pod1")@)
    );
}

proof fn lemma_init_leads_to_vol1_exists()
    ensures
        sm_spec()
            .entails(lift_state(init())
                .leads_to(lift_state(|s| resource_exists(s, new_strlit("my_volume1")@)))),
{
    leads_to_eq_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_cr_msg(new_strlit("my_cr")@));
    use_tla_forall::<CState, Message>(sm_spec(), |msg| weak_fairness(k8s_handle_create(msg)), create_vol_msg(new_strlit("my_volume1")@));

    user_send_create_cr_enabled();
    k8s_handle_create_enabled(create_cr_msg(new_strlit("my_cr")@));
    wf1_chain::<CState>(sm_spec(),
        next(),
        user_send_create_cr(),
        k8s_handle_create(create_cr_msg(new_strlit("my_cr")@)),
        init(),
        k8s_handle_create_pre(create_cr_msg(new_strlit("my_cr")@)),
        |s| resource_exists(s, new_strlit("my_cr")@),
    );

    controller_send_create_vol_enabled();
    wf1::<CState>(sm_spec(),
        next(),
        controller_send_create_vol(),
        |s| {
            &&& resource_exists(s, new_strlit("my_cr")@)
            &&& !message_sent(s, create_vol_msg(new_strlit("my_volume1")@))
        },
        |s| message_sent(s, create_vol_msg(new_strlit("my_volume1")@))
    );
    leads_to_assume_not::<CState>(sm_spec(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| message_sent(s, create_vol_msg(new_strlit("my_volume1")@))
    );

    k8s_handle_create_enabled(create_vol_msg(new_strlit("my_volume1")@));
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_vol_msg(new_strlit("my_volume1")@)),
        k8s_handle_create_pre(create_vol_msg(new_strlit("my_volume1")@)),
        |s| resource_exists(s, new_strlit("my_volume1")@)
    );

    leads_to_trans::<CState>(sm_spec(),
        |s| resource_exists(s, new_strlit("my_cr")@),
        |s| message_sent(s, create_vol_msg(new_strlit("my_volume1")@)),
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
        |s| resource_exists(s, new_strlit("my_statefulset_pod1")@)
    );

    lemma_init_leads_to_vol1_exists();
    leads_to_stable::<CState>(sm_spec(),
        next(),
        init(),
        |s| resource_exists(s, new_strlit("my_volume1")@)
    );

    leads_to_always_combine_then_weaken::<CState>(sm_spec(),
        init(),
        |s| resource_exists(s, new_strlit("my_statefulset_pod1")@),
        |s| resource_exists(s, new_strlit("my_volume1")@)
    );

    k8s_attach_vol_to_pod_enabled();
    wf1::<CState>(sm_spec(),
        next(),
        k8s_attach_vol_to_pod(),
        |s| {
            &&& resource_exists(s, new_strlit("my_statefulset_pod1")@)
            &&& resource_exists(s, new_strlit("my_volume1")@)
        },
        |s: CState| s.vol_attached
    );

    leads_to_trans::<CState>(sm_spec(),
        init(),
        |s| {
            &&& resource_exists(s, new_strlit("my_statefulset_pod1")@)
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
                    &&& resource_exists(s, new_strlit("my_statefulset_pod1")@)
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
            &&& s.vol_attached ==> resource_exists(s, new_strlit("my_statefulset_pod1")@)
            &&& s.vol_attached ==> resource_exists(s, new_strlit("my_volume1")@)
        },
        |s: CState| s.vol_attached
    );

    eventually_weaken::<CState>(sm_spec(),
        |s: CState| {
            &&& s.vol_attached ==> resource_exists(s, new_strlit("my_statefulset_pod1")@)
            &&& s.vol_attached ==> resource_exists(s, new_strlit("my_volume1")@)
            &&& s.vol_attached
        },
        |s: CState| {
            &&& resource_exists(s, new_strlit("my_statefulset_pod1")@)
            &&& resource_exists(s, new_strlit("my_volume1")@)
            &&& s.vol_attached
        }
    );
}

}
