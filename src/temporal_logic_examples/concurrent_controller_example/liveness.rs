// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::concurrent_controller_example::safety::*;
use crate::concurrent_controller_example::state_machine::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

proof fn lemma_init_leads_to_pod1_exists()
    ensures
        valid(sm_spec()
            .implies(init_state_pred().lift()
                .leads_to(pod1_exists_state_pred().lift()))),
{
    leads_to_eq_auto::<CState>(sm_spec());

    send_create_cr_enabled();
    wf1::<CState>(sm_spec(), next_action_pred(), send_create_cr_action_pred(), init_state_pred(), create_cr_sent_state_pred());

    k8s_create_cr_enabled();
    wf1::<CState>(sm_spec(), next_action_pred(), k8s_create_cr_action_pred(), create_cr_sent_state_pred(), cr_exists_state_pred());

    leads_to_trans::<CState>(sm_spec(), init_state_pred().lift(), create_cr_sent_state_pred().lift(), cr_exists_state_pred().lift());

    // assert(valid(sm_spec()
    //     .implies(init_state_pred().lift()
    //         .leads_to(cr_exists_state_pred().lift()))));

    send_create_sts_pre_and_next_implies_pre_or_post();
    send_create_sts_enabled();
    wf1::<CState>(sm_spec(), next_action_pred(), send_create_sts_action_pred(), send_create_sts_pre_state_pred(), create_sts_sent_state_pred());

    // Note that send_create_sts_pre_state_pred().lift() is the same as
    // cr_exists_state_pred().lift()
    //     .and(not(sts_exists_state_pred().lift()))
    //         .and(not(create_sts_sent_state_pred().lift()))
    leads_to_assume_not::<CState>(sm_spec(), cr_exists_state_pred().lift().and(not(sts_exists_state_pred().lift())), create_sts_sent_state_pred().lift());
    // assert(valid(sm_spec()
    //     .implies(cr_exists_state_pred().lift().and(not(sts_exists_state_pred().lift()))
    //         .leads_to(create_sts_sent_state_pred().lift()))));

    k8s_create_sts_pre_and_next_implies_pre_or_post();
    k8s_create_sts_enabled();
    wf1::<CState>(sm_spec(), next_action_pred(), k8s_create_sts_action_pred(), k8s_create_sts_pre_state_pred(), sts_exists_state_pred());

    create_sts_sent_implies_k8s_create_sts_pre();
    // This leads_to_weaken_left is not necessary since create_sts_sent and k8s_create_sts_pre are actually equivalent.
    // If we weaken k8s_create_sts_pre (which makes it more general), we will need leads_to_weaken_left here.
    // leads_to_weaken_left::<CState>(sm_spec(), k8s_create_sts_pre_state_pred().lift(), create_sts_sent_state_pred().lift(), sts_exists_state_pred().lift());

    leads_to_trans::<CState>(sm_spec(), cr_exists_state_pred().lift().and(not(sts_exists_state_pred().lift())), create_sts_sent_state_pred().lift(), sts_exists_state_pred().lift());
    // assert(valid(sm_spec()
    //     .implies(cr_exists_state_pred().lift().and(not(sts_exists_state_pred().lift()))
    //         .leads_to(sts_exists_state_pred().lift()))));

    leads_to_assume_not::<CState>(sm_spec(), cr_exists_state_pred().lift(), sts_exists_state_pred().lift());
    // assert(valid(sm_spec()
    //     .implies(cr_exists_state_pred().lift()
    //         .leads_to(sts_exists_state_pred().lift()))));

    k8s_create_pod_enabled();
    wf1::<CState>(sm_spec(), next_action_pred(), k8s_create_pod_action_pred(), sts_exists_state_pred(), pod1_exists_state_pred());
    leads_to_trans::<CState>(sm_spec(), cr_exists_state_pred().lift(), sts_exists_state_pred().lift(), pod1_exists_state_pred().lift());
    // assert(valid(sm_spec()
    //     .implies(cr_exists_state_pred().lift()
    //         .leads_to(pod1_exists_state_pred().lift()))));

    leads_to_trans::<CState>(sm_spec(), init_state_pred().lift(), cr_exists_state_pred().lift(), pod1_exists_state_pred().lift());
}


proof fn lemma_init_leads_to_vol1_exists()
    ensures
        valid(sm_spec()
            .implies(init_state_pred().lift()
                .leads_to(vol1_exists_state_pred().lift()))),
{
    leads_to_eq_auto::<CState>(sm_spec());

    send_create_cr_enabled();
    wf1::<CState>(sm_spec(), next_action_pred(), send_create_cr_action_pred(), init_state_pred(), create_cr_sent_state_pred());

    k8s_create_cr_enabled();
    wf1::<CState>(sm_spec(), next_action_pred(), k8s_create_cr_action_pred(), create_cr_sent_state_pred(), cr_exists_state_pred());

    leads_to_trans::<CState>(sm_spec(), init_state_pred().lift(), create_cr_sent_state_pred().lift(), cr_exists_state_pred().lift());

    send_create_vol_pre_and_next_implies_pre_or_post();
    send_create_vol_enabled();
    wf1::<CState>(sm_spec(), next_action_pred(), send_create_vol_action_pred(), send_create_vol_pre_state_pred(), create_vol_sent_state_pred());

    // Note that send_create_vol_pre_state_pred().lift() is the same as
    // cr_exists_state_pred().lift()
    //     .and(not(sts_exists_state_pred().lift()))
    //         .and(not(create_vol_sent_state_pred().lift()))
    leads_to_assume_not::<CState>(sm_spec(), cr_exists_state_pred().lift().and(not(vol1_exists_state_pred().lift())), create_vol_sent_state_pred().lift());

    k8s_create_vol_enabled();
    wf1::<CState>(sm_spec(), next_action_pred(), k8s_create_vol_action_pred(), create_vol_sent_state_pred(), vol1_exists_state_pred());

    leads_to_trans::<CState>(sm_spec(), cr_exists_state_pred().lift().and(not(vol1_exists_state_pred().lift())), create_vol_sent_state_pred().lift(), vol1_exists_state_pred().lift());

    leads_to_assume_not::<CState>(
        sm_spec(),
        cr_exists_state_pred().lift(),
        vol1_exists_state_pred().lift()
    );

    leads_to_trans::<CState>(sm_spec(), init_state_pred().lift(), cr_exists_state_pred().lift(), vol1_exists_state_pred().lift());
}

proof fn lemma_eventually_vol_attached()
    ensures
        valid(sm_spec()
            .implies(eventually(vol_attached_state_pred().lift())))
{
    leads_to_weaken_auto::<CState>(sm_spec());

    lemma_init_leads_to_pod1_exists();
    leads_to_stable::<CState>(sm_spec(), next_action_pred(), init_state_pred().lift(), pod1_exists_state_pred());
    // assert(valid(sm_spec()
    //     .implies(init_state_pred().lift()
    //         .leads_to(always(pod1_exists_state_pred().lift())))));

    lemma_init_leads_to_vol1_exists();
    leads_to_stable::<CState>(sm_spec(), next_action_pred(), init_state_pred().lift(), vol1_exists_state_pred());
    // assert(valid(sm_spec()
    //     .implies(init_state_pred().lift()
    //         .leads_to(always(vol1_exists_state_pred().lift())))));

    leads_to_always_combine::<CState>(sm_spec(), init_state_pred().lift(), pod1_exists_state_pred().lift(), vol1_exists_state_pred().lift());
    // assert(valid(sm_spec()
    //     .implies(init_state_pred().lift()
    //         .leads_to(always(pod1_exists_state_pred().lift().and(vol1_exists_state_pred().lift()))))));


    leads_to_always_weaken::<CState>(sm_spec(), init_state_pred().lift(), pod1_exists_state_pred().lift().and(vol1_exists_state_pred().lift()));
    // assert(valid(sm_spec()
    //     .implies(init_state_pred().lift()
    //         .leads_to(pod1_exists_state_pred().lift().and(vol1_exists_state_pred().lift())))));

    k8s_attach_vol_to_pod_enabled();
    wf1::<CState>(sm_spec(), next_action_pred(), k8s_attach_vol_to_pod_action_pred(), k8s_attach_vol_to_pod_pre_state_pred(), vol_attached_state_pred());

    leads_to_trans::<CState>(sm_spec(), init_state_pred().lift(), k8s_attach_vol_to_pod_pre_state_pred().lift(), vol_attached_state_pred().lift());

    leads_to_apply::<CState>(sm_spec(), init_state_pred().lift(), vol_attached_state_pred().lift());
}


proof fn liveness()
    ensures
        valid(sm_spec()
            .implies(eventually(vol_attached_state_pred().lift()
                .and(pod1_exists_state_pred().lift())
                    .and(vol1_exists_state_pred().lift())))),
{
    lemma_eventually_vol_attached();
    lemma_attach_after_create_inv_state_pred();
    always_and_eventually::<CState>(sm_spec(), attach_after_create_inv_state_pred().lift(), vol_attached_state_pred().lift());
    eventually_weaken::<CState>(
        sm_spec(),
        attach_after_create_inv_state_pred().lift().and(vol_attached_state_pred().lift()),
        vol_attached_state_pred().lift().and(pod1_exists_state_pred().lift()).and(vol1_exists_state_pred().lift())
    );
}

}
