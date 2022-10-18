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
            .implies(init().lift()
                .leads_to(pod1_exists().lift()))),
{
    leads_to_eq_auto::<CState>(sm_spec());

    send_create_cr_enabled();
    wf1::<CState>(sm_spec(), next(), send_create_cr(), init(), create_cr_sent());

    k8s_create_cr_enabled();
    wf1::<CState>(sm_spec(), next(), k8s_create_cr(), create_cr_sent(), cr_exists());

    leads_to_trans::<CState>(sm_spec(), init().lift(), create_cr_sent().lift(), cr_exists().lift());

    // assert(valid(sm_spec()
    //     .implies(init().lift()
    //         .leads_to(cr_exists().lift()))));

    send_create_sts_pre_and_next_implies_pre_or_post();
    send_create_sts_enabled();
    wf1::<CState>(sm_spec(), next(), send_create_sts(), send_create_sts_precondition(), create_sts_sent());

    // Note that send_create_sts_precondition().lift() is the same as
    // cr_exists().lift()
    //     .and(not(sts_exists().lift()))
    //         .and(not(create_sts_sent().lift()))
    leads_to_assume_not::<CState>(sm_spec(), cr_exists().lift().and(not(sts_exists().lift())), create_sts_sent().lift());
    // assert(valid(sm_spec()
    //     .implies(cr_exists().lift().and(not(sts_exists().lift()))
    //         .leads_to(create_sts_sent().lift()))));

    k8s_create_sts_pre_and_next_implies_pre_or_post();
    k8s_create_sts_enabled();
    wf1::<CState>(sm_spec(), next(), k8s_create_sts(), k8s_create_sts_precondition(), sts_exists());

    create_sts_sent_implies_sm_k8s_create_sts_precondition();
    // This leads_to_weaken_left is not necessary since create_sts_sent and k8s_create_sts_pre are actually equivalent.
    // If we weaken k8s_create_sts_pre (which makes it more general), we will need leads_to_weaken_left here.
    // leads_to_weaken_left::<CState>(sm_spec(), k8s_create_sts_precondition().lift(), create_sts_sent().lift(), sts_exists().lift());

    leads_to_trans::<CState>(sm_spec(), cr_exists().lift().and(not(sts_exists().lift())), create_sts_sent().lift(), sts_exists().lift());
    // assert(valid(sm_spec()
    //     .implies(cr_exists().lift().and(not(sts_exists().lift()))
    //         .leads_to(sts_exists().lift()))));

    leads_to_assume_not::<CState>(sm_spec(), cr_exists().lift(), sts_exists().lift());
    // assert(valid(sm_spec()
    //     .implies(cr_exists().lift()
    //         .leads_to(sts_exists().lift()))));

    k8s_create_pod_enabled();
    wf1::<CState>(sm_spec(), next(), k8s_create_pod(), sts_exists(), pod1_exists());
    leads_to_trans::<CState>(sm_spec(), cr_exists().lift(), sts_exists().lift(), pod1_exists().lift());
    // assert(valid(sm_spec()
    //     .implies(cr_exists().lift()
    //         .leads_to(pod1_exists().lift()))));

    leads_to_trans::<CState>(sm_spec(), init().lift(), cr_exists().lift(), pod1_exists().lift());
}


proof fn lemma_init_leads_to_vol1_exists()
    ensures
        valid(sm_spec()
            .implies(init().lift()
                .leads_to(vol1_exists().lift()))),
{
    leads_to_eq_auto::<CState>(sm_spec());

    send_create_cr_enabled();
    wf1::<CState>(sm_spec(), next(), send_create_cr(), init(), create_cr_sent());

    k8s_create_cr_enabled();
    wf1::<CState>(sm_spec(), next(), k8s_create_cr(), create_cr_sent(), cr_exists());

    leads_to_trans::<CState>(sm_spec(), init().lift(), create_cr_sent().lift(), cr_exists().lift());

    sm_send_create_vol_precondition_and_next_implies_pre_or_post();
    send_create_vol_enabled();
    wf1::<CState>(sm_spec(), next(), send_create_vol(), send_create_vol_precondition(), create_vol_sent());

    // Note that send_create_vol_precondition().lift() is the same as
    // cr_exists().lift()
    //     .and(not(sts_exists().lift()))
    //         .and(not(create_vol_sent().lift()))
    leads_to_assume_not::<CState>(sm_spec(), cr_exists().lift().and(not(vol1_exists().lift())), create_vol_sent().lift());

    k8s_create_vol_enabled();
    wf1::<CState>(sm_spec(), next(), k8s_create_vol(), create_vol_sent(), vol1_exists());

    leads_to_trans::<CState>(sm_spec(), cr_exists().lift().and(not(vol1_exists().lift())), create_vol_sent().lift(), vol1_exists().lift());

    leads_to_assume_not::<CState>(
        sm_spec(),
        cr_exists().lift(),
        vol1_exists().lift()
    );

    leads_to_trans::<CState>(sm_spec(), init().lift(), cr_exists().lift(), vol1_exists().lift());
}

proof fn lemma_eventually_vol_attached()
    ensures
        valid(sm_spec()
            .implies(eventually(vol_attached().lift())))
{
    leads_to_weaken_auto::<CState>(sm_spec());

    lemma_init_leads_to_pod1_exists();
    leads_to_stable::<CState>(sm_spec(), next(), init().lift(), pod1_exists());
    // assert(valid(sm_spec()
    //     .implies(init().lift()
    //         .leads_to(always(pod1_exists().lift())))));

    lemma_init_leads_to_vol1_exists();
    leads_to_stable::<CState>(sm_spec(), next(), init().lift(), vol1_exists());
    // assert(valid(sm_spec()
    //     .implies(init().lift()
    //         .leads_to(always(vol1_exists().lift())))));

    leads_to_always_combine::<CState>(sm_spec(), init().lift(), pod1_exists().lift(), vol1_exists().lift());
    // assert(valid(sm_spec()
    //     .implies(init().lift()
    //         .leads_to(always(pod1_exists().lift().and(vol1_exists().lift()))))));


    leads_to_always_weaken::<CState>(sm_spec(), init().lift(), pod1_exists().lift().and(vol1_exists().lift()));
    // assert(valid(sm_spec()
    //     .implies(init().lift()
    //         .leads_to(pod1_exists().lift().and(vol1_exists().lift())))));

    k8s_attach_vol_to_pod_enabled();
    wf1::<CState>(sm_spec(), next(), k8s_attach_vol_to_pod(), k8s_attach_vol_to_pod_precondition(), vol_attached());

    leads_to_trans::<CState>(sm_spec(), init().lift(), k8s_attach_vol_to_pod_precondition().lift(), vol_attached().lift());

    leads_to_apply::<CState>(sm_spec(), init().lift(), vol_attached().lift());
}


proof fn liveness()
    ensures
        valid(sm_spec()
            .implies(eventually(vol_attached().lift()
                .and(pod1_exists().lift())
                    .and(vol1_exists().lift())))),
{
    lemma_eventually_vol_attached();
    lemma_always_attach_after_create();
    always_and_eventually::<CState>(sm_spec(), attach_after_create().lift(), vol_attached().lift());
    eventually_weaken::<CState>(
        sm_spec(),
        attach_after_create().lift().and(vol_attached().lift()),
        vol_attached().lift().and(pod1_exists().lift()).and(vol1_exists().lift())
    );
}

}
