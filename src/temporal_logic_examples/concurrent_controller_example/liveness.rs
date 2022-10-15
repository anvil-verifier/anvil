// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::concurrent_controller_example::state_machine::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

spec fn pod1_exists_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| state.resources.dom().contains(new_strlit("my_pod1")@))
}

spec fn vol1_exists_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| state.resources.dom().contains(new_strlit("my_volume1")@))
}

spec fn vol_attached_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| state.vol_attached)
}

proof fn lemma_init_leads_to_pod1_exists()
    ensures
        valid(sm_spec()
            .implies(init_state_pred().lift()
                .leads_to(pod1_exists_state_pred().lift()))),
{
    implies_apply_auto::<CState>();
    leads_to_eq_auto::<CState>(sm_spec());

    send_create_cr_enabled();
    wf1::<CState>(next_action_pred(), send_create_cr_action_pred(), send_create_cr_pre_state_pred(), k8s_create_cr_pre_state_pred());

    k8s_create_cr_enabled();
    wf1::<CState>(next_action_pred(), k8s_create_cr_action_pred(), k8s_create_cr_pre_state_pred(), send_create_sts_pre_state_pred());

    send_create_sts_enabled();
    wf1::<CState>(next_action_pred(), send_create_sts_action_pred(), send_create_sts_pre_state_pred(), k8s_create_sts_pre_state_pred());

    k8s_create_sts_enabled();
    wf1::<CState>(next_action_pred(), k8s_create_sts_action_pred(), k8s_create_sts_pre_state_pred(), k8s_create_pod_pre_state_pred());

    k8s_create_pod_enabled();
    wf1::<CState>(next_action_pred(), k8s_create_pod_action_pred(), k8s_create_pod_pre_state_pred(), pod1_exists_state_pred());

    leads_to_trans::<CState>(sm_spec(), send_create_cr_pre_state_pred().lift(), k8s_create_cr_pre_state_pred().lift(), send_create_sts_pre_state_pred().lift());
    leads_to_trans::<CState>(sm_spec(), send_create_cr_pre_state_pred().lift(), send_create_sts_pre_state_pred().lift(), k8s_create_sts_pre_state_pred().lift());
    leads_to_trans::<CState>(sm_spec(), send_create_cr_pre_state_pred().lift(), k8s_create_sts_pre_state_pred().lift(), k8s_create_pod_pre_state_pred().lift());
    leads_to_trans::<CState>(sm_spec(), send_create_cr_pre_state_pred().lift(), k8s_create_pod_pre_state_pred().lift(), pod1_exists_state_pred().lift());
}


proof fn lemma_init_leads_to_vol1_exists()
    ensures
        valid(sm_spec()
            .implies(init_state_pred().lift()
                .leads_to(vol1_exists_state_pred().lift()))),
{
    implies_apply_auto::<CState>();
    leads_to_eq_auto::<CState>(sm_spec());

    send_create_cr_enabled();
    wf1::<CState>(next_action_pred(), send_create_cr_action_pred(), send_create_cr_pre_state_pred(), k8s_create_cr_pre_state_pred());

    k8s_create_cr_enabled();
    wf1::<CState>(next_action_pred(), k8s_create_cr_action_pred(), k8s_create_cr_pre_state_pred(), send_create_vol_pre_state_pred());

    send_create_vol_enabled();
    wf1::<CState>(next_action_pred(), send_create_vol_action_pred(), send_create_vol_pre_state_pred(), k8s_create_vol_pre_state_pred());

    k8s_create_vol_enabled();
    wf1::<CState>(next_action_pred(), k8s_create_vol_action_pred(), k8s_create_vol_pre_state_pred(), vol1_exists_state_pred());


    leads_to_trans::<CState>(sm_spec(), send_create_cr_pre_state_pred().lift(), k8s_create_cr_pre_state_pred().lift(), send_create_vol_pre_state_pred().lift());
    leads_to_trans::<CState>(sm_spec(), send_create_cr_pre_state_pred().lift(), send_create_vol_pre_state_pred().lift(), k8s_create_vol_pre_state_pred().lift());
    leads_to_trans::<CState>(sm_spec(), send_create_cr_pre_state_pred().lift(), k8s_create_vol_pre_state_pred().lift(), vol1_exists_state_pred().lift());

}

proof fn lemma_eventually_vol_attached()
    ensures
        valid(sm_spec()
            .implies(eventually(vol_attached_state_pred().lift())))
{
    implies_apply_auto::<CState>();

    leads_to_weaken_auto::<CState>(sm_spec());

    lemma_init_leads_to_pod1_exists();
    leads_to_stable::<CState>(sm_spec(), next_action_pred(), init_state_pred().lift(), pod1_exists_state_pred());

    lemma_init_leads_to_vol1_exists();
    leads_to_stable::<CState>(sm_spec(), next_action_pred(), init_state_pred().lift(), vol1_exists_state_pred());

    leads_to_always_combine::<CState>(sm_spec(), init_state_pred().lift(), pod1_exists_state_pred().lift(), vol1_exists_state_pred().lift());

    always_weaken::<CState>(pod1_exists_state_pred().lift().and(vol1_exists_state_pred().lift()));

    assert(valid(sm_spec()
        .implies(init_state_pred().lift()
            .leads_to(pod1_exists_state_pred().lift()
                .and(vol1_exists_state_pred().lift())))));

    k8s_attach_vol_to_pod_enabled();
    wf1::<CState>(next_action_pred(), k8s_attach_vol_to_pod_action_pred(), k8s_attach_vol_to_pod_pre_state_pred(), vol_attached_state_pred());

    leads_to_trans::<CState>(sm_spec(), init_state_pred().lift(), k8s_attach_vol_to_pod_pre_state_pred().lift(), vol_attached_state_pred().lift());

    leads_to_apply::<CState>(sm_spec(), init_state_pred().lift(), vol_attached_state_pred().lift());
}


}
