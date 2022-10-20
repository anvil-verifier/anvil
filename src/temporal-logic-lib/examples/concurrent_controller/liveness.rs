// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
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
        valid(sm_spec()
            .implies(init().lift()
                .leads_to(pod1_exists().lift()))),
{
    leads_to_eq_temp_auto::<CState>(sm_spec());
    use_tla_forall::<CState, Message>(sm_spec(), |m: Message| weak_fairness(k8s_handle_create_concretized(m)), create_cr_msg());
    use_tla_forall::<CState, Message>(sm_spec(), |m: Message| weak_fairness(k8s_handle_create_concretized(m)), create_sts_msg());

    send_create_cr_enabled();
    k8s_handle_any_create_msg_pre_implies_enabled(create_cr_msg());
    wf1_chain::<CState>(sm_spec(),
        next(),
        send_create_cr(),
        k8s_handle_create_concretized(create_cr_msg()),
        init(),
        k8s_handle_create_pre_concretized(create_cr_msg()),
        cr_exists(),
    );

    send_create_sts_enabled();
    wf1::<CState>(sm_spec(),
        next(),
        send_create_sts(),
        cr_exists_and_not_create_sts_sent(),
        create_sts_sent()
    );
    leads_to_assume_not::<CState>(sm_spec(),
        cr_exists(),
        create_sts_sent()
    );

    k8s_handle_any_create_msg_pre_implies_enabled(create_sts_msg());
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create_concretized(create_sts_msg()),
        k8s_handle_create_pre_concretized(create_sts_msg()),
        k8s_handle_create_post_concretized(create_sts_msg()),
    );

    leads_to_trans::<CState>(sm_spec(),
        cr_exists(),
        create_sts_sent(),
        sts_exists()
    );

    k8s_create_pod_enabled();
    wf1::<CState>(sm_spec(),
        next(),
        k8s_create_pod(),
        sts_exists(),
        pod1_exists()
    );
    leads_to_trans::<CState>(sm_spec(),
        cr_exists(),
        sts_exists(),
        pod1_exists()
    );

    leads_to_trans::<CState>(sm_spec(),
        init(),
        cr_exists(),
        pod1_exists()
    );
}

}
