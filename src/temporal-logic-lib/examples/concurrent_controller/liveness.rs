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
        sm_spec()
            .entails(StatePred::new(|state| init(state)).lift()
                .leads_to(StatePred::new(|state| resource_exists(state, new_strlit("my_pod1")@)).lift())),
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
        StatePred::new(|state| init(state)),
        (|message: Message| StatePred::new(|state| message_sent(state, message)))(create_cr_msg()),
        StatePred::new(|state| resource_exists(state, new_strlit("my_cr")@)),
    );

    send_create_sts_enabled();
    wf1::<CState>(sm_spec(),
        next(),
        send_create_sts(),
        StatePred::new(|state| {
            &&& resource_exists(state, new_strlit("my_cr")@)
            &&& !message_sent(state, Message::CreateStatefulSet{replica: 1})
        }),
        StatePred::new(|state| message_sent(state, Message::CreateStatefulSet{replica: 1}))
    );
    leads_to_assume_not::<CState>(sm_spec(),
        StatePred::new(|state| resource_exists(state, new_strlit("my_cr")@)),
        StatePred::new(|state| message_sent(state, Message::CreateStatefulSet{replica: 1}))
    );

    k8s_handle_create_enabled(create_sts_msg());
    wf1::<CState>(sm_spec(),
        next(),
        k8s_handle_create(create_sts_msg()),
        (|message: Message| StatePred::new(|state| message_sent(state, message)))(create_sts_msg()),
        StatePred::new(|state| resource_exists(state, new_strlit("my_statefulset")@))
    );

    leads_to_trans::<CState>(sm_spec(),
        StatePred::new(|state| resource_exists(state, new_strlit("my_cr")@)),
        StatePred::new(|state| message_sent(state, Message::CreateStatefulSet{replica: 1})),
        StatePred::new(|state| resource_exists(state, new_strlit("my_statefulset")@))
    );

    k8s_create_pod_enabled();
    wf1::<CState>(sm_spec(),
        next(),
        k8s_create_pod(),
        StatePred::new(|state| resource_exists(state, new_strlit("my_statefulset")@)),
        StatePred::new(|state| resource_exists(state, new_strlit("my_pod1")@))
    );
    leads_to_trans::<CState>(sm_spec(),
        StatePred::new(|state| resource_exists(state, new_strlit("my_cr")@)),
        StatePred::new(|state| resource_exists(state, new_strlit("my_statefulset")@)),
        StatePred::new(|state| resource_exists(state, new_strlit("my_pod1")@))
    );

    leads_to_trans::<CState>(sm_spec(),
        StatePred::new(|state| init(state)),
        StatePred::new(|state| resource_exists(state, new_strlit("my_cr")@)),
        StatePred::new(|state| resource_exists(state, new_strlit("my_pod1")@))
    );
}

}
