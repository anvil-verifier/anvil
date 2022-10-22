// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::map::*;
use crate::pervasive::seq::*;
use crate::pervasive::set::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

#[is_variant]
pub enum Message {
    CreateCR,
    CreateStatefulSet{replica: nat},
    CreateVolume{id: nat},
}

#[is_variant]
pub enum Resource {
    CustomResource,
    StatefulSet,
    Pod,
    Volume{attached: bool},
}

pub struct CState {
    pub resources: Map<Seq<char>, Resource>,
    pub messages: Set<Message>,
    pub vol_attached: bool,
}

/**
 *                      init
 *                        |
 *                 send_create_cr
 *                        |
 *                 k8s_create_cr
 *                 /           \
 *  send_create_sts             send_create_vol
 *                |             |
 *   k8s_create_sts             k8s_create_vol
 *                |             |
 *   k8s_create_pod             |
 *                \             /
 *                 \           /
 *             k8s_attach_vol_to_pod
 *
 *
 * TODO: k8s_create_vol and k8s_create_pod should be like
 *  {
 *      exists |i: nat|
 *          // create pod_i/volume_i
 *  }
 */

pub open spec fn message_sent(s: CState, m: Message) -> bool {
    s.messages.contains(m)
}

pub open spec fn resource_exists(s: CState, key: Seq<char>) -> bool {
    s.resources.dom().contains(key)
}

pub open spec fn resources_updated_with(s: CState, s_prime: CState, key: Seq<char>, val: Resource) -> bool {
    if resource_exists(s, key) {
        s_prime === s
    } else {
        s_prime === CState {
            resources: s.resources.insert(key, val),
            ..s
        }
    }
}

pub open spec fn init() -> StatePred<CState> {
    |s: CState| {
        &&& s.resources === Map::empty()
        &&& s.messages === Set::empty()
        &&& !s.vol_attached
    }
}

pub open spec fn send_create_cr() -> ActionPred<CState> {
    |s, s_prime| {
        &&& init()(s)
        &&& s_prime === CState {
            messages: s.messages.insert(Message::CreateCR),
            ..s
        }
    }
}

pub open spec fn send_create_sts_pre() -> StatePred<CState> {
    |s| {
        &&& resource_exists(s, new_strlit("my_cr")@)
        &&& !message_sent(s, Message::CreateStatefulSet{replica: 1})
    }
}

pub open spec fn send_create_sts() -> ActionPred<CState> {
    |s, s_prime| {
        &&& send_create_sts_pre()(s)
        &&& s_prime === CState {
            messages: s.messages.insert(Message::CreateStatefulSet{replica: 1}),
            ..s
        }
    }
}

pub open spec fn send_create_vol_pre() -> StatePred<CState> {
    |s| {
        &&& resource_exists(s, new_strlit("my_cr")@)
        &&& !message_sent(s, Message::CreateVolume{id: 1})
    }
}

pub open spec fn send_create_vol() -> ActionPred<CState> {
    |s, s_prime| {
        &&& send_create_vol_pre()(s)
        &&& s_prime === CState {
            messages: s.messages.insert(Message::CreateVolume{id: 1}),
            ..s
        }
    }
}

pub open spec fn k8s_handle_create_pre(msg: Message) -> StatePred<CState> {
    |s| message_sent(s, msg)
}

// TODO: k8s_handle_create should not be hardcoded to my_xxx
pub open spec fn k8s_handle_create(msg: Message) -> ActionPred<CState> {
    |s, s_prime| {
        &&& k8s_handle_create_pre(msg)(s)
        &&& match msg {
            Message::CreateCR => resources_updated_with(s, s_prime, new_strlit("my_cr")@, Resource::CustomResource),
            Message::CreateStatefulSet{..} => resources_updated_with(s, s_prime, new_strlit("my_statefulset")@, Resource::StatefulSet),
            Message::CreateVolume{..} => resources_updated_with(s, s_prime, new_strlit("my_volume1")@, Resource::Volume{attached: false}),
        }
    }
}

pub open spec fn k8s_create_pod_pre() -> StatePred<CState> {
    |s| {
        resource_exists(s, new_strlit("my_statefulset")@)
    }
}

pub open spec fn k8s_create_pod() -> ActionPred<CState> {
    |s, s_prime| {
        &&& k8s_create_pod_pre()(s)
        &&& s_prime === CState {
            resources: s.resources.insert(new_strlit("my_pod1")@, Resource::Pod),
            ..s
        }
    }
}

pub open spec fn k8s_attach_vol_to_pod_pre() -> StatePred<CState> {
    |s| {
        &&& resource_exists(s, new_strlit("my_pod1")@)
        &&& resource_exists(s, new_strlit("my_volume1")@)
    }
}

pub open spec fn k8s_attach_vol_to_pod() -> ActionPred<CState> {
    |s, s_prime| {
        &&& k8s_attach_vol_to_pod_pre()(s)
        &&& s_prime === CState {
            vol_attached: true,
            ..s
        }
    }
}

pub open spec fn stutter() -> ActionPred<CState> {
    |s, s_prime| s === s_prime
}

pub open spec fn next() -> ActionPred<CState> {
    |s, s_prime| {
        ||| send_create_cr()(s, s_prime)
        ||| send_create_sts()(s, s_prime)
        ||| send_create_vol()(s, s_prime)
        ||| exists |msg| #[trigger] action_pred_call(k8s_handle_create(msg), s, s_prime)
        ||| k8s_create_pod()(s, s_prime)
        ||| k8s_attach_vol_to_pod()(s, s_prime)
        ||| stutter()(s, s_prime)
    }
}

pub open spec fn sm_spec() -> TempPred<CState> {
    lift_state(init())
    .and(always(lift_action(next())))
    .and(weak_fairness(send_create_cr()))
    .and(weak_fairness(send_create_sts()))
    .and(weak_fairness(send_create_vol()))
    .and(tla_forall(|msg| weak_fairness(k8s_handle_create(msg))))
    .and(weak_fairness(k8s_create_pod()))
    .and(weak_fairness(k8s_attach_vol_to_pod()))
}

pub proof fn send_create_cr_enabled()
    ensures
        forall |s| init()(s)
            ==> state_pred_call(enabled(send_create_cr()), s),
{
    assert forall |s| init()(s)
    implies state_pred_call(enabled(send_create_cr()), s) by {
        let witness_s_prime = CState {
            messages: s.messages.insert(Message::CreateCR),
            ..s
        };
        assert(action_pred_call(send_create_cr(), s, witness_s_prime));
    };
}

/// Note that in some cases we need to call reveal_strlit to tell Verus two strings are not the same, like:
///
/// reveal_strlit("my_volume1");
/// reveal_strlit("my_statefulset");
/// assert(!new_strlit("my_statefulset")@.ext_equal(new_strlit("my_volume1")@));
/// assert(new_strlit("my_statefulset")@ !== new_strlit("my_volume1")@);
///
/// TODO: run it with Verus team

pub proof fn send_create_sts_enabled()
    ensures
        forall |s| send_create_sts_pre()(s)
            ==> state_pred_call(enabled(send_create_sts()), s),
{
    assert forall |s| send_create_sts_pre()(s)
    implies state_pred_call(enabled(send_create_sts()), s) by {
        let witness_s_prime = CState {
            messages: s.messages.insert(Message::CreateStatefulSet{replica: 1}),
            ..s
        };
        assert(action_pred_call(send_create_sts(), s, witness_s_prime));
    };
}

pub proof fn send_create_vol_enabled()
    ensures
        forall |s| send_create_vol_pre()(s)
            ==> state_pred_call(enabled(send_create_vol()), s),
{
    assert forall |s| send_create_vol_pre()(s)
    implies state_pred_call(enabled(send_create_vol()), s) by {
        let witness_s_prime = CState {
            messages: s.messages.insert(Message::CreateVolume{id: 1}),
            ..s
        };
        assert(action_pred_call(send_create_vol(), s, witness_s_prime));
    };
}

pub open spec fn k8s_handle_create_witness_s_prime(state: CState, key: Seq<char>, val: Resource) -> CState {
    if state.resources.dom().contains(key) {
        state
    } else {
        CState {
            resources: state.resources.insert(key, val),
            ..state
        }
    }
}

pub proof fn k8s_handle_create_enabled(msg: Message)
    ensures
        forall |s| k8s_handle_create_pre(msg)(s)
            ==> #[trigger] state_pred_call(enabled(k8s_handle_create(msg)), s),
{
    assert forall |s| k8s_handle_create_pre(msg)(s)
    implies #[trigger] state_pred_call(enabled(k8s_handle_create(msg)), s) by {
        match msg {
            Message::CreateCR => {
                let witness_s_prime = k8s_handle_create_witness_s_prime(s, new_strlit("my_cr")@, Resource::CustomResource);
                assert(action_pred_call(k8s_handle_create(msg), s, witness_s_prime));
            },
            Message::CreateStatefulSet{..} => {
                let witness_s_prime = k8s_handle_create_witness_s_prime(s, new_strlit("my_statefulset")@, Resource::StatefulSet);
                assert(action_pred_call(k8s_handle_create(msg), s, witness_s_prime));
            },
            Message::CreateVolume{..} => {
                let witness_s_prime = k8s_handle_create_witness_s_prime(s, new_strlit("my_volume1")@, Resource::Volume{attached: false});
                assert(action_pred_call(k8s_handle_create(msg), s, witness_s_prime));
            },
        }
    };
}

pub proof fn k8s_create_pod_enabled()
    ensures
        forall |s| k8s_create_pod_pre()(s)
            ==> state_pred_call(enabled(k8s_create_pod()), s),
{
    assert forall |s| k8s_create_pod_pre()(s)
    implies state_pred_call(enabled(k8s_create_pod()), s) by {
        let witness_s_prime = CState {
            resources: s.resources.insert(new_strlit("my_pod1")@, Resource::Pod),
            ..s
        };
        assert(action_pred_call(k8s_create_pod(), s, witness_s_prime));
    };
}

pub proof fn k8s_attach_vol_to_pod_enabled()
    ensures
        forall |s| k8s_attach_vol_to_pod_pre()(s)
            ==> state_pred_call(enabled(k8s_attach_vol_to_pod()), s),
{
    assert forall |s| k8s_attach_vol_to_pod_pre()(s)
    implies state_pred_call(enabled(k8s_attach_vol_to_pod()), s) by {
        let witness_s_prime = CState {
            vol_attached: true,
            ..s
        };
        assert(action_pred_call(k8s_attach_vol_to_pod(), s, witness_s_prime));
    };
}

}
