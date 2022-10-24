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
pub enum Resource {
    CustomResource,
    StatefulSet,
    Pod,
    Volume{attached: bool},
}

#[is_variant]
pub enum Message {
    CreateCR{
        name: Seq<char>,
        obj: Resource,
    },
    CreateStatefulSet{
        name: Seq<char>,
        obj: Resource,
    },
    CreateVolume{
        name: Seq<char>,
        obj: Resource,
    },
    CreatePod{
        name: Seq<char>,
        obj: Resource,
    }
}

impl Message {
    pub open spec fn name(self) -> Seq<char> {
        match self {
            Message::CreateCR{name, ..} => name,
            Message::CreateStatefulSet{name, ..} => name,
            Message::CreateVolume{name, ..} => name,
            Message::CreatePod{name, ..} => name,
        }
    }

    pub open spec fn obj(self) -> Resource {
        match self {
            Message::CreateCR{name, obj} => obj,
            Message::CreateStatefulSet{name, obj} => obj,
            Message::CreateVolume{name, obj} => obj,
            Message::CreatePod{name, obj} => obj,
        }
    }
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
 *              k8s_handle_create(cr)
 *                 /           \
 *  send_create_sts             send_create_vol
 *                |             |
 * k8s_handle_create(sts)       k8s_handle_create(vol)
 *                |             |
 *   k8s_create_pod             |
 *                \             /
 *                 \           /
 *             k8s_attach_vol_to_pod
 *
 *
 */

pub open spec fn message_sent(s: CState, m: Message) -> bool {
    s.messages.contains(m)
}

pub open spec fn resource_exists(s: CState, key: Seq<char>) -> bool {
    s.resources.dom().contains(key)
}


pub open spec fn create_cr_msg(name: Seq<char>) -> Message {
    Message::CreateCR{
        name: name,
        obj: Resource::CustomResource,
    }
}

pub open spec fn create_sts_msg(name: Seq<char>) -> Message {
    Message::CreateStatefulSet{
        name: name,
        obj: Resource::StatefulSet,
    }
}

pub open spec fn create_pod_msg(name: Seq<char>) -> Message {
    Message::CreatePod{
        name: name,
        obj: Resource::Pod,
    }
}

pub open spec fn create_vol_msg(name: Seq<char>) -> Message {
    Message::CreateVolume{
        name: new_strlit("my_volume1")@,
        obj: Resource::Volume{
            attached: false,
        },
    }
}

pub open spec fn update_resources_with(s: CState, msg: Message) -> Map<Seq<char>, Resource> {
    if s.resources.dom().contains(msg.name()) {
        s.resources
    } else {
        s.resources.insert(msg.name(), msg.obj())
    }
}

pub open spec fn update_messages_with(s: CState, msg: Message) -> Set<Message> {
    if msg.is_CreateStatefulSet() {
        s.messages.insert(create_pod_msg(msg.name() + new_strlit("_pod1")@))
    } else {
        s.messages
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
            messages: s.messages.insert(create_cr_msg(new_strlit("my_cr")@)),
            ..s
        }
    }
}

pub open spec fn send_create_sts_pre() -> StatePred<CState> {
    |s| {
        &&& resource_exists(s, new_strlit("my_cr")@)
        &&& !message_sent(s, create_sts_msg(new_strlit("my_statefulset")@))
    }
}

pub open spec fn send_create_sts() -> ActionPred<CState> {
    |s, s_prime| {
        &&& send_create_sts_pre()(s)
        &&& s_prime === CState {
            messages: s.messages.insert(create_sts_msg(new_strlit("my_statefulset")@)),
            ..s
        }
    }
}

pub open spec fn send_create_vol_pre() -> StatePred<CState> {
    |s| {
        &&& resource_exists(s, new_strlit("my_cr")@)
        &&& !message_sent(s, create_vol_msg(new_strlit("my_volume1")@))
    }
}

pub open spec fn send_create_vol() -> ActionPred<CState> {
    |s, s_prime| {
        &&& send_create_vol_pre()(s)
        &&& s_prime === CState {
            messages: s.messages.insert(create_vol_msg(new_strlit("my_volume1")@)),
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
        &&& s_prime === CState {
            resources: update_resources_with(s, msg),
            messages: update_messages_with(s, msg),
            ..s
        }
    }
}

pub open spec fn k8s_attach_vol_to_pod_pre() -> StatePred<CState> {
    |s| {
        &&& resource_exists(s, new_strlit("my_statefulset_pod1")@)
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
    .and(weak_fairness(k8s_attach_vol_to_pod()))
}

pub proof fn send_create_cr_enabled()
    ensures
        forall |s| state_pred_call(init(), s)
            ==> enabled(send_create_cr())(s),
{
    assert forall |s| state_pred_call(init(), s)
    implies enabled(send_create_cr())(s) by {
        let witness_s_prime = CState {
            messages: s.messages.insert(create_cr_msg(new_strlit("my_cr")@)),
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
        forall |s| state_pred_call(send_create_sts_pre(), s)
            ==> enabled(send_create_sts())(s),
{
    assert forall |s| state_pred_call(send_create_sts_pre(), s)
    implies enabled(send_create_sts())(s) by {
        let witness_s_prime = CState {
            messages: s.messages.insert(create_sts_msg(new_strlit("my_statefulset")@)),
            ..s
        };
        assert(action_pred_call(send_create_sts(), s, witness_s_prime));
    };
}

pub proof fn send_create_vol_enabled()
    ensures
        forall |s| state_pred_call(send_create_vol_pre(), s)
            ==> enabled(send_create_vol())(s),
{
    assert forall |s| state_pred_call(send_create_vol_pre(), s)
    implies enabled(send_create_vol())(s) by {
        let witness_s_prime = CState {
            messages: s.messages.insert(create_vol_msg(new_strlit("my_volume1")@)),
            ..s
        };
        assert(action_pred_call(send_create_vol(), s, witness_s_prime));
    };
}

pub proof fn k8s_handle_create_enabled(msg: Message)
    ensures
        forall |s| state_pred_call(k8s_handle_create_pre(msg), s)
            ==> enabled(k8s_handle_create(msg))(s),
{
    assert forall |s| state_pred_call(k8s_handle_create_pre(msg), s)
    implies enabled(k8s_handle_create(msg))(s) by {
        let witness_s_prime = CState {
            resources: update_resources_with(s, msg),
            messages: update_messages_with(s, msg),
            ..s
        };
        assert(action_pred_call(k8s_handle_create(msg), s, witness_s_prime));
    };
}

pub proof fn k8s_attach_vol_to_pod_enabled()
    ensures
        forall |s| state_pred_call(k8s_attach_vol_to_pod_pre(), s)
            ==> enabled(k8s_attach_vol_to_pod())(s),
{
    assert forall |s| state_pred_call(k8s_attach_vol_to_pod_pre(), s)
    implies enabled(k8s_attach_vol_to_pod())(s) by {
        let witness_s_prime = CState {
            vol_attached: true,
            ..s
        };
        assert(action_pred_call(k8s_attach_vol_to_pod(), s, witness_s_prime));
    };
}

}
