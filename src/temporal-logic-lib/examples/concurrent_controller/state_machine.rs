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

pub open spec fn init(s: CState) -> bool {
    &&& s.resources === Map::empty()
    &&& s.messages === Set::empty()
    &&& !s.vol_attached
}

pub open spec fn cr_exists_and_create_sts_not_sent(s: CState) -> bool {
    &&& resource_exists(s, new_strlit("my_cr")@)
    &&& !message_sent(s, Message::CreateStatefulSet{replica: 1})
}

pub open spec fn cr_exists_and_create_vol_not_sent(s: CState) -> bool {
    &&& resource_exists(s, new_strlit("my_cr")@)
    &&& !message_sent(s, Message::CreateVolume{id: 1})
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

pub open spec fn pod1_exists_and_vol1_exists(s: CState) -> bool {
    &&& resource_exists(s, new_strlit("my_pod1")@)
    &&& resource_exists(s, new_strlit("my_volume1")@)
}

pub open spec fn send_create_cr() -> ActionPred<CState> {
    |a: Action<CState>| {
        &&& init(a.state)
        &&& a.state_prime === CState {
            messages: a.state.messages.insert(Message::CreateCR),
            ..a.state
        }
    }
}

pub open spec fn send_create_sts() -> ActionPred<CState> {
    |a: Action<CState>| {
        &&& cr_exists_and_create_sts_not_sent(a.state)
        &&& a.state_prime === CState {
            messages: a.state.messages.insert(Message::CreateStatefulSet{replica: 1}),
            ..a.state
        }
    }
}

pub open spec fn send_create_vol() -> ActionPred<CState> {
    |a: Action<CState>| {
        &&& cr_exists_and_create_vol_not_sent(a.state)
        &&& a.state_prime === CState {
            messages: a.state.messages.insert(Message::CreateVolume{id: 1}),
            ..a.state
        }
    }
}

// TODO: k8s_handle_create should not be hardcoded to my_xxx
pub open spec fn k8s_handle_create(msg: Message) -> ActionPred<CState> {
    |a: Action<CState>| {
        &&& message_sent(a.state, msg)
        &&& match msg {
            Message::CreateCR => resources_updated_with(a.state, a.state_prime, new_strlit("my_cr")@, Resource::CustomResource),
            Message::CreateStatefulSet{..} => resources_updated_with(a.state, a.state_prime, new_strlit("my_statefulset")@, Resource::StatefulSet),
            Message::CreateVolume{..} => resources_updated_with(a.state, a.state_prime, new_strlit("my_volume1")@, Resource::Volume{attached: false}),
        }
    }
}

pub open spec fn k8s_create_pod() -> ActionPred<CState> {
    |a: Action<CState>| {
        &&& resource_exists(a.state, new_strlit("my_statefulset")@)
        &&& a.state_prime === CState {
            resources: a.state.resources.insert(new_strlit("my_pod1")@, Resource::Pod),
            ..a.state
        }
    }
}

pub open spec fn k8s_attach_vol_to_pod() -> ActionPred<CState> {
    |a: Action<CState>| {
        &&& pod1_exists_and_vol1_exists(a.state)
        &&& a.state_prime === CState {
            vol_attached: true,
            ..a.state
        }
    }
}

pub open spec fn stutter() -> ActionPred<CState> {
    |a: Action<CState>| a.state === a.state_prime
}

pub open spec fn next() -> ActionPred<CState> {
    |a: Action<CState>| {
        ||| closure_call(send_create_cr(), a)
        ||| closure_call(send_create_sts(), a)
        ||| closure_call(send_create_vol(), a)
        ||| exists |msg| closure_call(#[trigger] k8s_handle_create(msg), a)
        ||| closure_call(k8s_create_pod(), a)
        ||| closure_call(k8s_attach_vol_to_pod(), a)
        ||| closure_call(stutter(), a)
    }
}

pub open spec fn sm_spec() -> TempPred<CState> {
    lift_state(|state| init(state))
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
        forall |s| closure_call(|state| init(state), s)
            ==> closure_call(enabled(send_create_cr()), s),
{
    assert forall |s| closure_call(|state| init(state), s)
    implies closure_call(enabled(send_create_cr()), s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                messages: s.messages.insert(Message::CreateCR),
                ..s
            }
        };
        assert(closure_call(send_create_cr(), witness_action));
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
        forall |s| closure_call(|state| cr_exists_and_create_sts_not_sent(state), s)
            ==> closure_call(enabled(send_create_sts()), s),
{
    assert forall |s| closure_call(|state| cr_exists_and_create_sts_not_sent(state), s)
    implies closure_call(enabled(send_create_sts()), s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                messages: s.messages.insert(Message::CreateStatefulSet{replica: 1}),
                ..s
            }
        };
        assert(closure_call(send_create_sts(), witness_action));
    };
}

pub proof fn send_create_vol_enabled()
    ensures
        forall |s| closure_call(|state| cr_exists_and_create_vol_not_sent(state), s)
            ==> closure_call(enabled(send_create_vol()), s),
{
    assert forall |s| closure_call(|state| cr_exists_and_create_vol_not_sent(state), s)
    implies closure_call(enabled(send_create_vol()), s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                messages: s.messages.insert(Message::CreateVolume{id: 1}),
                ..s
            }
        };
        assert(closure_call(send_create_vol(), witness_action));
    };
}

pub open spec fn k8s_handle_create_witness_action(state: CState, key: Seq<char>, val: Resource) -> Action<CState> {
    if state.resources.dom().contains(key) {
        Action {
            state: state,
            state_prime: state,
        }
    } else {
        Action {
            state: state,
            state_prime: CState {
                resources: state.resources.insert(key, val),
                ..state
            },
        }
    }
}

pub open spec fn k8s_handle_create_pre(msg: Message) -> StatePred<CState> {
    |state| message_sent(state, msg)
}

pub proof fn k8s_handle_create_enabled(msg: Message)
    ensures
        forall |state| closure_call(k8s_handle_create_pre(msg), state)
            ==> #[trigger] closure_call(enabled(k8s_handle_create(msg)), state),
{
    assert forall |state| closure_call(k8s_handle_create_pre(msg), state)
    implies #[trigger] closure_call(enabled(k8s_handle_create(msg)), state) by {
        match msg {
            Message::CreateCR => {
                let witness_action = k8s_handle_create_witness_action(state, new_strlit("my_cr")@, Resource::CustomResource);
                assert(closure_call(k8s_handle_create(msg), witness_action));
            },
            Message::CreateStatefulSet{..} => {
                let witness_action = k8s_handle_create_witness_action(state, new_strlit("my_statefulset")@, Resource::StatefulSet);
                assert(closure_call(k8s_handle_create(msg), witness_action));
            },
            Message::CreateVolume{..} => {
                let witness_action = k8s_handle_create_witness_action(state, new_strlit("my_volume1")@, Resource::Volume{attached: false});
                assert(closure_call(k8s_handle_create(msg), witness_action));
            },
        }
    };
}

pub proof fn k8s_create_pod_enabled()
    ensures
        forall |s| closure_call(|state| resource_exists(state, new_strlit("my_statefulset")@), s)
            ==> closure_call(enabled(k8s_create_pod()), s),
{
    assert forall |s| closure_call(|state| resource_exists(state, new_strlit("my_statefulset")@), s)
    implies closure_call(enabled(k8s_create_pod()), s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                resources: s.resources.insert(new_strlit("my_pod1")@, Resource::Pod),
                ..s
            }
        };
        assert(closure_call(k8s_create_pod(), witness_action));
    };
}

pub proof fn k8s_attach_vol_to_pod_enabled()
    ensures
        forall |s| closure_call(|state| pod1_exists_and_vol1_exists(state), s)
            ==> closure_call(enabled(k8s_attach_vol_to_pod()), s),
{
    assert forall |s| closure_call(|state| pod1_exists_and_vol1_exists(state), s)
    implies closure_call(enabled(k8s_attach_vol_to_pod()), s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                vol_attached: true,
                ..s
            }
        };
        assert(closure_call(k8s_attach_vol_to_pod(), witness_action));
    };
}

}
