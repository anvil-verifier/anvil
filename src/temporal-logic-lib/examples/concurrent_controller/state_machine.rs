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

pub open spec fn init(s: CState) -> bool {
    &&& s.resources === Map::empty()
    &&& s.messages === Set::empty()
    &&& !s.vol_attached
}

pub open spec fn cr_exists_and_not_create_sts_sent(s: CState) -> bool {
    &&& s.resources.dom().contains(new_strlit("my_cr")@)
    &&& !s.messages.contains(Message::CreateStatefulSet{replica: 1})
}

pub open spec fn cr_exists_and_not_create_vol_sent(s: CState) -> bool {
    &&& s.resources.dom().contains(new_strlit("my_cr")@)
    &&& !s.messages.contains(Message::CreateVolume{id: 1})
}

pub open spec fn message_sent(s: CState, m: Message) -> bool {
    s.messages.contains(m)
}

pub open spec fn resources_updated_with(s: CState, s_prime: CState, key: Seq<char>, val: Resource) -> bool {
    if s.resources.dom().contains(key) {
        s_prime === s
    } else {
        s_prime === CState {
            resources: s.resources.insert(key, val),
            ..s
        }
    }
}

pub open spec fn sts_exists(s: CState) -> bool {
    s.resources.dom().contains(new_strlit("my_statefulset")@)
}

pub open spec fn pod1_exists_and_vol1_exists(s: CState) -> bool {
    &&& s.resources.dom().contains(new_strlit("my_pod1")@)
    &&& s.resources.dom().contains(new_strlit("my_volume1")@)
}

pub open spec fn send_create_cr() -> ActionPred<CState> {
    ActionPred::new(|a: Action<CState>| {
        &&& init(a.state)
        &&& a.state_prime === CState {
            messages: a.state.messages.insert(Message::CreateCR),
            ..a.state
        }
    })
}

pub open spec fn send_create_sts() -> ActionPred<CState> {
    ActionPred::new(|a: Action<CState>| {
        &&& cr_exists_and_not_create_sts_sent(a.state)
        &&& a.state_prime === CState {
            messages: a.state.messages.insert(Message::CreateStatefulSet{replica: 1}),
            ..a.state
        }
    })
}

pub open spec fn send_create_vol() -> ActionPred<CState> {
    ActionPred::new(|a: Action<CState>| {
        &&& cr_exists_and_not_create_vol_sent(a.state)
        &&& a.state_prime === CState {
            messages: a.state.messages.insert(Message::CreateVolume{id: 1}),
            ..a.state
        }
    })
}

// TODO: k8s_handle_create should not be hardcoded to my_xxx
pub open spec fn k8s_handle_create(quantified_msg: Message) -> ActionPred<CState> {
    (|msg: Message| ActionPred::new(|a: Action<CState>| {
        &&& message_sent(a.state, msg)
        &&& match msg {
            Message::CreateCR => resources_updated_with(a.state, a.state_prime, new_strlit("my_cr")@, Resource::CustomResource),
            Message::CreateStatefulSet{..} => resources_updated_with(a.state, a.state_prime, new_strlit("my_statefulset")@, Resource::StatefulSet),
            Message::CreateVolume{..} => resources_updated_with(a.state, a.state_prime, new_strlit("my_volume1")@, Resource::Volume{attached: false}),
        }
    }))(quantified_msg)
}

pub open spec fn k8s_create_pod() -> ActionPred<CState> {
    ActionPred::new(|a: Action<CState>| {
        &&& sts_exists(a.state)
        &&& a.state_prime === CState {
            resources: a.state.resources.insert(new_strlit("my_pod1")@, Resource::Pod),
            ..a.state
        }
    })
}

pub open spec fn k8s_attach_vol_to_pod() -> ActionPred<CState> {
    ActionPred::new(|a: Action<CState>| {
        &&& pod1_exists_and_vol1_exists(a.state)
        &&& a.state_prime === CState {
            vol_attached: true,
            ..a.state
        }
    })
}

pub open spec fn stutter() -> ActionPred<CState> {
    ActionPred::new(|a: Action<CState>| a.state === a.state_prime)
}

pub open spec fn next() -> ActionPred<CState> {
    ActionPred::new(|a: Action<CState>| {
        ||| send_create_cr().satisfied_by(a)
        ||| send_create_sts().satisfied_by(a)
        ||| send_create_vol().satisfied_by(a)
        ||| exists |m: Message| (#[trigger] k8s_handle_create(m)).satisfied_by(a)
        ||| k8s_create_pod().satisfied_by(a)
        ||| k8s_attach_vol_to_pod().satisfied_by(a)
        ||| stutter().satisfied_by(a)
    })
}

pub open spec fn sm_spec() -> TempPred<CState> {
    StatePred::new(|state: CState| init(state)).lift()
    .and(always(next().lift()))
    .and(weak_fairness(send_create_cr()))
    .and(weak_fairness(send_create_sts()))
    .and(weak_fairness(send_create_vol()))
    .and(tla_forall(|m: Message| weak_fairness(k8s_handle_create(m))))
    .and(weak_fairness(k8s_create_pod()))
    .and(weak_fairness(k8s_attach_vol_to_pod()))
}

pub proof fn send_create_cr_enabled()
    ensures
        forall |s: CState| StatePred::new(|state: CState| init(state)).satisfied_by(s)
            ==> enabled(send_create_cr()).satisfied_by(s),
{
    assert forall |s: CState| StatePred::new(|state: CState| init(state)).satisfied_by(s)
    implies enabled(send_create_cr()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                messages: s.messages.insert(Message::CreateCR),
                ..s
            }
        };
        assert(send_create_cr().satisfied_by(witness_action));
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
        forall |s: CState| StatePred::new(|state: CState| cr_exists_and_not_create_sts_sent(state)).satisfied_by(s)
            ==> enabled(send_create_sts()).satisfied_by(s),
{
    assert forall |s: CState| StatePred::new(|state: CState| cr_exists_and_not_create_sts_sent(state)).satisfied_by(s)
    implies enabled(send_create_sts()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                messages: s.messages.insert(Message::CreateStatefulSet{replica: 1}),
                ..s
            }
        };
        assert(send_create_sts().satisfied_by(witness_action));
    };
}

pub proof fn send_create_vol_enabled()
    ensures
        forall |s: CState| StatePred::new(|state: CState| cr_exists_and_not_create_vol_sent(state)).satisfied_by(s)
            ==> enabled(send_create_vol()).satisfied_by(s),
{
    assert forall |s: CState| StatePred::new(|state: CState| cr_exists_and_not_create_vol_sent(state)).satisfied_by(s)
    implies enabled(send_create_vol()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                messages: s.messages.insert(Message::CreateVolume{id: 1}),
                ..s
            }
        };
        assert(send_create_vol().satisfied_by(witness_action));
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

pub proof fn k8s_handle_create_enabled(msg: Message)
    ensures
        forall |state: CState| (|message: Message| StatePred::new(|state: CState| message_sent(state, message)))(msg).satisfied_by(state)
            ==> #[trigger] enabled(k8s_handle_create(msg)).satisfied_by(state),
{
    assert forall |state: CState| (|message: Message| StatePred::new(|state: CState| message_sent(state, message)))(msg).satisfied_by(state)
    implies #[trigger] enabled(k8s_handle_create(msg)).satisfied_by(state) by {
        match msg {
            Message::CreateCR => {
                let witness_action = k8s_handle_create_witness_action(state, new_strlit("my_cr")@, Resource::CustomResource);
                assert(k8s_handle_create(msg).satisfied_by(witness_action));
            },
            Message::CreateStatefulSet{..} => {
                let witness_action = k8s_handle_create_witness_action(state, new_strlit("my_statefulset")@, Resource::StatefulSet);
                assert(k8s_handle_create(msg).satisfied_by(witness_action));
            },
            Message::CreateVolume{..} => {
                let witness_action = k8s_handle_create_witness_action(state, new_strlit("my_volume1")@, Resource::Volume{attached: false});
                assert(k8s_handle_create(msg).satisfied_by(witness_action));
            },
        }
    };
}

pub proof fn k8s_create_pod_enabled()
    ensures
        forall |s: CState| StatePred::new(|state: CState| state.resources.dom().contains(new_strlit("my_statefulset")@)).satisfied_by(s)
            ==> enabled(k8s_create_pod()).satisfied_by(s),
{
    assert forall |s: CState| StatePred::new(|state: CState| state.resources.dom().contains(new_strlit("my_statefulset")@)).satisfied_by(s)
    implies enabled(k8s_create_pod()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                resources: s.resources.insert(new_strlit("my_pod1")@, Resource::Pod),
                ..s
            }
        };
        assert(k8s_create_pod().satisfied_by(witness_action));
    };
}

pub proof fn k8s_attach_vol_to_pod_enabled()
    ensures
        forall |s: CState| StatePred::new(|state: CState| pod1_exists_and_vol1_exists(state)).satisfied_by(s)
            ==> enabled(k8s_attach_vol_to_pod()).satisfied_by(s),
{
    assert forall |s: CState| StatePred::new(|state: CState| pod1_exists_and_vol1_exists(state)).satisfied_by(s)
    implies enabled(k8s_attach_vol_to_pod()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                vol_attached: true,
                ..s
            }
        };
        assert(k8s_attach_vol_to_pod().satisfied_by(witness_action));
    };
}

}
