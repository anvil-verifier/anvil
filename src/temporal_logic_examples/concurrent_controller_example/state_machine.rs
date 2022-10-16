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

pub enum Message {
    CreateCR,
    CreateStatefulSet{replica: nat},
    CreateVolume{id: nat},
}

pub struct Resource {}

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

pub open spec fn send_create_cr_pre(s: CState) -> bool {
    &&& s.resources === Map::empty()
    &&& s.messages === Set::empty()
    &&& !s.vol_attached
}


pub open spec fn send_create_cr(s: CState, s_prime: CState) -> bool {
    &&& send_create_cr_pre(s)
    &&& s_prime === CState {
        messages: s.messages.insert(Message::CreateCR),
        ..s
    }
}

pub open spec fn send_create_sts_pre(s: CState) -> bool {
    &&& s.resources.dom().contains(new_strlit("my_cr")@)
    &&& !s.resources.dom().contains(new_strlit("my_statefulset")@)
    &&& !s.messages.contains(Message::CreateStatefulSet{replica: 1})
}

pub open spec fn send_create_sts(s: CState, s_prime: CState) -> bool {
    &&& send_create_sts_pre(s)
    &&& s_prime === CState {
        messages: s.messages.insert(Message::CreateStatefulSet{replica: 1}),
        ..s
    }
}

pub open spec fn send_create_vol_pre(s: CState) -> bool {
    &&& s.resources.dom().contains(new_strlit("my_cr")@)
    &&& !s.resources.dom().contains(new_strlit("my_volume1")@)
    &&& !s.messages.contains(Message::CreateVolume{id: 1})
}

pub open spec fn send_create_vol(s: CState, s_prime: CState) -> bool {
    &&& send_create_vol_pre(s)
    &&& s_prime === CState {
        messages: s.messages.insert(Message::CreateVolume{id: 1}),
        ..s
    }
}

pub open spec fn k8s_create_cr_pre(s: CState) -> bool {
    s.messages.contains(Message::CreateCR)
}

pub open spec fn k8s_create_cr(s: CState, s_prime: CState) -> bool {
    &&& k8s_create_cr_pre(s)
    &&& s_prime === CState {
        resources: s.resources.insert(new_strlit("my_cr")@, Resource{}),
        ..s
    }
}

pub open spec fn k8s_create_sts_pre(s: CState) -> bool {
    s.messages.contains(Message::CreateStatefulSet{replica: 1})
}

pub open spec fn k8s_create_sts(s: CState, s_prime: CState) -> bool {
    &&& k8s_create_sts_pre(s)
    &&& s_prime === CState {
        resources: s.resources.insert(new_strlit("my_statefulset")@, Resource{}),
        ..s
    }
}

pub open spec fn k8s_create_vol_pre(s: CState) -> bool {
    s.messages.contains(Message::CreateVolume{id: 1})
}

pub open spec fn k8s_create_vol(s: CState, s_prime: CState) -> bool {
    &&& k8s_create_vol_pre(s)
    &&& s_prime === CState {
        resources: s.resources.insert(new_strlit("my_volume1")@, Resource{}),
        ..s
    }
}

pub open spec fn k8s_create_pod_pre(s: CState) -> bool {
    s.resources.dom().contains(new_strlit("my_statefulset")@)
}

pub open spec fn k8s_create_pod(s: CState, s_prime: CState) -> bool {
    &&& k8s_create_pod_pre(s)
    &&& s_prime === CState {
        resources: s.resources.insert(new_strlit("my_pod1")@, Resource{}),
        ..s
    }
}

pub open spec fn k8s_attach_vol_to_pod_pre(s: CState) -> bool {
    &&& s.resources.dom().contains(new_strlit("my_pod1")@)
    &&& s.resources.dom().contains(new_strlit("my_volume1")@)
}

pub open spec fn k8s_attach_vol_to_pod(s: CState, s_prime: CState) -> bool {
    &&& k8s_attach_vol_to_pod_pre(s)
    &&& s_prime === CState {
        vol_attached: true,
        ..s
    }
}

// pub open spec fn reconcile(s: CState, s_prime: CState) -> bool {
//     ||| send_create_cr(s, s_prime)
//     ||| send_create_sts(s, s_prime)
//     ||| send_create_vol(s, s_prime)
// }

pub open spec fn stutter(s: CState, s_prime: CState) -> bool {
    s === s_prime
}

pub open spec fn next(s: CState, s_prime: CState) -> bool {
    ||| send_create_cr(s, s_prime)
    ||| send_create_sts(s, s_prime)
    ||| send_create_vol(s, s_prime)
    ||| k8s_create_cr(s, s_prime)
    ||| k8s_create_sts(s, s_prime)
    ||| k8s_create_vol(s, s_prime)
    ||| k8s_create_pod(s, s_prime)
    ||| k8s_attach_vol_to_pod(s, s_prime)
    ||| stutter(s, s_prime)
}

pub open spec fn send_create_cr_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| send_create_cr_pre(state))
}

pub open spec fn send_create_sts_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| send_create_sts_pre(state))
}

pub open spec fn send_create_vol_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| send_create_vol_pre(state))
}

pub open spec fn k8s_create_cr_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| k8s_create_cr_pre(state))
}

pub open spec fn k8s_create_sts_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| k8s_create_sts_pre(state))
}

pub open spec fn k8s_create_vol_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| k8s_create_vol_pre(state))
}

pub open spec fn k8s_create_pod_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| k8s_create_pod_pre(state))
}

pub open spec fn k8s_attach_vol_to_pod_pre_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| k8s_attach_vol_to_pod_pre(state))
}

pub open spec fn send_create_cr_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| send_create_cr(action.state, action.state_prime))
}

pub open spec fn send_create_sts_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| send_create_sts(action.state, action.state_prime))
}

pub open spec fn send_create_vol_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| send_create_vol(action.state, action.state_prime))
}

pub open spec fn k8s_create_cr_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| k8s_create_cr(action.state, action.state_prime))
}

pub open spec fn k8s_create_sts_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| k8s_create_sts(action.state, action.state_prime))
}

pub open spec fn k8s_create_vol_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| k8s_create_vol(action.state, action.state_prime))
}

pub open spec fn k8s_create_pod_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| k8s_create_pod(action.state, action.state_prime))
}

pub open spec fn k8s_attach_vol_to_pod_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| k8s_attach_vol_to_pod(action.state, action.state_prime))
}

pub open spec fn init_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| init(state))
}

// pub open spec fn reconcile_action_pred() -> ActionPred<CState> {
//     ActionPred::new(|action: Action<CState>| reconcile(action.state, action.state_prime))
// }

pub open spec fn next_action_pred() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| next(action.state, action.state_prime))
}

pub open spec fn sm_spec() -> TempPred<CState> {
    init_state_pred().lift()
    .and(always(next_action_pred().lift())
    .and(weak_fairness(send_create_cr_action_pred()).and(weak_fairness(send_create_sts_action_pred())
    .and(weak_fairness(send_create_vol_action_pred()).and(weak_fairness(k8s_create_cr_action_pred())
    .and(weak_fairness(k8s_create_sts_action_pred()).and(weak_fairness(k8s_create_vol_action_pred())
    .and(weak_fairness(k8s_create_pod_action_pred()).and(weak_fairness(k8s_attach_vol_to_pod_action_pred()))))))))))
}

pub proof fn send_create_cr_enabled()
    ensures forall |s: CState| send_create_cr_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(send_create_cr_action_pred()).satisfied_by(s)
{
    assert forall |s: CState| send_create_cr_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(send_create_cr_action_pred()).satisfied_by(s) by {
        if send_create_cr_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    messages: s.messages.insert(Message::CreateCR),
                    ..s
                }
            };
            assert(send_create_cr_action_pred().satisfied_by(witness_action));
        }
    };
}

/// Typically there is not need to prove the following lemma,
/// but Verus does not really know whether two strlit are the same or not.
/// Unfortunately we have to reveal the strlit to convince Verus that they do not equal each other.
/// Is there a better way to do so?
pub proof fn send_create_sts_pre_and_next_implies_pre_or_post()
    ensures
        forall |a: Action<CState>| send_create_sts_pre_state_pred().satisfied_by(a.state) && #[trigger] next_action_pred().satisfied_by(a)
            ==> send_create_sts_pre_state_pred().satisfied_by(a.state_prime) || k8s_create_sts_pre_state_pred().satisfied_by(a.state_prime),
{
    assert forall |a: Action<CState>| send_create_sts_pre_state_pred().satisfied_by(a.state) && #[trigger] next_action_pred().satisfied_by(a)
    implies send_create_sts_pre_state_pred().satisfied_by(a.state_prime) || k8s_create_sts_pre_state_pred().satisfied_by(a.state_prime) by {
        reveal_strlit("my_volume1");
        reveal_strlit("my_statefulset");
        assert(!new_strlit("my_statefulset")@.ext_equal(new_strlit("my_volume1")@));
        assert(new_strlit("my_statefulset")@ !== new_strlit("my_volume1")@);
    };
}

pub proof fn send_create_sts_enabled()
    ensures
        forall |s: CState| send_create_sts_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(send_create_sts_action_pred()).satisfied_by(s),
{
    assert forall |s: CState| send_create_sts_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(send_create_sts_action_pred()).satisfied_by(s) by {
        if send_create_sts_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    messages: s.messages.insert(Message::CreateStatefulSet{replica: 1}),
                    ..s
                }
            };
            assert(send_create_sts_action_pred().satisfied_by(witness_action));
        }
    };
}

pub proof fn send_create_vol_pre_and_next_implies_pre_or_post()
    ensures
        forall |a: Action<CState>| send_create_vol_pre_state_pred().satisfied_by(a.state) && #[trigger] next_action_pred().satisfied_by(a)
            ==> send_create_vol_pre_state_pred().satisfied_by(a.state_prime) || k8s_create_vol_pre_state_pred().satisfied_by(a.state_prime),
{
    assert forall |a: Action<CState>| send_create_vol_pre_state_pred().satisfied_by(a.state) && #[trigger] next_action_pred().satisfied_by(a)
    implies send_create_vol_pre_state_pred().satisfied_by(a.state_prime) || k8s_create_vol_pre_state_pred().satisfied_by(a.state_prime) by {
        reveal_strlit("my_volume1");
        reveal_strlit("my_statefulset");
        reveal_strlit("my_pod1");
        assert(!new_strlit("my_volume1")@.ext_equal(new_strlit("my_statefulset")@));
        assert(!new_strlit("my_volume1")@.ext_equal(new_strlit("my_pod1")@));
        assert(new_strlit("my_volume1")@ !== new_strlit("my_statefulset")@);
        assert(new_strlit("my_volume1")@ !== new_strlit("my_pod1")@);
    };
}

pub proof fn send_create_vol_enabled()
    ensures forall |s: CState| send_create_vol_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(send_create_vol_action_pred()).satisfied_by(s)
{
    assert forall |s: CState| send_create_vol_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(send_create_vol_action_pred()).satisfied_by(s) by {
        if send_create_vol_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    messages: s.messages.insert(Message::CreateVolume{id: 1}),
                    ..s
                }
            };
            assert(send_create_vol_action_pred().satisfied_by(witness_action));
        }
    };
}

pub proof fn k8s_create_cr_enabled()
    ensures forall |s: CState| k8s_create_cr_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(k8s_create_cr_action_pred()).satisfied_by(s)
{
    assert forall |s: CState| k8s_create_cr_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(k8s_create_cr_action_pred()).satisfied_by(s) by {
        if k8s_create_cr_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    resources: s.resources.insert(new_strlit("my_cr")@, Resource{}),
                    ..s
                }
            };
            assert(k8s_create_cr_action_pred().satisfied_by(witness_action));
        }
    };
}

pub proof fn k8s_create_sts_enabled()
    ensures forall |s: CState| k8s_create_sts_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(k8s_create_sts_action_pred()).satisfied_by(s)
{
    assert forall |s: CState| k8s_create_sts_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(k8s_create_sts_action_pred()).satisfied_by(s) by {
        if k8s_create_sts_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    resources: s.resources.insert(new_strlit("my_statefulset")@, Resource{}),
                    ..s
                }
            };
            assert(k8s_create_sts_action_pred().satisfied_by(witness_action));
        }
    };
}

pub proof fn k8s_create_vol_enabled()
    ensures forall |s: CState| k8s_create_vol_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(k8s_create_vol_action_pred()).satisfied_by(s)
{
    assert forall |s: CState| k8s_create_vol_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(k8s_create_vol_action_pred()).satisfied_by(s) by {
        if k8s_create_vol_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    resources: s.resources.insert(new_strlit("my_volume1")@, Resource{}),
                    ..s
                }
            };
            assert(k8s_create_vol_action_pred().satisfied_by(witness_action));
        }
    };
}

pub proof fn k8s_create_pod_enabled()
    ensures forall |s: CState| k8s_create_pod_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(k8s_create_pod_action_pred()).satisfied_by(s)
{
    assert forall |s: CState| k8s_create_pod_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(k8s_create_pod_action_pred()).satisfied_by(s) by {
        if k8s_create_pod_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    resources: s.resources.insert(new_strlit("my_pod1")@, Resource{}),
                    ..s
                }
            };
            assert(k8s_create_pod_action_pred().satisfied_by(witness_action));
        }
    };
}

pub proof fn k8s_attach_vol_to_pod_enabled()
    ensures forall |s: CState| k8s_attach_vol_to_pod_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(k8s_attach_vol_to_pod_action_pred()).satisfied_by(s)
{
    assert forall |s: CState| k8s_attach_vol_to_pod_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(k8s_attach_vol_to_pod_action_pred()).satisfied_by(s) by {
        if k8s_attach_vol_to_pod_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    vol_attached: true,
                    ..s
                }
            };
            assert(k8s_attach_vol_to_pod_action_pred().satisfied_by(witness_action));
        }
    };
}

}
