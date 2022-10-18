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

pub open spec fn sm_init(s: CState) -> bool {
    &&& s.resources === Map::empty()
    &&& s.messages === Set::empty()
    &&& !s.vol_attached
}

pub open spec fn sm_send_create_cr_precondition(s: CState) -> bool {
    &&& s.resources === Map::empty()
    &&& s.messages === Set::empty()
    &&& !s.vol_attached
}


pub open spec fn sm_send_create_cr(s: CState, s_prime: CState) -> bool {
    &&& sm_send_create_cr_precondition(s)
    &&& s_prime === CState {
        messages: s.messages.insert(Message::CreateCR),
        ..s
    }
}

pub open spec fn sm_send_create_sts_precondition(s: CState) -> bool {
    &&& s.resources.dom().contains(new_strlit("my_cr")@)
    &&& !s.resources.dom().contains(new_strlit("my_statefulset")@)
    &&& !s.messages.contains(Message::CreateStatefulSet{replica: 1})
}

pub open spec fn sm_send_create_sts(s: CState, s_prime: CState) -> bool {
    &&& sm_send_create_sts_precondition(s)
    &&& s_prime === CState {
        messages: s.messages.insert(Message::CreateStatefulSet{replica: 1}),
        ..s
    }
}

pub open spec fn sm_send_create_vol_precondition(s: CState) -> bool {
    &&& s.resources.dom().contains(new_strlit("my_cr")@)
    &&& !s.resources.dom().contains(new_strlit("my_volume1")@)
    &&& !s.messages.contains(Message::CreateVolume{id: 1})
}

pub open spec fn sm_send_create_vol(s: CState, s_prime: CState) -> bool {
    &&& sm_send_create_vol_precondition(s)
    &&& s_prime === CState {
        messages: s.messages.insert(Message::CreateVolume{id: 1}),
        ..s
    }
}

pub open spec fn sm_k8s_create_cr_precondition(s: CState) -> bool {
    s.messages.contains(Message::CreateCR)
}

pub open spec fn sm_k8s_create_cr(s: CState, s_prime: CState) -> bool {
    &&& sm_k8s_create_cr_precondition(s)
    &&& s_prime === CState {
        resources: s.resources.insert(new_strlit("my_cr")@, Resource::CustomResource),
        ..s
    }
}

// Xudong: This predicate does not have to have a parameter m since it basically
// expects one particular m.
// I make it parameterized on m just to evaluate how we prove the properties when
// there is existential quantifier in the actions.
pub open spec fn sm_k8s_create_sts_precondition(s: CState, m: Message) -> bool {
    &&& s.messages.contains(m)
    &&& m === Message::CreateStatefulSet{replica: 1}
}

pub open spec fn sm_k8s_create_sts(s: CState, s_prime: CState, m: Message) -> bool {
    &&& sm_k8s_create_sts_precondition(s, m)
    &&& s_prime === CState {
        resources: s.resources.insert(new_strlit("my_statefulset")@, Resource::StatefulSet),
        ..s
    }
}

pub open spec fn sm_k8s_create_vol_precondition(s: CState) -> bool {
    s.messages.contains(Message::CreateVolume{id: 1})
}

pub open spec fn sm_k8s_create_vol(s: CState, s_prime: CState) -> bool {
    &&& sm_k8s_create_vol_precondition(s)
    &&& s_prime === CState {
        resources: s.resources.insert(new_strlit("my_volume1")@, Resource::Volume{attached: false}),
        ..s
    }
}

pub open spec fn sm_k8s_create_pod_precondition(s: CState) -> bool {
    s.resources.dom().contains(new_strlit("my_statefulset")@)
}

pub open spec fn sm_k8s_create_pod(s: CState, s_prime: CState) -> bool {
    &&& sm_k8s_create_pod_precondition(s)
    &&& s_prime === CState {
        resources: s.resources.insert(new_strlit("my_pod1")@, Resource::Pod),
        ..s
    }
}

pub open spec fn sm_k8s_attach_vol_to_pod_precondition(s: CState) -> bool {
    &&& s.resources.dom().contains(new_strlit("my_pod1")@)
    &&& s.resources.dom().contains(new_strlit("my_volume1")@)
}

pub open spec fn sm_k8s_attach_vol_to_pod(s: CState, s_prime: CState) -> bool {
    &&& sm_k8s_attach_vol_to_pod_precondition(s)
    &&& s_prime === CState {
        vol_attached: true,
        ..s
    }
}

pub open spec fn sm_stutter(s: CState, s_prime: CState) -> bool {
    s === s_prime
}

pub open spec fn cr_exists() -> StatePred<CState> {
    StatePred::new(|state: CState| state.resources.dom().contains(new_strlit("my_cr")@))
}

pub open spec fn sts_exists() -> StatePred<CState> {
    StatePred::new(|state: CState| state.resources.dom().contains(new_strlit("my_statefulset")@))
}

pub open spec fn pod1_exists() -> StatePred<CState> {
    StatePred::new(|state: CState| state.resources.dom().contains(new_strlit("my_pod1")@))
}

pub open spec fn vol1_exists() -> StatePred<CState> {
    StatePred::new(|state: CState| state.resources.dom().contains(new_strlit("my_volume1")@))
}

pub open spec fn create_cr_sent() -> StatePred<CState> {
    StatePred::new(|state: CState| state.messages.contains(Message::CreateCR))
}

pub open spec fn create_sts_sent() -> StatePred<CState> {
    StatePred::new(|state: CState| state.messages.contains(Message::CreateStatefulSet{replica: 1}))
}

pub open spec fn create_vol_sent() -> StatePred<CState> {
    StatePred::new(|state: CState| state.messages.contains(Message::CreateVolume{id: 1}))
}

pub open spec fn vol_attached() -> StatePred<CState> {
    StatePred::new(|state: CState| state.vol_attached)
}

// Xudong: I would like to replace the following xxx_precondition with the above StatePred.
// But this requires us to implement and, or, not and maybe other operators for StatePred.
// I think we should discuss whether we want to keep everything at the TempPred level or not.
// The current way of mixing all three kinds of predicates makes things difficult.

pub open spec fn send_create_sts_precondition() -> StatePred<CState> {
    StatePred::new(|state: CState| sm_send_create_sts_precondition(state))
}

pub open spec fn send_create_vol_precondition() -> StatePred<CState> {
    StatePred::new(|state: CState| sm_send_create_vol_precondition(state))
}

pub open spec fn k8s_create_sts_precondition() -> StatePred<CState> {
    UnquantifiedStatePred::new(|state: CState, message: Message| sm_k8s_create_sts_precondition(state, message)).existentially_quantified()
}

pub open spec fn k8s_attach_vol_to_pod_precondition() -> StatePred<CState> {
    StatePred::new(|state: CState| sm_k8s_attach_vol_to_pod_precondition(state))
}

pub open spec fn send_create_cr() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| sm_send_create_cr(action.state, action.state_prime))
}

pub open spec fn send_create_sts() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| sm_send_create_sts(action.state, action.state_prime))
}

pub open spec fn send_create_vol() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| sm_send_create_vol(action.state, action.state_prime))
}

pub open spec fn k8s_create_cr() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| sm_k8s_create_cr(action.state, action.state_prime))
}

pub open spec fn k8s_create_sts() -> ActionPred<CState> {
    UnquantifiedActionPred::new(|action: Action<CState>, message: Message| sm_k8s_create_sts(action.state, action.state_prime, message)).existentially_quantified()
}

pub open spec fn k8s_create_vol() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| sm_k8s_create_vol(action.state, action.state_prime))
}

pub open spec fn k8s_create_pod() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| sm_k8s_create_pod(action.state, action.state_prime))
}

pub open spec fn k8s_attach_vol_to_pod() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| sm_k8s_attach_vol_to_pod(action.state, action.state_prime))
}

pub open spec fn stutter() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| sm_stutter(action.state, action.state_prime))
}

pub open spec fn init() -> StatePred<CState> {
    StatePred::new(|state: CState| sm_init(state))
}

pub open spec fn sm_next(s: CState, s_prime: CState) -> bool {
    ||| sm_send_create_cr(s, s_prime)
    ||| sm_send_create_sts(s, s_prime)
    ||| sm_send_create_vol(s, s_prime)
    ||| sm_k8s_create_cr(s, s_prime)
    ||| exists |m: Message| sm_k8s_create_sts(s, s_prime, m)
    ||| sm_k8s_create_vol(s, s_prime)
    ||| sm_k8s_create_pod(s, s_prime)
    ||| sm_k8s_attach_vol_to_pod(s, s_prime)
    ||| sm_stutter(s, s_prime)
}

// Xudong: It might be better to write next() as
//
// send_create_cr().or(send_create_sts())
// .or(send_create_vol()).or(k8s_create_cr())
// .or(k8s_create_sts()).or(k8s_create_vol())
// .or(k8s_create_pod()).or(k8s_attach_vol_to_pod())
// .or(stutter())
//
// But this requires us to implement or for ActionPred, and slows down the verification.

pub open spec fn next() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| sm_next(action.state, action.state_prime))
}

pub open spec fn sm_spec() -> TempPred<CState> {
    init().lift()
    .and(always(next().lift())
    .and(weak_fairness(send_create_cr()).and(weak_fairness(send_create_sts())
    .and(weak_fairness(send_create_vol()).and(weak_fairness(k8s_create_cr())
    .and(weak_fairness(k8s_create_sts()).and(weak_fairness(k8s_create_vol())
    .and(weak_fairness(k8s_create_pod()).and(weak_fairness(k8s_attach_vol_to_pod()))))))))))
}

pub proof fn send_create_cr_enabled()
    ensures forall |s: CState| init().satisfied_by(s) ==> #[trigger] enabled(send_create_cr()).satisfied_by(s)
{
    assert forall |s: CState| init().satisfied_by(s) implies #[trigger] enabled(send_create_cr()).satisfied_by(s) by {
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

/// Typically there is not need to prove the following lemma,
/// but Verus does not really know whether two strlit are the same or not.
/// Unfortunately we have to reveal the strlit to convince Verus that they do not equal each other.
/// Is there a better way to do so?
///
/// TODO: run it with Verus team
pub proof fn send_create_sts_pre_and_next_implies_pre_or_post()
    ensures
        forall |a: Action<CState>| send_create_sts_precondition().satisfied_by(a.state) && #[trigger] next().satisfied_by(a)
            ==> send_create_sts_precondition().satisfied_by(a.state_prime) || create_sts_sent().satisfied_by(a.state_prime),
{
    assert forall |a: Action<CState>| send_create_sts_precondition().satisfied_by(a.state) && #[trigger] next().satisfied_by(a)
    implies send_create_sts_precondition().satisfied_by(a.state_prime) || create_sts_sent().satisfied_by(a.state_prime) by {
        reveal_strlit("my_volume1");
        reveal_strlit("my_statefulset");
        assert(!new_strlit("my_statefulset")@.ext_equal(new_strlit("my_volume1")@));
        assert(new_strlit("my_statefulset")@ !== new_strlit("my_volume1")@);
    };
}

pub proof fn send_create_sts_enabled()
    ensures
        forall |s: CState| send_create_sts_precondition().satisfied_by(s) ==> #[trigger] enabled(send_create_sts()).satisfied_by(s),
{
    assert forall |s: CState| send_create_sts_precondition().satisfied_by(s) implies #[trigger] enabled(send_create_sts()).satisfied_by(s) by {
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

pub proof fn sm_send_create_vol_precondition_and_next_implies_pre_or_post()
    ensures
        forall |a: Action<CState>| send_create_vol_precondition().satisfied_by(a.state) && #[trigger] next().satisfied_by(a)
            ==> send_create_vol_precondition().satisfied_by(a.state_prime) || create_vol_sent().satisfied_by(a.state_prime),
{
    assert forall |a: Action<CState>| send_create_vol_precondition().satisfied_by(a.state) && #[trigger] next().satisfied_by(a)
    implies send_create_vol_precondition().satisfied_by(a.state_prime) || create_vol_sent().satisfied_by(a.state_prime) by {
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
    ensures forall |s: CState| send_create_vol_precondition().satisfied_by(s) ==> #[trigger] enabled(send_create_vol()).satisfied_by(s)
{
    assert forall |s: CState| send_create_vol_precondition().satisfied_by(s) implies #[trigger] enabled(send_create_vol()).satisfied_by(s) by {
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

pub proof fn k8s_create_cr_enabled()
    ensures forall |s: CState| create_cr_sent().satisfied_by(s) ==> #[trigger] enabled(k8s_create_cr()).satisfied_by(s)
{
    assert forall |s: CState| create_cr_sent().satisfied_by(s) implies #[trigger] enabled(k8s_create_cr()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                resources: s.resources.insert(new_strlit("my_cr")@, Resource::CustomResource),
                ..s
            }
        };
        assert(k8s_create_cr().satisfied_by(witness_action));
    };
}

pub proof fn create_sts_sent_implies_sm_k8s_create_sts_precondition()
    ensures forall |s: CState| create_sts_sent().satisfied_by(s) ==> #[trigger] k8s_create_sts_precondition().satisfied_by(s)
{
    assert forall |s: CState| create_sts_sent().satisfied_by(s) implies #[trigger] k8s_create_sts_precondition().satisfied_by(s) by {
        assert(UnquantifiedStatePred::new(|state: CState, message: Message| sm_k8s_create_sts_precondition(state, message)).satisfied_by(s, Message::CreateStatefulSet{replica: 1}));
    };
}

pub proof fn k8s_create_sts_pre_and_next_implies_pre_or_post()
    ensures
        forall |a: Action<CState>| k8s_create_sts_precondition().satisfied_by(a.state) && #[trigger] next().satisfied_by(a)
        ==> k8s_create_sts_precondition().satisfied_by(a.state_prime) || sts_exists().satisfied_by(a.state_prime),
{
    assert forall |a: Action<CState>| k8s_create_sts_precondition().satisfied_by(a.state) && #[trigger] next().satisfied_by(a)
    implies k8s_create_sts_precondition().satisfied_by(a.state_prime) || sts_exists().satisfied_by(a.state_prime) by {
        let m = choose(|m: Message| sm_k8s_create_sts_precondition(a.state, m));
        assert(sm_k8s_create_sts_precondition(a.state, m));
        assert(sm_k8s_create_sts_precondition(a.state_prime, m));
        assert(UnquantifiedStatePred::new(|state: CState, message: Message| sm_k8s_create_sts_precondition(state, message)).satisfied_by(a.state_prime, m));
        assert(k8s_create_sts_precondition().satisfied_by(a.state_prime));
    };
}

pub proof fn k8s_create_sts_enabled()
    ensures forall |s: CState| k8s_create_sts_precondition().satisfied_by(s) ==> #[trigger] enabled(k8s_create_sts()).satisfied_by(s)
{
    assert forall |s: CState| k8s_create_sts_precondition().satisfied_by(s) implies #[trigger] enabled(k8s_create_sts()).satisfied_by(s) by {
        let m = choose(|m: Message| sm_k8s_create_sts_precondition(s, m));
        let witness_action = Action {
            state: s,
            state_prime: CState {
                resources: s.resources.insert(new_strlit("my_statefulset")@, Resource::StatefulSet),
                ..s
            }
        };
        assert(UnquantifiedActionPred::new(|action: Action<CState>, message: Message| sm_k8s_create_sts(action.state, action.state_prime, message)).satisfied_by(witness_action, m));
        assert(k8s_create_sts().satisfied_by(witness_action));
    };
}

pub proof fn k8s_create_vol_enabled()
    ensures forall |s: CState| create_vol_sent().satisfied_by(s) ==> #[trigger] enabled(k8s_create_vol()).satisfied_by(s)
{
    assert forall |s: CState| create_vol_sent().satisfied_by(s) implies #[trigger] enabled(k8s_create_vol()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                resources: s.resources.insert(new_strlit("my_volume1")@, Resource::Volume{attached: false}),
                ..s
            }
        };
        assert(k8s_create_vol().satisfied_by(witness_action));
    };
}

pub proof fn k8s_create_pod_enabled()
    ensures forall |s: CState| sts_exists().satisfied_by(s) ==> #[trigger] enabled(k8s_create_pod()).satisfied_by(s)
{
    assert forall |s: CState| sts_exists().satisfied_by(s) implies #[trigger] enabled(k8s_create_pod()).satisfied_by(s) by {
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
    ensures forall |s: CState| k8s_attach_vol_to_pod_precondition().satisfied_by(s) ==> #[trigger] enabled(k8s_attach_vol_to_pod()).satisfied_by(s)
{
    assert forall |s: CState| k8s_attach_vol_to_pod_precondition().satisfied_by(s) implies #[trigger] enabled(k8s_attach_vol_to_pod()).satisfied_by(s) by {
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
