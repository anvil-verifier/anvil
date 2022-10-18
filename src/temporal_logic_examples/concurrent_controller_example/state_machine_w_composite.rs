// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::concurrent_controller_example::state_machine::*;
use crate::pervasive::map::*;
use crate::pervasive::seq::*;
use crate::pervasive::set::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

// The pre is fairly simple: just make sure the message is sent
pub open spec fn sm_k8s_handle_create_pre(s: CState, m: Message) -> bool {
    &&& s.messages.contains(m)
    // We don't even need the this line since the message has only three types
    // &&& m.is_CreateCR() || m.is_CreateStatefulSet() || m.is_CreateVolume()
}

// This sm_k8s_handle_create should replace sm_k8s_create_(cr|sts|vol) in state_machine.rs
// Note that sm_k8s_create_pod is a bit different so it is not included yet
// TODO: sm_k8s_handle_create should not be hardcoded to my_xxx
pub open spec fn sm_k8s_handle_create(s: CState, s_prime: CState, m: Message) -> bool {
    &&& sm_k8s_handle_create_pre(s, m)
    &&& match m {
        Message::CreateCR => {
            if s.resources.dom().contains(new_strlit("my_cr")@) {
                s_prime === s
            } else {
                s_prime === CState {
                    resources: s.resources.insert(new_strlit("my_cr")@, Resource::CustomResource),
                    ..s
                }
            }
        },
        Message::CreateStatefulSet{..} => {
            if s.resources.dom().contains(new_strlit("my_statefulset")@) {
                s_prime === s
            } else {
                s_prime === CState {
                    resources: s.resources.insert(new_strlit("my_statefulset")@, Resource::StatefulSet),
                    ..s
                }
            }
        },
        Message::CreateVolume{..} => {
            if s.resources.dom().contains(new_strlit("my_volume1")@) {
                s_prime === s
            } else {
                s_prime === CState {
                    resources: s.resources.insert(new_strlit("my_volume1")@, Resource::Volume{attached: false}),
                    ..s
                }
            }
        },
    }
}

pub open spec fn sm_k8s_handle_create_post(s_prime: CState, m: Message) -> bool {
    match m {
        Message::CreateCR => s_prime.resources.dom().contains(new_strlit("my_cr")@),
        Message::CreateStatefulSet{..} => s_prime.resources.dom().contains(new_strlit("my_statefulset")@),
        Message::CreateVolume{..} => s_prime.resources.dom().contains(new_strlit("my_volume1")@),
    }
}

pub open spec fn k8s_handle_create_pre_unquantified() -> UnquantifiedStatePred<CState, Message> {
    UnquantifiedStatePred::new(|state: CState, message: Message| sm_k8s_handle_create_pre(state, message))
}

pub open spec fn k8s_handle_create_unquantified() -> UnquantifiedActionPred<CState, Message> {
    UnquantifiedActionPred::new(|action: Action<CState>, message: Message| sm_k8s_handle_create(action.state, action.state_prime, message))
}

pub open spec fn k8s_handle_create_post_unquantified() -> UnquantifiedStatePred<CState, Message> {
    UnquantifiedStatePred::new(|state_prime: CState, message: Message| sm_k8s_handle_create_post(state_prime, message))
}

pub open spec fn k8s_handle_create_pre() -> StatePred<CState> {
    k8s_handle_create_pre_unquantified().existentially_quantified()
}

pub open spec fn k8s_handle_create() -> ActionPred<CState> {
    k8s_handle_create_unquantified().existentially_quantified()
}

pub open spec fn k8s_handle_create_post() -> StatePred<CState> {
    k8s_handle_create_post_unquantified().existentially_quantified()
}

pub open spec fn create_cr_msg() -> Message {
    Message::CreateCR
}

pub open spec fn create_sts_msg() -> Message {
    Message::CreateStatefulSet{replica: 1}
}

pub open spec fn create_vol_msg() -> Message {
    Message::CreateVolume{id: 1}
}

pub open spec fn k8s_handle_create_pre_concretized(m: Message) -> StatePred<CState> {
    k8s_handle_create_pre_unquantified().quantified_by(m)
}

pub open spec fn k8s_handle_create_concretized(m: Message) -> ActionPred<CState> {
    k8s_handle_create_unquantified().quantified_by(m)
}

pub open spec fn k8s_handle_create_post_concretized(m: Message) -> StatePred<CState> {
    k8s_handle_create_post_unquantified().quantified_by(m)
}

pub open spec fn sm_next_with_composite(s: CState, s_prime: CState) -> bool {
    ||| sm_send_create_cr(s, s_prime)
    ||| sm_send_create_sts(s, s_prime)
    ||| sm_send_create_vol(s, s_prime)
    ||| exists |m: Message| sm_k8s_handle_create(s, s_prime, m)
    ||| sm_k8s_create_pod(s, s_prime)
    ||| sm_k8s_attach_vol_to_pod(s, s_prime)
    ||| sm_stutter(s, s_prime)
}

pub open spec fn next_with_composite() -> ActionPred<CState> {
    ActionPred::new(|action: Action<CState>| sm_next_with_composite(action.state, action.state_prime))
}

pub open spec fn sm_spec_with_composite() -> TempPred<CState> {
    init().lift()
    .and(always(next().lift()))
    .and(weak_fairness(send_create_cr()))
    .and(weak_fairness(send_create_sts()))
    .and(weak_fairness(send_create_vol()))
    .and(weak_fairness(k8s_handle_create()))
    .and(weak_fairness(k8s_create_pod()))
    .and(weak_fairness(k8s_attach_vol_to_pod()))
}

pub proof fn k8s_handle_any_create_msg_pre_and_next_and_forward_implies_post(msg: Message)
    ensures
        forall |action: Action<CState>|
            #[trigger] k8s_handle_create_pre_concretized(msg).satisfied_by(action.state)
            && next_with_composite().satisfied_by(action)
            && k8s_handle_create_concretized(msg).satisfied_by(action)
            ==> k8s_handle_create_post_concretized(msg).satisfied_by(action.state_prime)
{}

pub proof fn k8s_handle_any_create_msg_pre_and_next_implies_pre_and_post(msg: Message)
    ensures
        forall |action: Action<CState>|
            #[trigger] k8s_handle_create_pre_concretized(msg).satisfied_by(action.state)
            && next_with_composite().satisfied_by(action)
            ==> k8s_handle_create_pre_concretized(msg).satisfied_by(action.state_prime)
                || k8s_handle_create_post_concretized(msg).satisfied_by(action.state_prime)
{}

pub proof fn k8s_handle_any_create_msg_pre_implies_enabled(msg: Message)
    ensures
        forall |state: CState| #[trigger] k8s_handle_create_pre_concretized(msg).satisfied_by(state)
            ==> enabled(k8s_handle_create_concretized(msg)).satisfied_by(state),
{
    assert forall |state: CState| #[trigger] k8s_handle_create_pre_concretized(msg).satisfied_by(state)
    implies enabled(k8s_handle_create_concretized(msg)).satisfied_by(state) by {
        match msg {
            Message::CreateCR => {
                if state.resources.dom().contains(new_strlit("my_cr")@) {
                    let witness_action = Action {
                        state: state,
                        state_prime: state,
                    };
                    assert(k8s_handle_create_concretized(msg).satisfied_by(witness_action));
                } else {
                    let witness_action = Action {
                        state: state,
                        state_prime: CState {
                            resources: state.resources.insert(new_strlit("my_cr")@, Resource::CustomResource),
                            ..state
                        },
                    };
                    assert(k8s_handle_create_concretized(msg).satisfied_by(witness_action));
                }
            },
            Message::CreateStatefulSet{..} => {
                if state.resources.dom().contains(new_strlit("my_statefulset")@) {
                    let witness_action = Action {
                        state: state,
                        state_prime: state,
                    };
                    assert(k8s_handle_create_concretized(msg).satisfied_by(witness_action));
                } else {
                    let witness_action = Action {
                        state: state,
                        state_prime: CState {
                            resources: state.resources.insert(new_strlit("my_statefulset")@, Resource::StatefulSet),
                            ..state
                        },
                    };
                    assert(k8s_handle_create_concretized(msg).satisfied_by(witness_action));
                }
            },
            Message::CreateVolume{..} => {
                if state.resources.dom().contains(new_strlit("my_volume1")@) {
                    let witness_action = Action {
                        state: state,
                        state_prime: state,
                    };
                    assert(k8s_handle_create_concretized(msg).satisfied_by(witness_action));
                } else {
                    let witness_action = Action {
                        state: state,
                        state_prime: CState {
                            resources: state.resources.insert(new_strlit("my_volume1")@, Resource::Volume{attached: false}),
                            ..state
                        },
                    };
                    assert(k8s_handle_create_concretized(msg).satisfied_by(witness_action));
                }
            },
        }
    }
}

// Mechanically prove k8s_handle_create is enabled. It is a repeated and tedious process.
pub proof fn k8s_handle_create_enabled()
    ensures
        forall |s: CState| k8s_handle_create_pre().satisfied_by(s) ==> #[trigger] enabled(k8s_handle_create()).satisfied_by(s),
{
    assert forall |s: CState| k8s_handle_create_pre().satisfied_by(s) implies #[trigger] enabled(k8s_handle_create()).satisfied_by(s) by {
        let m = choose(|m: Message| sm_k8s_handle_create_pre(s, m));
        match m {
            Message::CreateCR => {
                if s.resources.dom().contains(new_strlit("my_cr")@) {
                    let witness_action = Action {
                        state: s,
                        state_prime: s,
                    };
                    assert(UnquantifiedActionPred::new(|action: Action<CState>, message: Message| sm_k8s_handle_create(action.state, action.state_prime, message)).satisfied_by(witness_action, m));
                    assert(k8s_handle_create().satisfied_by(witness_action));
                } else {
                    let witness_action = Action {
                        state: s,
                        state_prime: CState {
                            resources: s.resources.insert(new_strlit("my_cr")@, Resource::CustomResource),
                            ..s
                        },
                    };
                    assert(UnquantifiedActionPred::new(|action: Action<CState>, message: Message| sm_k8s_handle_create(action.state, action.state_prime, message)).satisfied_by(witness_action, m));
                    assert(k8s_handle_create().satisfied_by(witness_action));
                }
            },
            Message::CreateStatefulSet{..} => {
                if s.resources.dom().contains(new_strlit("my_statefulset")@) {
                    let witness_action = Action {
                        state: s,
                        state_prime: s,
                    };
                    assert(UnquantifiedActionPred::new(|action: Action<CState>, message: Message| sm_k8s_handle_create(action.state, action.state_prime, message)).satisfied_by(witness_action, m));
                    assert(k8s_handle_create().satisfied_by(witness_action));
                } else {
                    let witness_action = Action {
                        state: s,
                        state_prime: CState {
                            resources: s.resources.insert(new_strlit("my_statefulset")@, Resource::StatefulSet),
                            ..s
                        },
                    };
                    assert(UnquantifiedActionPred::new(|action: Action<CState>, message: Message| sm_k8s_handle_create(action.state, action.state_prime, message)).satisfied_by(witness_action, m));
                    assert(k8s_handle_create().satisfied_by(witness_action));
                }
            },
            Message::CreateVolume{..} => {
                if s.resources.dom().contains(new_strlit("my_volume1")@) {
                    let witness_action = Action {
                        state: s,
                        state_prime: s,
                    };
                    assert(UnquantifiedActionPred::new(|action: Action<CState>, message: Message| sm_k8s_handle_create(action.state, action.state_prime, message)).satisfied_by(witness_action, m));
                    assert(k8s_handle_create().satisfied_by(witness_action));
                } else {
                    let witness_action = Action {
                        state: s,
                        state_prime: CState {
                            resources: s.resources.insert(new_strlit("my_volume1")@, Resource::Volume{attached: false}),
                            ..s
                        }
                    };
                    assert(UnquantifiedActionPred::new(|action: Action<CState>, message: Message| sm_k8s_handle_create(action.state, action.state_prime, message)).satisfied_by(witness_action, m));
                    assert(k8s_handle_create().satisfied_by(witness_action));
                }
            },
        }
    };
}

// The following just tries to prove that if the "CreateStatefulSet" branch is enabled
// the pre get preserved after next() action.
// pub open spec fn sm_k8s_handle_create_sts_pre(s: CState, m: Message) -> bool {
//     &&& s.messages.contains(m)
//     &&& m.is_CreateStatefulSet()
// }

// pub open spec fn k8s_handle_create_sts_pre() -> StatePred<CState> {
//     UnquantifiedStatePred::new(|state: CState, message: Message| {sm_k8s_handle_create_sts_pre(state, message)}).existentially_quantified()
// }

// pub proof fn k8s_handle_create_sts_pre_and_next_implies_pre_or_post()
//     ensures
//         forall |a: Action<CState>| k8s_handle_create_sts_pre().satisfied_by(a.state) && #[trigger] next_with_composite().satisfied_by(a)
//         ==> k8s_handle_create_sts_pre().satisfied_by(a.state_prime) || sts_exists().satisfied_by(a.state_prime),
// {
//     assert forall |a: Action<CState>| k8s_handle_create_sts_pre().satisfied_by(a.state) && #[trigger] next_with_composite().satisfied_by(a)
//     implies k8s_handle_create_sts_pre().satisfied_by(a.state_prime) || sts_exists().satisfied_by(a.state_prime) by {
//         let m = choose(|m: Message| sm_k8s_handle_create_sts_pre(a.state, m));
//         assert(sm_k8s_handle_create_sts_pre(a.state, m));
//         assert(sm_k8s_handle_create_sts_pre(a.state_prime, m));
//         assert(UnquantifiedStatePred::new(|state: CState, message: Message| sm_k8s_handle_create_sts_pre(state, message)).satisfied_by(a.state_prime, m));
//         assert(k8s_handle_create_sts_pre().satisfied_by(a.state_prime));
//     };
// }

}
