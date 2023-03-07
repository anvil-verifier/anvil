// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{common::*, controller::common::*, reconciler::*};
use crate::pervasive::{map::*, multiset::*, option::*, seq::*, set::*};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn issue_initial_list<T>(reconciler: Reconciler<T>) -> ControllerAction<T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<T>| {
            &&& input.scheduled_cr_key.is_None()
            &&& input.recv.is_None()
            &&& s.self_watcher.state.is_Empty() // Only issue the initial list at Empty state
            &&& s.self_watcher.pending_req_msg.is_None() // and the initial list is not issued yet
        },
        transition: |input: ControllerActionInput, s: ControllerState<T>| {
            let list_req_msg = controller_req_msg(APIRequest::ListRequest(ListRequest {
                kind: ResourceKind::CustomResourceKind,
            }), s.req_id);
            let s_prime = ControllerState {
                self_watcher: Watcher{
                    pending_req_msg: Option::Some(list_req_msg),
                    ..s.self_watcher
                },
                req_id: s.req_id + 1,
                ..s
            };
            let send = Multiset::singleton(list_req_msg);
            (s_prime, send)
        },
    }
}

pub open spec fn get_key_set_from_list_result(list: Seq<ResourceObj>) -> Set<ResourceKey> {
    // TODO: the returned set should contain all the keys of objects in the list
    Set::empty()
}

pub open spec fn trigger_reconcile_with_list_resp<T>(reconciler: Reconciler<T>) -> ControllerAction<T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<T>| {
            &&& input.scheduled_cr_key.is_None()
            &&& input.recv.is_Some()
            &&& input.recv.get_Some_0().dst == HostId::CustomController
            &&& input.recv.get_Some_0().content.is_list_response()
            &&& s.self_watcher.state.is_Empty() // Only issue the initial list at Empty state
            &&& s.self_watcher.pending_req_msg.is_Some() // and the initial list is already issued
            &&& resp_msg_matches_req_msg(input.recv.get_Some_0(), s.self_watcher.pending_req_msg.get_Some_0()) // and, of course, the resp matches the request
        },
        transition: |input: ControllerActionInput, s: ControllerState<T>| {
            let list_resp = input.recv.get_Some_0().content.get_list_response();
            if list_resp.res.is_Ok() {
                let s_prime = ControllerState {
                    self_watcher: Watcher {
                        state: WatcherState::InitListed,
                        pending_req_msg: Option::None,
                    },
                    scheduled_reconciles: s.scheduled_reconciles + get_key_set_from_list_result(list_resp.res.get_Ok_0()),
                    ..s
                };
                let send = Multiset::empty();
                (s_prime, send)
            } else {
                let s_prime = ControllerState {
                    self_watcher: Watcher {
                        state: WatcherState::Empty,
                        pending_req_msg: Option::None,
                    },
                    ..s
                };
                let send = Multiset::empty();
                (s_prime, send)
            }
        },
    }
}

pub open spec fn start_watching<T>(reconciler: Reconciler<T>) -> ControllerAction<T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<T>| {
            &&& input.scheduled_cr_key.is_None()
            &&& input.recv.is_None()
            &&& s.self_watcher.state.is_InitListed()
        },
        transition: |input: ControllerActionInput, s: ControllerState<T>| {
            let s_prime =  ControllerState {
                self_watcher: Watcher {
                    state: WatcherState::Watching,
                    ..s.self_watcher
                },
                ..s
            };
            // TODO: the controller should send a watch request with the rv returned by the previous list
            let send = Multiset::empty();
            (s_prime, send)
        },
    }
}

// TODO: this trigger_reconcile only considers self_watcher
pub open spec fn trigger_reconcile<T>(reconciler: Reconciler<T>) -> ControllerAction<T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<T>| {
            &&& input.scheduled_cr_key.is_None()
            &&& input.recv.is_Some()
            &&& input.recv.get_Some_0().dst == HostId::CustomController
            &&& input.recv.get_Some_0().content.is_WatchEvent()
            &&& (reconciler.reconcile_trigger)(input.recv.get_Some_0()).is_Some()
            &&& s.self_watcher.state.is_Watching() // Only receive notification at Watching state
        },
        transition: |input: ControllerActionInput, s: ControllerState<T>| {
            let cr_key = (reconciler.reconcile_trigger)(input.recv.get_Some_0()).get_Some_0();
            let s_prime = ControllerState {
                scheduled_reconciles: s.scheduled_reconciles.insert(cr_key),
                ..s
            };
            let send = Multiset::empty();
            (s_prime, send)
        },
    }
}

pub open spec fn run_scheduled_reconcile<T>(reconciler: Reconciler<T>) -> ControllerAction<T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<T>| {
            &&& input.scheduled_cr_key.is_Some()
            &&& s.scheduled_reconciles.contains(input.scheduled_cr_key.get_Some_0())
            &&& input.recv.is_None()
            &&& !s.ongoing_reconciles.dom().contains(input.scheduled_cr_key.get_Some_0())
        },
        transition: |input: ControllerActionInput, s: ControllerState<T>| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let initialized_ongoing_reconcile = OngoingReconcile {
                pending_req_msg: Option::None,
                local_state: (reconciler.reconcile_init_state)(),
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, initialized_ongoing_reconcile),
                scheduled_reconciles: s.scheduled_reconciles.remove(cr_key),
                ..s
            };
            let send = Multiset::empty();
            (s_prime, send)
        },
    }
}

pub open spec fn continue_reconcile<T>(reconciler: Reconciler<T>) -> ControllerAction<T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<T>| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& !(reconciler.reconcile_done)(s.ongoing_reconciles[cr_key].local_state)
                &&& !(reconciler.reconcile_error)(s.ongoing_reconciles[cr_key].local_state)
                &&& if input.recv.is_Some() {
                    &&& input.recv.get_Some_0().content.is_APIResponse()
                    &&& s.ongoing_reconciles[cr_key].pending_req_msg.is_Some()
                    &&& resp_msg_matches_req_msg(input.recv.get_Some_0(), s.ongoing_reconciles[cr_key].pending_req_msg.get_Some_0())
                } else {
                    s.ongoing_reconciles[cr_key].pending_req_msg.is_None()
                }
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: ControllerState<T>| {
            let resp_o = if input.recv.is_Some() {
                Option::Some(input.recv.get_Some_0().content.get_APIResponse_0())
            } else {
                Option::None
            };
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let reconcile_state = s.ongoing_reconciles[cr_key];

            let (local_state_prime, req_o) = (reconciler.reconcile_core)(cr_key, resp_o, reconcile_state.local_state);

            let pending_req_msg = if req_o.is_Some() {
                Option::Some(controller_req_msg(req_o.get_Some_0(), s.req_id))
            } else {
                Option::None
            };

            let reconcile_state_prime = OngoingReconcile {
                pending_req_msg: pending_req_msg,
                local_state: local_state_prime,
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, reconcile_state_prime),
                req_id: s.req_id + 1,
                ..s
            };
            let send = if pending_req_msg.is_Some() {
                Multiset::singleton(pending_req_msg.get_Some_0())
            } else {
                Multiset::empty()
            };
            (s_prime, send)
        }
    }
}

pub open spec fn end_reconcile<T>(reconciler: Reconciler<T>) -> ControllerAction<T> {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState<T>| {
            if input.scheduled_cr_key.is_Some() {
                let cr_key = input.scheduled_cr_key.get_Some_0();

                &&& s.ongoing_reconciles.dom().contains(cr_key)
                &&& ((reconciler.reconcile_done)(s.ongoing_reconciles[cr_key].local_state) || (reconciler.reconcile_error)(s.ongoing_reconciles[cr_key].local_state))
                &&& input.recv.is_None()
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: ControllerState<T>| {
            let cr_key = input.scheduled_cr_key.get_Some_0();
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.remove(cr_key),
                scheduled_reconciles: s.scheduled_reconciles.insert(cr_key),
                ..s
            };
            (s_prime, Multiset::empty())
        }
    }
}

}
