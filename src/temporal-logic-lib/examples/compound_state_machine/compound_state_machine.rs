// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::compound_state_machine::{
    client_state_machine, common::*, controller_state_machine, kubernetes_api_state_machine,
    network_state_machine,
};
use crate::pervasive::{map::*, option::*, seq::*, set::*, string::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct CompoundState {
    pub kubernetes_api_state: kubernetes_api_state_machine::KubernetesAPIState,
    pub controller_state: controller_state_machine::ControllerState,
    pub network_state: network_state_machine::NetworkState,
    pub client_state: client_state_machine::ClientState,
}

pub open spec fn init() -> StatePred<CompoundState> {
    |s: CompoundState| {
        &&& kubernetes_api_state_machine::init(s.kubernetes_api_state)
        &&& controller_state_machine::init(s.controller_state)
        &&& network_state_machine::init(s.network_state)
        &&& client_state_machine::init(s.client_state)
    }
}

pub open spec fn message_sent(msg: Message) -> StatePred<CompoundState> {
    |s: CompoundState| s.network_state.sent_messages.contains(msg)
}

pub open spec fn kubernetes_api_action_handle_request_pre(recv: Option<Message>) -> StatePred<CompoundState> {
    |s: CompoundState| {
        &&& (network_state_machine::deliver().precondition)(recv, s.network_state)
        &&& (kubernetes_api_state_machine::handle_request().precondition)(recv, s.kubernetes_api_state)
    }
}

/// TODO: Ideally, we should not choose any outbound messages.
/// kubernetes_api_state_machine should decide the outbound messages
/// and return them to the compound one
pub open spec fn kubernetes_api_action(recv: Option<Message>) -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        exists |output_messages: Set<Message>| {
            &&& #[trigger] kubernetes_api_state_machine::next(recv, s.kubernetes_api_state, s_prime.kubernetes_api_state, output_messages)
            &&& network_state_machine::next(recv, s.network_state, s_prime.network_state, output_messages)
            &&& s_prime.controller_state === s.controller_state
            &&& s_prime.client_state === s.client_state
        }
    }
}

pub open spec fn controller_action_send_create_sts_pre(recv: Option<Message>) -> StatePred<CompoundState> {
    |s: CompoundState| {
        &&& (network_state_machine::deliver().precondition)(recv, s.network_state)
        &&& (controller_state_machine::send_create_sts().precondition)(recv, s.controller_state)
    }
}

pub open spec fn controller_action(recv: Option<Message>) -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        exists |output_messages: Set<Message>| {
            &&& #[trigger] controller_state_machine::next(recv, s.controller_state, s_prime.controller_state, output_messages)
            &&& network_state_machine::next(recv, s.network_state, s_prime.network_state, output_messages)
            &&& s_prime.kubernetes_api_state === s.kubernetes_api_state
            &&& s_prime.client_state === s.client_state
        }
    }
}

pub open spec fn client_action(recv: Option<Message>) -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        exists |output_messages: Set<Message>| {
            &&& #[trigger] client_state_machine::next(recv, s.client_state, s_prime.client_state, output_messages)
            &&& network_state_machine::next(recv, s.network_state, s_prime.network_state, output_messages)
            &&& s_prime.kubernetes_api_state === s.kubernetes_api_state
            &&& s_prime.controller_state === s.controller_state
        }
    }
}

pub open spec fn stutter() -> ActionPred<CompoundState> {
    |s, s_prime| s === s_prime
}

pub enum CompoundStep {
    KubernetesAPIActionStep(Option<Message>),
    ControllerActionStep(Option<Message>),
    ClientActionStep(Option<Message>),
    StutterStep,
}

pub open spec fn next_step(s: CompoundState, s_prime: CompoundState, step: CompoundStep) -> bool {
    match step {
        CompoundStep::KubernetesAPIActionStep(recv) => kubernetes_api_action(recv)(s, s_prime),
        CompoundStep::ControllerActionStep(recv) => controller_action(recv)(s, s_prime),
        CompoundStep::ClientActionStep(recv) => client_action(recv)(s, s_prime),
        CompoundStep::StutterStep => stutter()(s, s_prime),
    }
}

pub open spec fn next() -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| exists |step: CompoundStep| next_step(s, s_prime, step)
}

pub open spec fn sm_spec() -> TempPred<CompoundState> {
    lift_state(init())
    .and(always(lift_action(next())))
    .and(tla_forall(|recv| weak_fairness(kubernetes_api_action(recv))))
    .and(tla_forall(|recv| weak_fairness(controller_action(recv))))
}

pub open spec fn resource_exists(key: ResourceKey) -> StatePred<CompoundState> {
    |s: CompoundState| s.kubernetes_api_state.resources.dom().contains(key)
}

pub proof fn kubernetes_api_action_handle_request_enabled(recv: Option<Message>)
    ensures
        forall |s| state_pred_call(kubernetes_api_action_handle_request_pre(recv), s)
            ==> enabled(kubernetes_api_action(recv))(s),
{
    assert forall |s| state_pred_call(kubernetes_api_action_handle_request_pre(recv), s) implies enabled(kubernetes_api_action(recv))(s) by {
        let send = (kubernetes_api_state_machine::handle_request().output)(recv, s.kubernetes_api_state);
        let s_prime = CompoundState {
            network_state: (network_state_machine::deliver().transition)(recv, s.network_state, send),
            kubernetes_api_state: (kubernetes_api_state_machine::handle_request().transition)(recv, s.kubernetes_api_state),
            ..s
        };
        let witness_kubernetes_step = kubernetes_api_state_machine::KubernetesAPIStep::HandleRequest;
        assert(kubernetes_api_state_machine::next_step(recv, s.kubernetes_api_state, s_prime.kubernetes_api_state, send, witness_kubernetes_step));
        assert(kubernetes_api_state_machine::next(recv, s.kubernetes_api_state, s_prime.kubernetes_api_state, send));
        assert(action_pred_call(kubernetes_api_action(recv), s, s_prime));
    };
}

pub proof fn controller_action_send_create_sts_enabled(recv: Option<Message>)
    ensures
        forall |s| state_pred_call(controller_action_send_create_sts_pre(recv), s) ==> enabled(controller_action(recv))(s),
{
    assert forall |s| state_pred_call(controller_action_send_create_sts_pre(recv), s) implies enabled(controller_action(recv))(s) by {
        let send = (controller_state_machine::send_create_sts().output)(recv, s.controller_state);
        let s_prime = CompoundState {
            network_state: (network_state_machine::deliver().transition)(recv, s.network_state, send),
            controller_state: (controller_state_machine::send_create_sts().transition)(recv, s.controller_state),
            ..s
        };
        let witness_controller_step = controller_state_machine::ControllerStep::SendCreateStsStep;
        assert(controller_state_machine::next_step(recv, s.controller_state, s_prime.controller_state, send, witness_controller_step));
        assert(controller_state_machine::next(recv, s.controller_state, s_prime.controller_state, send));
        assert(action_pred_call(controller_action(recv), s, s_prime));
    };
}

}
