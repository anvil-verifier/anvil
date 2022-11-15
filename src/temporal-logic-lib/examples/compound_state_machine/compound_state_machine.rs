// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::compound_state_machine::{
    client_state_machine as client, common::*, controller_state_machine as controller,
    kubernetes_api_state_machine as kubernetes_api, network_state_machine as network,
};
use crate::pervasive::{map::*, option::*, seq::*, set::*, string::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct CompoundState {
    pub kubernetes_api_state: kubernetes_api::State,
    pub controller_state: controller::State,
    pub network_state: network::State,
    pub client_state: client::State,
}

pub open spec fn init() -> StatePred<CompoundState> {
    |s: CompoundState| {
        &&& kubernetes_api::init(s.kubernetes_api_state)
        &&& controller::init(s.controller_state)
        &&& network::init(s.network_state)
        &&& client::init(s.client_state)
    }
}

pub open spec fn message_sent(msg: Message) -> StatePred<CompoundState> {
    |s: CompoundState| s.network_state.sent_messages.contains(msg)
}

pub open spec fn kubernetes_api_action_handle_request_pre(recv: Option<Message>) -> StatePred<CompoundState> {
    |s: CompoundState| {
        &&& (network::deliver().precondition)(recv, s.network_state)
        &&& (kubernetes_api::handle_request().precondition)(recv, s.kubernetes_api_state)
    }
}

pub open spec fn controller_action_send_create_sts_pre(recv: Option<Message>) -> StatePred<CompoundState> {
    |s: CompoundState| {
        &&& (network::deliver().precondition)(recv, s.network_state)
        &&& (controller::send_create_sts().precondition)(recv, s.controller_state)
    }
}

pub open spec fn kubernetes_api_action(recv: Option<Message>) -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        &&& kubernetes_api::next(recv, s.kubernetes_api_state, s_prime.kubernetes_api_state)
        &&& network::next(recv, s.network_state, s_prime.network_state, kubernetes_api::output(recv, s.kubernetes_api_state, s_prime.kubernetes_api_state))
        &&& s_prime.controller_state === s.controller_state
        &&& s_prime.client_state === s.client_state
    }
}

pub open spec fn controller_action(recv: Option<Message>) -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        &&& controller::next(recv, s.controller_state, s_prime.controller_state)
        &&& network::next(recv, s.network_state, s_prime.network_state, controller::output(recv, s.controller_state, s_prime.controller_state))
        &&& s_prime.kubernetes_api_state === s.kubernetes_api_state
        &&& s_prime.client_state === s.client_state
    }
}

pub open spec fn client_action(recv: Option<Message>) -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        &&& client::next(recv, s.client_state, s_prime.client_state)
        &&& network::next(recv, s.network_state, s_prime.network_state, client::output(recv, s.client_state, s_prime.client_state))
        &&& s_prime.kubernetes_api_state === s.kubernetes_api_state
        &&& s_prime.controller_state === s.controller_state
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
        let send = (kubernetes_api::handle_request().output)(recv, s.kubernetes_api_state);
        let s_prime = CompoundState {
            network_state: (network::deliver().transition)(recv, s.network_state, send),
            kubernetes_api_state: (kubernetes_api::handle_request().transition)(recv, s.kubernetes_api_state),
            ..s
        };
        let witness_kubernetes_step = kubernetes_api::KubernetesAPIStep::HandleRequest;
        assert(kubernetes_api::next_step(recv, s.kubernetes_api_state, s_prime.kubernetes_api_state, witness_kubernetes_step));
        assert(kubernetes_api::next(recv, s.kubernetes_api_state, s_prime.kubernetes_api_state));
        assert(action_pred_call(kubernetes_api_action(recv), s, s_prime));
    };
}

pub proof fn controller_action_send_create_sts_enabled(recv: Option<Message>)
    ensures
        forall |s| state_pred_call(controller_action_send_create_sts_pre(recv), s) ==> enabled(controller_action(recv))(s),
{
    assert forall |s| state_pred_call(controller_action_send_create_sts_pre(recv), s) implies enabled(controller_action(recv))(s) by {
        let send = (controller::send_create_sts().output)(recv, s.controller_state);
        let s_prime = CompoundState {
            network_state: (network::deliver().transition)(recv, s.network_state, send),
            controller_state: (controller::send_create_sts().transition)(recv, s.controller_state),
            ..s
        };
        let witness_controller_step = controller::ControllerStep::SendCreateStsStep;
        assert(controller::next_step(recv, s.controller_state, s_prime.controller_state, witness_controller_step));
        assert(controller::next(recv, s.controller_state, s_prime.controller_state));
        assert(action_pred_call(controller_action(recv), s, s_prime));
    };
}

}
