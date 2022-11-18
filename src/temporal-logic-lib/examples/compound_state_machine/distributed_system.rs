// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::compound_state_machine::{
    client, client::client, common::*, controller, controller::controller, kubernetes_api,
    kubernetes_api::kubernetes_api, network, network::network,
};
use crate::pervasive::{map::*, option::*, seq::*, set::*, string::*};
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct State {
    pub kubernetes_api_state: kubernetes_api::State,
    pub controller_state: controller::State,
    pub client_state: client::State,
    pub network_state: network::State,
}

pub open spec fn init() -> StatePred<State> {
    |s: State| {
        &&& (kubernetes_api().init)(s.kubernetes_api_state)
        &&& (controller().init)(s.controller_state)
        &&& (client().init)(s.client_state)
        &&& (network().init)(s.network_state)
    }
}

pub open spec fn kubernetes_api_next() -> CompoundAction<State, Option<Message>> {
    CompoundAction {
        precondition: |recv: Option<Message>, s: State| {
            let host_result = kubernetes_api().next_result(recv, s.kubernetes_api_state);
            let network_result = network().next_result(recv, s.network_state, host_result.get_Enabled_1());

            &&& host_result.is_Enabled()
            &&& network_result.is_Enabled()
        },
        transition: |recv: Option<Message>, s: State| {
            let host_result = kubernetes_api().next_result(recv, s.kubernetes_api_state);
            let network_result = network().next_result(recv, s.network_state, host_result.get_Enabled_1());

            State {
                kubernetes_api_state: host_result.get_Enabled_0(),
                network_state: network_result.get_Enabled_0(),
                ..s
            }
        },
    }
}

pub open spec fn controller_next() -> CompoundAction<State, Option<Message>> {
    CompoundAction {
        precondition: |recv: Option<Message>, s: State| {
            let host_result = controller().next_result(recv, s.controller_state);
            let network_result = network().next_result(recv, s.network_state, host_result.get_Enabled_1());

            &&& host_result.is_Enabled()
            &&& network_result.is_Enabled()
        },
        transition: |recv: Option<Message>, s: State| {
            let host_result = controller().next_result(recv, s.controller_state);
            let network_result = network().next_result(recv, s.network_state, host_result.get_Enabled_1());

            State {
                controller_state: host_result.get_Enabled_0(),
                network_state: network_result.get_Enabled_0(),
                ..s
            }
        },
    }
}

pub open spec fn client_next() -> CompoundAction<State, Option<Message>> {
    CompoundAction {
        precondition: |recv: Option<Message>, s: State| {
            let host_result = client().next_result(recv, s.client_state);
            let network_result = network().next_result(recv, s.network_state, host_result.get_Enabled_1());

            &&& host_result.is_Enabled()
            &&& network_result.is_Enabled()
        },
        transition: |recv: Option<Message>, s: State| {
            let host_result = client().next_result(recv, s.client_state);
            let network_result = network().next_result(recv, s.network_state, host_result.get_Enabled_1());

            State {
                client_state: host_result.get_Enabled_0(),
                network_state: network_result.get_Enabled_0(),
                ..s
            }
        },
    }
}

pub enum Step {
    KubernetesAPIStep(Option<Message>),
    ControllerStep(Option<Message>),
    ClientStep(Option<Message>),
    StutterStep,
}

pub open spec fn next_step(s: State, s_prime: State, step: Step) -> bool {
    match step {
        Step::KubernetesAPIStep(recv) => kubernetes_api_next().forward(recv)(s, s_prime),
        Step::ControllerStep(recv) => controller_next().forward(recv)(s, s_prime),
        Step::ClientStep(recv) => client_next().forward(recv)(s, s_prime),
        Step::StutterStep => s === s_prime,
    }
}

/// `next` chooses:
/// * which host to take the next action (`Step`)
/// * whether to deliver a message and which message to deliver (`Option<Message>` in `Step`)
pub open spec fn next() -> ActionPred<State> {
    |s: State, s_prime: State| exists |step: Step| next_step(s, s_prime, step)
}

pub open spec fn sm_spec() -> TempPred<State> {
    lift_state(init())
    .and(always(lift_action(next())))
    .and(tla_forall(|recv| weak_fairness(kubernetes_api_next().forward(recv))))
    .and(tla_forall(|recv| weak_fairness(controller_next().forward(recv))))
}

pub open spec fn message_sent(msg: Message) -> StatePred<State> {
    |s: State| s.network_state.sent_messages.contains(msg)
}

pub open spec fn resource_exists(key: ResourceKey) -> StatePred<State> {
    |s: State| s.kubernetes_api_state.resources.dom().contains(key)
}

pub open spec fn kubernetes_api_action_pre(recv: Option<Message>, action: kubernetes_api::KubernetesAPIAction) -> StatePred<State> {
    |s: State| {
        &&& (network::deliver().precondition)(recv, s.network_state)
        &&& (action.precondition)(recv, s.kubernetes_api_state)
    }
}

pub proof fn kubernetes_api_action_enabled(recv: Option<Message>, action: kubernetes_api::KubernetesAPIAction)
    requires
        kubernetes_api().actions.contains(action),
    ensures
        forall |s| state_pred_call(kubernetes_api_action_pre(recv, action), s) ==> enabled(kubernetes_api_next().forward(recv))(s),
{
    assert forall |s| #[trigger] state_pred_call(kubernetes_api_action_pre(recv, action), s) implies state_pred_call(kubernetes_api_next().pre(recv), s) by {
        kubernetes_api::exists_next_step(action, recv, s.kubernetes_api_state);
    };
    kubernetes_api_next().pre_implies_forward_enabled(recv);
}

pub open spec fn controller_action_pre(recv: Option<Message>, action: controller::ControllerAction) -> StatePred<State> {
    |s: State| {
        &&& (network::deliver().precondition)(recv, s.network_state)
        &&& (action.precondition)(recv, s.controller_state)
    }
}

pub proof fn controller_action_enabled(recv: Option<Message>, action: controller::ControllerAction)
    requires
        controller().actions.contains(action),
    ensures
        forall |s| state_pred_call(controller_action_pre(recv, action), s) ==> enabled(controller_next().forward(recv))(s),
{
    assert forall |s| #[trigger] state_pred_call(controller_action_pre(recv, action), s) implies state_pred_call(controller_next().pre(recv), s) by {
        controller::exists_next_step(action, recv, s.controller_state);
    };
    controller_next().pre_implies_forward_enabled(recv);
}

}
