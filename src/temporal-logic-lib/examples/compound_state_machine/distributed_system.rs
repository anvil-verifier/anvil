// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::compound_state_machine::{
    client, client::client, common::*, controller, controller::controller, kubernetes_api,
    kubernetes_api::kubernetes_api, network, network::network,
};
use crate::pervasive::{map::*, option::*, seq::*, set::*, string::*};
use crate::state_machine::*;
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

pub open spec fn kubernetes_api_next() -> Action<State, Option<Message>, ()> {
    let result = |recv: Option<Message>, s: State| {
        let host_result = kubernetes_api().next_result(recv, s.kubernetes_api_state);
        let msg_ops = MessageOps {
            recv: recv,
            send: host_result.get_Enabled_1(),
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |recv: Option<Message>, s: State| {
            &&& result(recv, s).0.is_Enabled()
            &&& result(recv, s).1.is_Enabled()
        },
        transition: |recv: Option<Message>, s: State| {
            (State {
                kubernetes_api_state: result(recv, s).0.get_Enabled_0(),
                network_state: result(recv, s).1.get_Enabled_0(),
                ..s
            }, ())
        },
    }
}

pub open spec fn controller_next() -> Action<State, Option<Message>, ()> {
    let result = |recv: Option<Message>, s: State| {
        let host_result = controller().next_result(recv, s.controller_state);
        let msg_ops = MessageOps {
            recv: recv,
            send: host_result.get_Enabled_1(),
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |recv: Option<Message>, s: State| {
            &&& result(recv, s).0.is_Enabled()
            &&& result(recv, s).1.is_Enabled()
        },
        transition: |recv: Option<Message>, s: State| {
            (State {
                controller_state: result(recv, s).0.get_Enabled_0(),
                network_state: result(recv, s).1.get_Enabled_0(),
                ..s
            }, ())
        },
    }
}

pub open spec fn client_next() -> Action<State, Option<Message>, ()> {
    let result = |recv: Option<Message>, s: State| {
        let host_result = client().next_result(recv, s.client_state);
        let msg_ops = MessageOps {
            recv: recv,
            send: host_result.get_Enabled_1(),
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |recv: Option<Message>, s: State| {
            &&& result(recv, s).0.is_Enabled()
            &&& result(recv, s).1.is_Enabled()
        },
        transition: |recv: Option<Message>, s: State| {
            (State {
                client_state: result(recv, s).0.get_Enabled_0(),
                network_state: result(recv, s).1.get_Enabled_0(),
                ..s
            }, ())
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

pub open spec fn kubernetes_api_action_pre(action: kubernetes_api::KubernetesAPIAction, recv: Option<Message>) -> StatePred<State> {
    |s: State| {
        let host_result = kubernetes_api().next_action_result(action, recv, s.kubernetes_api_state);
        let msg_ops = MessageOps {
            recv: recv,
            send: host_result.get_Enabled_1(),
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        &&& host_result.is_Enabled()
        &&& network_result.is_Enabled()
    }
}

pub open spec fn controller_action_pre(action: controller::ControllerAction, recv: Option<Message>) -> StatePred<State> {
    |s: State| {
        let host_result = controller().next_action_result(action, recv, s.controller_state);
        let msg_ops = MessageOps {
            recv: recv,
            send: host_result.get_Enabled_1(),
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        &&& host_result.is_Enabled()
        &&& network_result.is_Enabled()
    }
}

pub proof fn kubernetes_api_action_pre_implies_next_pre(action: kubernetes_api::KubernetesAPIAction, recv: Option<Message>)
    requires
        kubernetes_api().actions.contains(action),
    ensures
        valid(lift_state(kubernetes_api_action_pre(action, recv)).implies(lift_state(kubernetes_api_next().pre(recv)))),
{
    assert forall |s| #[trigger] state_pred_call(kubernetes_api_action_pre(action, recv), s) implies state_pred_call(kubernetes_api_next().pre(recv), s) by {
        kubernetes_api::exists_next_step(action, recv, s.kubernetes_api_state);
    };
}

pub proof fn controller_action_pre_implies_next_pre(action: controller::ControllerAction, recv: Option<Message>)
    requires
        controller().actions.contains(action),
    ensures
        valid(lift_state(controller_action_pre(action, recv)).implies(lift_state(controller_next().pre(recv)))),
{
    assert forall |s| #[trigger] state_pred_call(controller_action_pre(action, recv), s) implies state_pred_call(controller_next().pre(recv), s) by {
        controller::exists_next_step(action, recv, s.controller_state);
    };
}

}
