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

pub open spec fn kubernetes_api_action_pre(msg: Message) -> StatePred<CompoundState> {
    |s: CompoundState| {
        &&& s.network_state.sent_messages.contains(msg)
        &&& kubernetes_api_state_machine::handle_request_pre(s.kubernetes_api_state, msg)
    }
}

/// TODO: Ideally, we should not choose any outbound messages.
/// kubernetes_api_state_machine should decide the outbound messages
/// and return them to the compound one
pub open spec fn kubernetes_api_action(msg: Message) -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        exists |outbound_msgs: Set<Message>| {
            &&& #[trigger] kubernetes_api_state_machine::next(s.kubernetes_api_state, s_prime.kubernetes_api_state, MessageOps {
                recv: Option::Some(msg),
                send: outbound_msgs,
            })
            &&& network_state_machine::next(s.network_state, s_prime.network_state, MessageOps {
                recv: Option::Some(msg),
                send: outbound_msgs,
            })
            &&& s_prime.controller_state === s.controller_state
            &&& s_prime.client_state === s.client_state
        }
    }
}

pub open spec fn controller_action(msg: Message) -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        exists |outbound_msgs: Set<Message>| {
            &&& #[trigger] controller_state_machine::next(s.controller_state, s_prime.controller_state, MessageOps {
                recv: Option::Some(msg),
                send: outbound_msgs,
            })
            &&& network_state_machine::next(s.network_state, s_prime.network_state, MessageOps {
                recv: Option::Some(msg),
                send: outbound_msgs,
            })
            &&& s_prime.kubernetes_api_state === s.kubernetes_api_state
            &&& s_prime.client_state === s.client_state
        }
    }
}

pub open spec fn client_action() -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        exists |outbound_msgs: Set<Message>| {
            &&& #[trigger] client_state_machine::next(s.client_state, s_prime.client_state, MessageOps {
                recv: Option::None,
                send: outbound_msgs,
            })
            &&& network_state_machine::next(s.network_state, s_prime.network_state, MessageOps {
                recv: Option::None,
                send: outbound_msgs,
            })
            &&& s_prime.kubernetes_api_state === s.kubernetes_api_state
            &&& s_prime.controller_state === s.controller_state
        }
    }
}

pub open spec fn stutter() -> ActionPred<CompoundState> {
    |s, s_prime| s === s_prime
}

pub enum CompoundStep {
    KubernetesAPIActionStep(Message),
    ControllerActionStep(Message),
    ClientActionStep,
    StutterStep,
}

pub open spec fn next_step(s: CompoundState, s_prime: CompoundState, step: CompoundStep) -> bool {
    match step {
        CompoundStep::KubernetesAPIActionStep(msg) => kubernetes_api_action(msg)(s, s_prime),
        CompoundStep::ControllerActionStep(msg) => controller_action(msg)(s, s_prime),
        CompoundStep::ClientActionStep => client_action()(s, s_prime),
        CompoundStep::StutterStep => stutter()(s, s_prime),
    }
}

pub open spec fn next() -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| exists |step: CompoundStep| next_step(s, s_prime, step)
}

pub open spec fn sm_spec() -> TempPred<CompoundState> {
    lift_state(init())
    .and(always(lift_action(next())))
    .and(tla_forall(|msg| weak_fairness(kubernetes_api_action(msg))))
    .and(tla_forall(|msg| weak_fairness(controller_action(msg))))
}

pub open spec fn resource_exists(key: ResourceKey) -> StatePred<CompoundState> {
    |s: CompoundState| s.kubernetes_api_state.resources.dom().contains(key)
}

pub proof fn kubernetes_api_action_enabled(msg: Message)
    ensures
        forall |s| #[trigger] state_pred_call(kubernetes_api_action_pre(msg), s)
            ==> enabled(kubernetes_api_action(msg))(s),
{
    assert forall |s| #[trigger] state_pred_call(kubernetes_api_action_pre(msg), s) implies enabled(kubernetes_api_action(msg))(s) by {
        let msg_ops = MessageOps {
            recv: Option::Some(msg),
            send: kubernetes_api_state_machine::outcome_messages(s.kubernetes_api_state, msg),
        };
        let s_prime = CompoundState {
            network_state: network_state_machine::NetworkState{
                sent_messages: s.network_state.sent_messages + msg_ops.send
            },
            kubernetes_api_state: kubernetes_api_state_machine::KubernetesAPIState{
                resources: kubernetes_api_state_machine::update_resources_with(s.kubernetes_api_state, msg),
            },
            ..s
        };
        let witness_kubernetes_step = kubernetes_api_state_machine::KubernetesAPIStep::HandleRequest;
        assert(kubernetes_api_state_machine::next_step(s.kubernetes_api_state, s_prime.kubernetes_api_state, msg_ops, witness_kubernetes_step));
        assert(kubernetes_api_state_machine::next(s.kubernetes_api_state, s_prime.kubernetes_api_state, msg_ops));
        assert(action_pred_call(kubernetes_api_action(msg), s, s_prime));
    };
}

pub proof fn controller_action_enabled_by_create_cr_resp_sent(msg: Message)
    requires
        msg.is_CreateResponse(),
        msg.get_CreateResponse_0().obj.key.kind.is_CustomResourceKind(),
    ensures
        forall |s| state_pred_call(message_sent(msg), s) ==> enabled(controller_action(msg))(s),
{
    assert forall |s| state_pred_call(message_sent(msg), s) implies enabled(controller_action(msg))(s) by {
        let msg_ops = MessageOps {
            recv: Option::Some(msg),
            send: set![create_req_msg(ResourceKey{
                name: msg.get_CreateResponse_0().obj.key.name + sts_suffix(),
                kind: ResourceKind::StatefulSetKind
            })],
        };
        let s_prime = CompoundState {
            network_state: network_state_machine::NetworkState{
                sent_messages: s.network_state.sent_messages + msg_ops.send
            },
            ..s
        };
        let witness_controller_step = controller_state_machine::ControllerStep::SendCreateStsStep;
        assert(controller_state_machine::next_step(s.controller_state, s_prime.controller_state, msg_ops, witness_controller_step));
        assert(controller_state_machine::next(s.controller_state, s_prime.controller_state, msg_ops));
        assert(action_pred_call(controller_action(msg), s, s_prime));
    };
}


}
