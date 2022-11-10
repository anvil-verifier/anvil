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

pub open spec fn kubernetes_api_action(msg_ops: MessageOps) -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        &&& kubernetes_api_state_machine::next(s.kubernetes_api_state, s_prime.kubernetes_api_state, msg_ops)
        &&& network_state_machine::next(s.network_state, s_prime.network_state, msg_ops)
        &&& s_prime.controller_state === s.controller_state
        &&& s_prime.client_state === s.client_state
    }
}

pub open spec fn controller_action(msg_ops: MessageOps) -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        &&& controller_state_machine::next(s.controller_state, s_prime.controller_state, msg_ops)
        &&& network_state_machine::next(s.network_state, s_prime.network_state, msg_ops)
        &&& s_prime.kubernetes_api_state === s.kubernetes_api_state
        &&& s_prime.client_state === s.client_state
    }
}

pub open spec fn client_action(msg_ops: MessageOps) -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| {
        &&& client_state_machine::next(s.client_state, s_prime.client_state, msg_ops)
        &&& network_state_machine::next(s.network_state, s_prime.network_state, msg_ops)
        &&& s_prime.kubernetes_api_state === s.kubernetes_api_state
        &&& s_prime.controller_state === s.controller_state
    }
}

pub open spec fn stutter() -> ActionPred<CompoundState> {
    |s, s_prime| s === s_prime
}

pub enum CompoundStep {
    KubernetesAPIActionStep(MessageOps),
    ControllerActionStep(MessageOps),
    ClientActionStep(MessageOps),
    StutterStep,
}

pub open spec fn next_step(s: CompoundState, s_prime: CompoundState, step: CompoundStep) -> bool {
    match step {
        CompoundStep::KubernetesAPIActionStep(msg_ops) => kubernetes_api_action(msg_ops)(s, s_prime),
        CompoundStep::ControllerActionStep(msg_ops) => controller_action(msg_ops)(s, s_prime),
        CompoundStep::ClientActionStep(msg_ops) => client_action(msg_ops)(s, s_prime),
        CompoundStep::StutterStep => stutter()(s, s_prime),
    }
}

pub open spec fn next() -> ActionPred<CompoundState> {
    |s: CompoundState, s_prime: CompoundState| exists |step: CompoundStep| next_step(s, s_prime, step)
}

pub open spec fn sm_spec() -> TempPred<CompoundState> {
    lift_state(init())
    .and(always(lift_action(next())))
    .and(tla_forall(|msg_ops| weak_fairness(kubernetes_api_action(msg_ops))))
    .and(tla_forall(|msg_ops| weak_fairness(controller_action(msg_ops))))
}

spec fn message_sent(msg: Message) -> StatePred<CompoundState> {
    |s: CompoundState| s.network_state.sent_messages.contains(msg)
}

proof fn try_wf1(msg: Message)
    requires
        msg.is_CreateResponse(),
        msg.get_CreateResponse_0().obj.key.kind.is_CustomResourceKind(),
{

    let cr_create_resp_msg = msg;
    let sts_create_req_msg = create_req_msg(ResourceKey{
        name: msg.get_CreateResponse_0().obj.key.name + sts_suffix(),
        kind: ResourceKind::StatefulSetKind
    });

    let msg_ops = MessageOps {
        recv: Option::Some(cr_create_resp_msg),
        send: Set::empty().insert(sts_create_req_msg),
    };

    use_tla_forall::<CompoundState, MessageOps>(sm_spec(), |m| weak_fairness(controller_action(m)), msg_ops);

    assert forall |s| state_pred_call(message_sent(cr_create_resp_msg), s)
    implies enabled(controller_action(msg_ops))(s) by {
        let witness_s_prime = CompoundState {
            network_state: network_state_machine::NetworkState{
                sent_messages: s.network_state.sent_messages + msg_ops.send
            },
            ..s
        };
        let witness_controller_step = controller_state_machine::ControllerStep::SendCreateStsStep;
        assert(controller_state_machine::next_step(s.controller_state, witness_s_prime.controller_state, msg_ops, witness_controller_step));
        assert(action_pred_call(controller_action(msg_ops), s, witness_s_prime));
    };

    wf1::<CompoundState>(sm_spec(),
        next(),
        controller_action(msg_ops),
        message_sent(cr_create_resp_msg),
        message_sent(sts_create_req_msg),
    );
}

}
