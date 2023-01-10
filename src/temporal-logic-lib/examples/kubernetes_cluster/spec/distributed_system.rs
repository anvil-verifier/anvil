// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::kubernetes_cluster::spec::{
    client,
    client::{client, ClientActionInput, ClientState},
    common::*,
    controller::common::{
        ControllerAction, ControllerActionInput, ControllerState, OngoingReconcile,
    },
    controller::state_machine::controller,
    kubernetes_api::common::{KubernetesAPIAction, KubernetesAPIActionInput, KubernetesAPIState},
    kubernetes_api::state_machine::kubernetes_api,
    network,
    network::{network, NetworkState},
    reconciler::Reconciler,
};
use crate::pervasive::{map::*, option::*, seq::*, set::*};
use crate::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct State {
    pub kubernetes_api_state: KubernetesAPIState,
    pub controller_state: ControllerState,
    pub client_state: ClientState,
    pub network_state: NetworkState,
}

impl State {
    #[verifier(inline)]
    pub open spec fn message_sent(self, msg: Message) -> bool {
        self.network_state.sent_messages.contains(msg)
    }

    pub open spec fn resource_key_exists(self, key: ResourceKey) -> bool {
        self.kubernetes_api_state.resources.dom().contains(key)
    }

    pub open spec fn resource_obj_exists(self, obj: ResourceObj) -> bool {
        &&& self.kubernetes_api_state.resources.dom().contains(obj.key)
        &&& self.kubernetes_api_state.resources[obj.key] === obj
    }

    pub open spec fn resource_obj_of(self, key: ResourceKey) -> ResourceObj
        recommends self.resource_key_exists(key)
    {
        self.kubernetes_api_state.resources[key]
    }

    pub open spec fn reconcile_state_contains(self, key: ResourceKey) -> bool {
        self.controller_state.ongoing_reconciles.dom().contains(key)
    }

    pub open spec fn reconcile_state_of(self, key: ResourceKey) -> OngoingReconcile
        recommends self.reconcile_state_contains(key)
    {
        self.controller_state.ongoing_reconciles[key]
    }

    pub open spec fn reconcile_scheduled_for(self, key: ResourceKey) -> bool {
        self.controller_state.scheduled_reconciles.contains(key)
    }
}

pub open spec fn init(reconciler: Reconciler) -> StatePred<State> {
    |s: State| {
        &&& (kubernetes_api().init)(s.kubernetes_api_state)
        &&& (controller(reconciler).init)(s.controller_state)
        &&& (client().init)(s.client_state)
        &&& (network().init)(s.network_state)
    }
}

pub open spec fn received_msg_destined_for(recv: Option<Message>, host_id: HostId) -> bool {
    if recv.is_Some() {
        recv.get_Some_0().dst === host_id
    } else {
        true
    }
}

pub open spec fn kubernetes_api_next() -> Action<State, KubernetesAPIActionInput, ()> {
    let result = |input: KubernetesAPIActionInput, s: State| {
        let host_result = kubernetes_api().next_result(input, s.kubernetes_api_state);
        let msg_ops = MessageOps {
            recv: input,
            send: host_result.get_Enabled_1(),
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |input: KubernetesAPIActionInput, s: State| {
            &&& received_msg_destined_for(input, HostId::KubernetesAPI)
            &&& result(input, s).0.is_Enabled()
            &&& result(input, s).1.is_Enabled()
        },
        transition: |input: KubernetesAPIActionInput, s: State| {
            (State {
                kubernetes_api_state: result(input, s).0.get_Enabled_0(),
                network_state: result(input, s).1.get_Enabled_0(),
                ..s
            }, ())
        },
    }
}

pub open spec fn controller_next(reconciler: Reconciler) -> Action<State, ControllerActionInput, ()> {
    let result = |input: ControllerActionInput, s: State| {
        let host_result = controller(reconciler).next_result(input, s.controller_state);
        let msg_ops = MessageOps {
            recv: input.recv,
            send: host_result.get_Enabled_1(),
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |input: ControllerActionInput, s: State| {
            &&& received_msg_destined_for(input.recv, HostId::CustomController)
            &&& result(input, s).0.is_Enabled()
            &&& result(input, s).1.is_Enabled()
        },
        transition: |input: ControllerActionInput, s: State| {
            (State {
                controller_state: result(input, s).0.get_Enabled_0(),
                network_state: result(input, s).1.get_Enabled_0(),
                ..s
            }, ())
        },
    }
}

pub open spec fn client_next() -> Action<State, ClientActionInput, ()> {
    let result = |input: ClientActionInput, s: State| {
        let host_result = client().next_result(input, s.client_state);
        let msg_ops = MessageOps {
            recv: input.recv,
            send: host_result.get_Enabled_1(),
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |input: ClientActionInput, s: State| {
            &&& received_msg_destined_for(input.recv, HostId::Client)
            &&& result(input, s).0.is_Enabled()
            &&& result(input, s).1.is_Enabled()
        },
        transition: |input: ClientActionInput, s: State| {
            (State {
                client_state: result(input, s).0.get_Enabled_0(),
                network_state: result(input, s).1.get_Enabled_0(),
                ..s
            }, ())
        },
    }
}

pub open spec fn stutter() -> Action<State, Option<Message>, ()> {
    Action {
        precondition: |input: Option<Message>, s: State| {
            input.is_None()
        },
        transition: |input: Option<Message>, s: State| {
            (s, ())
        },
    }
}

pub enum Step {
    KubernetesAPIStep(KubernetesAPIActionInput),
    ControllerStep(ControllerActionInput),
    ClientStep(ClientActionInput),
    StutterStep(Option<Message>),
}

pub open spec fn next_step(reconciler: Reconciler, s: State, s_prime: State, step: Step) -> bool {
    match step {
        Step::KubernetesAPIStep(input) => kubernetes_api_next().forward(input)(s, s_prime),
        Step::ControllerStep(input) => controller_next(reconciler).forward(input)(s, s_prime),
        Step::ClientStep(input) => client_next().forward(input)(s, s_prime),
        Step::StutterStep(input) => stutter().forward(input)(s, s_prime),
    }
}

/// `next` chooses:
/// * which host to take the next action (`Step`)
/// * whether to deliver a message and which message to deliver (`Option<Message>` in `Step`)
pub open spec fn next(reconciler: Reconciler) -> ActionPred<State> {
    |s: State, s_prime: State| exists |step: Step| next_step(reconciler, s, s_prime, step)
}

/// We install the reconciler to the Kubernetes cluster state machine spec
/// TODO: develop a struct for the compound state machine and make reconciler its member
/// so that we don't have to pass reconciler to init and next in the proof.
pub open spec fn sm_spec(reconciler: Reconciler) -> TempPred<State> {
    lift_state(init(reconciler))
    .and(always(lift_action(next(reconciler))))
    .and(tla_forall(|input| kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| controller_next(reconciler).weak_fairness(input)))
}

pub open spec fn kubernetes_api_action_pre(action: KubernetesAPIAction, input: KubernetesAPIActionInput) -> StatePred<State> {
    |s: State| {
        let host_result = kubernetes_api().next_action_result(action, input, s.kubernetes_api_state);
        let msg_ops = MessageOps {
            recv: input,
            send: host_result.get_Enabled_1(),
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        &&& received_msg_destined_for(input, HostId::KubernetesAPI)
        &&& host_result.is_Enabled()
        &&& network_result.is_Enabled()
    }
}

pub open spec fn controller_action_pre(reconciler: Reconciler, action: ControllerAction, input: ControllerActionInput) -> StatePred<State> {
    |s: State| {
        let host_result = controller(reconciler).next_action_result(action, input, s.controller_state);
        let msg_ops = MessageOps {
            recv: input.recv,
            send: host_result.get_Enabled_1(),
        };
        let network_result = network().next_result(msg_ops, s.network_state);

        &&& received_msg_destined_for(input.recv, HostId::CustomController)
        &&& host_result.is_Enabled()
        &&& network_result.is_Enabled()
    }
}

}
