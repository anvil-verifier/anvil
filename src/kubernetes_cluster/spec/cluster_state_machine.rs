// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{api_method::*, common::*, dynamic::*, error::*, resource::*};
use crate::kubernetes_cluster::spec::{
    client::types::ClientActionInput,
    cluster::Cluster,
    controller::common::{
        ControllerAction, ControllerActionInput, ControllerState, OngoingReconcile,
    },
    external_api::*,
    kubernetes_api::common::{KubernetesAPIAction, KubernetesAPIActionInput},
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

#[is_variant]
pub enum Step<K, E: ExternalAPI> {
    KubernetesAPIStep(Option<Message>),
    ControllerStep((Option<Message>, Option<ExternalComm<E::Input, E::Output>>, Option<ObjectRef>)),
    ClientStep((Option<Message>, K)),
    ExternalAPIStep(ExternalComm<E::Input, E::Output>),
    ScheduleControllerReconcileStep(ObjectRef),
    RestartController(),
    DisableCrash(),
    KubernetesBusy(Option<Message>),
    DisableBusy(),
    StutterStep(),
}

impl<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn init() -> StatePred<Self> {
    |s: Self| {
        &&& (Self::kubernetes_api().init)(s.kubernetes_api_state)
        &&& (Self::controller().init)(s.controller_state)
        &&& (Self::client().init)(s.client_state)
        &&& (Self::network().init)(s.network_state)
        &&& Self::external_api_state_init(s.external_api_state)
        &&& s.crash_enabled
        &&& s.busy_enabled
    }
}

pub open spec fn kubernetes_api_next() -> Action<Self, Option<Message>, ()> {
    let result = |input: Option<Message>, s: Self| {
        let host_result = Self::kubernetes_api().next_result(
            KubernetesAPIActionInput{recv: input, rest_id_allocator: s.rest_id_allocator},
            s.kubernetes_api_state
        );
        let msg_ops = MessageOps {
            recv: input,
            send: host_result.get_Enabled_1().0,
        };
        let network_result = Self::network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |input: Option<Message>, s: Self| {
            &&& received_msg_destined_for(input, HostId::KubernetesAPI)
            &&& result(input, s).0.is_Enabled()
            &&& result(input, s).1.is_Enabled()
        },
        transition: |input: Option<Message>, s: Self| {
            (Self {
                kubernetes_api_state: result(input, s).0.get_Enabled_0(),
                network_state: result(input, s).1.get_Enabled_0(),
                rest_id_allocator: result(input, s).0.get_Enabled_1().1,
                ..s
            }, ())
        },
    }
}

/// This action basically executes the transition process of the external api. When external support is needed, It receives
/// the result computed by the controller as input and store the output of the transition for later use. If no external api
/// is used (i.e., EmptyAPI is fed to the reconciler), the precondition should not be satisfied since the developer should not
/// make reconcile_core return a external request.
///
/// This action simulates the behavior of certain executions where the reconcile process is blocked and waits for the handling
/// by external api, the external api will then take the input provided by the controller and carry out its own operations.
/// We make all the operations by the external api each time atomic.
pub open spec fn external_api_next() -> Action<Self, ExternalComm<E::Input, E::Output>, ()> {
    Action {
        precondition: |input: ExternalComm<E::Input, E::Output>, s: Self| {
            // For the external api action, a valid input must exist in the in_flight set of the external_api_state.
            &&& input.is_Input()
            &&& s.external_api_state.in_flight.contains(input)
        },
        transition: |input: ExternalComm<E::Input, E::Output>, s: Self| {
            let s_external = s.external_api_state;
            let (external_api_output_opt, external_api_state_prime) = E::transition(input.get_Input_0(), s_external.external_api_state);
            let output = if external_api_output_opt.is_None() { Option::None }
                            else { Option::Some(ExternalComm::Output(external_api_output_opt.get_Some_0(), input.get_Input_1())) };
            // After this action, the input should be removed, and, if there is an output destined for the external api,
            // it should be inserted to the in_flight set.
            let s_prime_external = ExternalAPIState {
                external_api_state: external_api_state_prime,
                in_flight: if output.is_Some() { s_external.in_flight.remove(input).insert(output.get_Some_0()) }
                                    else { s_external.in_flight.remove(input) },
            };
            let s_prime = Self {
                external_api_state: s_prime_external,
                ..s
            };
            (s_prime, ())
        },
    }
}

pub open spec fn controller_next() -> Action<Self, (Option<Message>, Option<ExternalComm<E::Input, E::Output>>, Option<ObjectRef>), ()> {
    let result = |input: (Option<Message>, Option<ExternalComm<E::Input, E::Output>>, Option<ObjectRef>), s: Self| {
        let host_result = Self::controller().next_result(
            ControllerActionInput{recv: input.0, external_api_output: input.1, scheduled_cr_key: input.2, rest_id_allocator: s.rest_id_allocator},
            s.controller_state
        );
        let msg_ops = MessageOps {
            recv: input.0,
            send: host_result.get_Enabled_1().send,
        };
        let network_result = Self::network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |input: (Option<Message>, Option<ExternalComm<E::Input, E::Output>>, Option<ObjectRef>), s: Self| {
            &&& received_msg_destined_for(input.0, HostId::CustomController)
            // This precondition requires that if the response from the external library is not empty,
            // it must be contained by the set in the external_api_state.
            // This ensures the response is produced by the external api.
            &&& input.1.is_Some() ==> s.external_api_state.in_flight.contains(input.1.get_Some_0())
            &&& result(input, s).0.is_Enabled()
            &&& result(input, s).1.is_Enabled()
        },
        transition: |input: (Option<Message>, Option<ExternalComm<E::Input, E::Output>>, Option<ObjectRef>), s: Self| {
            let (host_result, network_result) = result(input, s);
            (Self {
                controller_state: host_result.get_Enabled_0(),
                network_state: network_result.get_Enabled_0(),
                rest_id_allocator: host_result.get_Enabled_1().rest_id_allocator,
                external_api_state: Self::external_api_send_output_and_receive_input(input.1, host_result.get_Enabled_1().external_api_input, s.external_api_state),
                ..s
            }, ())
        },
    }
}

/// This action checks whether a custom resource exists in the Kubernetes API and if so schedule a controller
/// reconcile for it. It is used to set up the assumption for liveness proof: for a existing cr, the reconcile is
/// infinitely frequently invoked for it. The assumption that cr always exists and the weak fairness assumption on this
/// action allow us to prove reconcile is always eventually scheduled.
///
/// This action abstracts away a lot of implementation details in the Kubernetes API and kube framework,
/// such as the list-then-watch pattern.
///
/// In general, this action assumes the following key behavior:
/// (1) The kube library always invokes `reconcile_with` (defined in the shim layer) whenever a cr object gets created
///   -- so the first creation event will schedule a reconcile
/// (2) The shim layer always re-queues `reconcile_with` unless the corresponding cr object does not exist,
/// and the kube library always eventually invokes the re-queued `reconcile_with`
///   -- so as long as the cr still exists, the reconcile will still be scheduled over and over again
/// (3) The shim layer always performs a quorum read to etcd to get the cr object and passes it to `reconcile_core`
///   -- so the reconcile is scheduled with the most recent view of the cr object when this action happens
/// (4) The shim layer never invokes `reconcile_core` if the cr object does not exist
///   -- this is not assumed by `schedule_controller_reconcile` because it never talks about what should happen if the
///   cr object does not exist, but it is still important because `schedule_controller_reconcile` is the only
///   action that can schedule a reconcile in our state machine.
pub open spec fn schedule_controller_reconcile() -> Action<Self, ObjectRef, ()> {
    Action {
        precondition: |input: ObjectRef, s: Self| {
            &&& s.resource_key_exists(input)
            &&& input.kind.is_CustomResourceKind()
            &&& K::from_dynamic_object(s.resource_obj_of(input)).is_Ok()
        },
        transition: |input: ObjectRef, s: Self| {
            (Self {
                controller_state: ControllerState {
                    scheduled_reconciles: s.controller_state.scheduled_reconciles.insert(input, K::from_dynamic_object(s.resource_obj_of(input)).get_Ok_0()),
                    ..s.controller_state
                },
                ..s
            }, ())
        }
    }
}

/// This action restarts the crashed controller.
pub open spec fn restart_controller() -> Action<Self, (), ()> {
    Action {
        precondition: |input: (), s: Self| {
            s.crash_enabled
        },
        transition: |input: (), s: Self| {
            (Self {
                controller_state: Self::init_controller_state(),
                ..s
            }, ())
        },
    }
}

/// This action disallows the controller to crash from this point.
/// This is used to constraint the crash behavior for liveness proof:
/// the controller eventually stops crashing.
pub open spec fn disable_crash() -> Action<Self, (), ()> {
    Action {
        precondition: |input: (), s: Self| {
            true
        },
        transition: |input: (), s: Self| {
            (Self {
                crash_enabled: false,
                ..s
            }, ())
        },
    }
}

pub open spec fn busy_kubernetes_api_rejects_request() -> Action<Self, Option<Message>, ()> {
    let network_result = |input: Option<Message>, s: Self| {
        let req_msg = input.get_Some_0();
        let resp = form_matched_resp_msg(req_msg, Result::Err(APIError::ServerTimeout));
        let msg_ops = MessageOps {
            recv: input,
            send: Multiset::singleton(resp),
        };
        let result = Self::network().next_result(msg_ops, s.network_state);
        result
    };
    Action {
        precondition: |input: Option<Message>, s: Self| {
            &&& s.busy_enabled
            &&& input.is_Some()
            &&& input.get_Some_0().content.is_APIRequest()
            &&& network_result(input, s).is_Enabled()
        },
        transition: |input: Option<Message>, s: Self| {
            (Self {
                network_state: network_result(input, s).get_Enabled_0(),
                ..s
            }, ())
        }
    }
}

/// This action disallows the Kubernetes API to be busy from this point.
/// This is used to constraint the transient error of Kubernetes APIs for liveness proof:
/// the requests from the controller eventually stop being rejected by transient error.
pub open spec fn disable_busy() -> Action<Self, (), ()> {
    Action {
        precondition: |input:(), s: Self| {
            true
        },
        transition: |input: (), s: Self| {
            (Self {
                busy_enabled: false,
                ..s
            }, ())
        }
    }
}

pub open spec fn client_next() -> Action<Self, (Option<Message>, K), ()> {
    let result = |input: (Option<Message>, K), s: Self| {
        let host_result = Self::client().next_result(
            ClientActionInput{recv: input.0, cr: input.1, rest_id_allocator: s.rest_id_allocator},
            s.client_state
        );
        let msg_ops = MessageOps {
            recv: input.0,
            send: host_result.get_Enabled_1().0,
        };
        let network_result = Self::network().next_result(msg_ops, s.network_state);

        (host_result, network_result)
    };
    Action {
        precondition: |input: (Option<Message>, K), s: Self| {
            &&& received_msg_destined_for(input.0, HostId::Client)
            &&& result(input, s).0.is_Enabled()
            &&& result(input, s).1.is_Enabled()
        },
        transition: |input: (Option<Message>, K), s: Self| {
            (Self {
                client_state: result(input, s).0.get_Enabled_0(),
                network_state: result(input, s).1.get_Enabled_0(),
                rest_id_allocator: result(input, s).0.get_Enabled_1().1,
                ..s
            }, ())
        },
    }
}

pub open spec fn stutter() -> Action<Self, (), ()> {
    Action {
        precondition: |input: (), s: Self| {
            true
        },
        transition: |input: (), s: Self| {
            (s, ())
        },
    }
}

pub open spec fn next_step(s: Self, s_prime: Self, step: Step<K, E>) -> bool {
    match step {
        Step::KubernetesAPIStep(input) => Self::kubernetes_api_next().forward(input)(s, s_prime),
        Step::ControllerStep(input) => Self::controller_next().forward(input)(s, s_prime),
        Step::ClientStep(input) => Self::client_next().forward(input)(s, s_prime),
        Step::ExternalAPIStep(input) => Self::external_api_next().forward(input)(s, s_prime),
        Step::ScheduleControllerReconcileStep(input) => Self::schedule_controller_reconcile().forward(input)(s, s_prime),
        Step::RestartController() => Self::restart_controller().forward(())(s, s_prime),
        Step::DisableCrash() => Self::disable_crash().forward(())(s, s_prime),
        Step::KubernetesBusy(input) => Self::busy_kubernetes_api_rejects_request().forward(input)(s, s_prime),
        Step::DisableBusy() => Self::disable_busy().forward(())(s, s_prime),
        Step::StutterStep() => Self::stutter().forward(())(s, s_prime),
    }
}

/// `next` chooses:
/// * which host to take the next action (`Step`)
/// * whether to deliver a message and which message to deliver (`Option<Message>` in `Step`)
pub open spec fn next() -> ActionPred<Self> {
    |s: Self, s_prime: Self| exists |step: Step<K, E>| Self::next_step(s, s_prime, step)
}

/// We install the reconciler to the Kubernetes cluster state machine spec
/// TODO: develop a struct for the compound state machine and make reconciler its member
/// so that we don't have to pass reconciler to init and next in the proof.
pub open spec fn sm_spec() -> TempPred<Self> {
    lift_state(Self::init()).and(Self::sm_partial_spec())
}

pub open spec fn sm_partial_spec() -> TempPred<Self> {
    always(lift_action(Self::next()))
    .and(tla_forall(|input| Self::kubernetes_api_next().weak_fairness(input)))
    .and(tla_forall(|input| Self::controller_next().weak_fairness(input)))
    .and(tla_forall(|input| Self::external_api_next().weak_fairness(input)))
    .and(tla_forall(|input| Self::schedule_controller_reconcile().weak_fairness(input)))
    .and(Self::disable_crash().weak_fairness(()))
    .and(Self::disable_busy().weak_fairness(()))
}

pub open spec fn kubernetes_api_action_pre(action: KubernetesAPIAction, input: Option<Message>) -> StatePred<Self> {
    |s: Self| {
        let host_result = Self::kubernetes_api().next_action_result(
            action,
            KubernetesAPIActionInput{recv: input, rest_id_allocator: s.rest_id_allocator},
            s.kubernetes_api_state
        );
        let msg_ops = MessageOps {
            recv: input,
            send: host_result.get_Enabled_1().0,
        };
        let network_result = Self::network().next_result(msg_ops, s.network_state);

        &&& received_msg_destined_for(input, HostId::KubernetesAPI)
        &&& host_result.is_Enabled()
        &&& network_result.is_Enabled()
    }
}

pub open spec fn controller_action_pre(action: ControllerAction<K, E, R>, input: (Option<Message>, Option<ExternalComm<E::Input, E::Output>>, Option<ObjectRef>)) -> StatePred<Self> {
    |s: Self| {
        let host_result = Self::controller().next_action_result(
            action,
            ControllerActionInput{recv: input.0, external_api_output: input.1, scheduled_cr_key: input.2, rest_id_allocator: s.rest_id_allocator},
            s.controller_state
        );
        let msg_ops = MessageOps {
            recv: input.0,
            send: host_result.get_Enabled_1().send,
        };
        let network_result = Self::network().next_result(msg_ops, s.network_state);

        &&& received_msg_destined_for(input.0, HostId::CustomController)
        &&& input.1.is_Some() ==> s.external_api_state.in_flight.contains(input.1.get_Some_0())
        &&& host_result.is_Enabled()
        &&& network_result.is_Enabled()
    }
}

pub open spec fn crash_disabled() -> StatePred<Self> {
    |s: Self| !s.crash_enabled
}

pub open spec fn busy_disabled() -> StatePred<Self> {
    |s: Self| !s.busy_enabled
}

pub open spec fn rest_id_counter_is(rest_id: nat) -> StatePred<Self> {
    |s: Self| s.rest_id_allocator.rest_id_counter == rest_id
}

pub open spec fn rest_id_counter_is_no_smaller_than(rest_id: nat) -> StatePred<Self> {
    |s: Self| s.rest_id_allocator.rest_id_counter >= rest_id
}

}

}
