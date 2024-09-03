// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster_v2::spec::{
    api_server::state_machine::api_server, api_server::types::*,
    builtin_controllers::state_machine::builtin_controllers, builtin_controllers::types::*,
    controller::state_machine::controller, controller::types::*, external::state_machine::external,
    external::types::*, message::*, network::state_machine::network, network::types::*,
};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct ClusterState {
    pub api_server: ApiServerState,
    pub controller_and_externals: Map<int, ControllerAndExternalState>,
    pub network: NetworkState,
    pub rest_id_allocator: RestIdAllocator,
    pub crash_enabled: bool,
    pub transient_failure_enabled: bool,
}

pub struct ControllerAndExternalState {
    pub controller: ControllerState,
    pub external: Option<ExternalState>,
}

impl ClusterState {
    #[verifier(inline)]
    pub open spec fn in_flight(self) -> Multiset<Message> {
        self.network.in_flight
    }

    #[verifier(inline)]
    pub open spec fn resources(self) -> StoredState {
        self.api_server.resources
    }

    #[verifier(inline)]
    pub open spec fn ongoing_reconciles(self, key: int) -> Map<ObjectRef, OngoingReconcile> {
        self.controller_and_externals[key].controller.ongoing_reconciles
    }

    #[verifier(inline)]
    pub open spec fn scheduled_reconciles(self, key: int) -> Map<ObjectRef, DynamicObjectView> {
        self.controller_and_externals[key].controller.scheduled_reconciles
    }

    pub open spec fn has_rest_id_counter_no_smaller_than(self, rest_id: nat) -> bool {
        self.rest_id_allocator.rest_id_counter >= rest_id
    }
}

// #[is_variant]
// pub enum Step {
//     ApiServerStep(Option<Message>),
//     BuiltinControllersStep((BuiltinControllerChoice, ObjectRef)),
//     ControllerStep((Option<Message>, Option<ObjectRef>)),
//     ClientStep(),
//     ExternalAPIStep(Option<Message>),
//     ScheduleControllerReconcileStep(ObjectRef),
//     RestartController(),
//     DisableCrash(),
//     FailTransientlyStep((Message, APIError)),
//     DisableTransientFailure(),
//     StutterStep(),
// }

pub struct Cluster {
    pub installed_types: InstalledTypes,
    pub controller_models: Map<int, ControllerModel>,
}

pub struct ControllerModel {
    pub cr_kind: Kind,
    pub reconcile_model: ReconcileModel,
    pub external_model: Option<ExternalModel>,
}

impl Cluster {

    pub open spec fn init(self) -> StatePred<ClusterState> {
        |s: ClusterState| {
            &&& (api_server(self.installed_types).init)(s.api_server)
            &&& (builtin_controllers().init)(s.api_server)
            &&& (network().init)(s.network)
            &&& s.crash_enabled
            &&& s.transient_failure_enabled
            &&& forall |key| self.controller_models.contains_key(key)
                ==> {
                    let model = self.controller_models[key];
                    &&& s.controller_and_externals.contains_key(key)
                    &&& (controller(model.cr_kind, model.reconcile_model).init)(s.controller_and_externals[key].controller)
                    &&& model.external_model.is_Some()
                        ==> {
                            &&& s.controller_and_externals[key].external.is_Some()
                            &&& (external(model.external_model.get_Some_0()).init)(s.controller_and_externals[key].external.get_Some_0())
                        }
                }
        }
    }

    /// api_server_next models the behavior that the Kubernetes API server (and its backend, a key-value store)
    /// handles one request from some client or controller that gets/lists/creates/updates/deletes some object(s).
    /// Handling each create/update/delete request will potentially change the objects stored in the key-value store
    /// (etcd by default).
    /// The persistent state stored in the key-value store is modeled as a Map.
    pub open spec fn api_server_next(self) -> Action<ClusterState, Option<Message>, ()> {
        let result = |input: Option<Message>, s: ClusterState| {
            let host_result = api_server(self.installed_types).next_result(
                ApiServerActionInput{ recv: input },
                s.api_server
            );
            let msg_ops = MessageOps {
                recv: input,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            (host_result, network_result)
        };
        Action {
            precondition: |input: Option<Message>, s: ClusterState| {
                &&& received_msg_destined_for(input, HostId::ApiServer)
                &&& result(input, s).0.is_Enabled()
                &&& result(input, s).1.is_Enabled()
            },
            transition: |input: Option<Message>, s: ClusterState| {
                let (host_result, network_result) = result(input, s);
                (ClusterState {
                    api_server: host_result.get_Enabled_0(),
                    network: network_result.get_Enabled_0(),
                    ..s
                }, ())
            },
        }
    }
}


// /// builtin_controllers_next models the behavior that one of the built-in controllers reconciles one object.
// /// The cluster state machine chooses which built-in controller to run and which object to reconcile.
// /// The behavior of each built-in controller is modeled as a function that takes the current cluster state
// /// (objects stored in the key-value store) and returns request(s) to update the cluster state.
// pub open spec fn builtin_controllers_next() -> Action<Self, (BuiltinControllerChoice, ObjectRef), ()> {
//     let result = |input: (BuiltinControllerChoice, ObjectRef), s: Self| {
//         let host_result = Self::builtin_controllers().next_result(
//             BuiltinControllersActionInput {
//                 choice: input.0,
//                 key: input.1,
//                 rest_id_allocator: s.rest_id_allocator,
//             },
//             s.api_server
//         );
//         let msg_ops = MessageOps {
//             recv: None,
//             send: host_result.get_Enabled_1().send,
//         };
//         let network_result = Self::network().next_result(msg_ops, s.network);

//         (host_result, network_result)
//     };
//     Action {
//         precondition: |input: (BuiltinControllerChoice, ObjectRef), s: Self| {
//             &&& result(input, s).0.is_Enabled()
//             &&& result(input, s).1.is_Enabled()
//         },
//         transition: |input: (BuiltinControllerChoice, ObjectRef), s: Self| {
//             let (host_result, network_result) = result(input, s);
//             (Self {
//                 api_server: host_result.get_Enabled_0(),
//                 network: network_result.get_Enabled_0(),
//                 rest_id_allocator: host_result.get_Enabled_1().rest_id_allocator,
//                 ..s
//             }, ())
//         },
//     }
// }

// /// external_api_next models the behavior of some external system that handles the requests from the controller.
// /// It behaves in a very similar way to the Kubernetes API by interacting with the controller via RPC.
// /// It delivers an external request message to the external system, runs E::transition, and puts the response message
// /// into the network.
// pub open spec fn external_api_next() -> Action<Self, Option<Message>, ()> {
//     let result = |input: Option<Message>, s: Self| {
//         let host_result = Self::external_api().next_result(
//             ExternalAPIActionInput {
//                 recv: input,
//                 resources: s.api_server.resources,
//             },
//             s.external_api_state
//         );
//         let msg_ops = MessageOps {
//             recv: input,
//             send: host_result.get_Enabled_1().send,
//         };
//         let network_result = Self::network().next_result(msg_ops, s.network);

//         (host_result, network_result)
//     };
//     Action {
//         precondition: |input: Option<Message>, s: Self| {
//             &&& received_msg_destined_for(input, HostId::ExternalAPI)
//             &&& result(input, s).0.is_Enabled()
//             &&& result(input, s).1.is_Enabled()
//         },
//         transition: |input: Option<Message>, s: Self| {
//             let (host_result, network_result) = result(input, s);
//             (Self {
//                 external_api_state: host_result.get_Enabled_0(),
//                 network: network_result.get_Enabled_0(),
//                 ..s
//             }, ())
//         },
//     }
// }

// pub open spec fn controller_next() -> Action<Self, (Option<Message>, Option<ObjectRef>), ()> {
//     let result = |input: (Option<Message>, Option<ObjectRef>), s: Self| {
//         let host_result = Self::controller().next_result(
//             ControllerActionInput{recv: input.0, scheduled_cr_key: input.1, rest_id_allocator: s.rest_id_allocator},
//             s.controller_state
//         );
//         let msg_ops = MessageOps {
//             recv: input.0,
//             send: host_result.get_Enabled_1().send,
//         };
//         let network_result = Self::network().next_result(msg_ops, s.network);

//         (host_result, network_result)
//     };
//     Action {
//         precondition: |input: (Option<Message>, Option<ObjectRef>), s: Self| {
//             &&& received_msg_destined_for(input.0, HostId::CustomController)
//             &&& result(input, s).0.is_Enabled()
//             &&& result(input, s).1.is_Enabled()
//         },
//         transition: |input: (Option<Message>, Option<ObjectRef>), s: Self| {
//             let (host_result, network_result) = result(input, s);
//             (Self {
//                 controller_state: host_result.get_Enabled_0(),
//                 network: network_result.get_Enabled_0(),
//                 rest_id_allocator: host_result.get_Enabled_1().rest_id_allocator,
//                 ..s
//             }, ())
//         },
//     }
// }

// /// This action checks whether a custom resource exists in the Kubernetes API and if so schedule a controller
// /// reconcile for it. It is used to set up the assumption for liveness proof: for a existing cr, the reconcile is
// /// infinitely frequently invoked for it. The assumption that cr always exists and the weak fairness assumption on this
// /// action allow us to prove reconcile is always eventually scheduled.
// ///
// /// This action abstracts away a lot of implementation details in the Kubernetes API and kube framework,
// /// such as the list-then-watch pattern.
// ///
// /// In general, this action assumes the following key behavior:
// /// (1) The kube library always invokes `reconcile_with` (defined in the shim layer) whenever a cr object gets created
// ///   -- so the first creation event will schedule a reconcile
// /// (2) The shim layer always re-queues `reconcile_with` unless the corresponding cr object does not exist,
// /// and the kube library always eventually invokes the re-queued `reconcile_with`
// ///   -- so as long as the cr still exists, the reconcile will still be scheduled over and over again
// /// (3) The shim layer always performs a quorum read to etcd to get the cr object and passes it to `reconcile_core`
// ///   -- so the reconcile is scheduled with the most recent view of the cr object when this action happens
// /// (4) The shim layer never invokes `reconcile_core` if the cr object does not exist
// ///   -- this is not assumed by `schedule_controller_reconcile` because it never talks about what should happen if the
// ///   cr object does not exist, but it is still important because `schedule_controller_reconcile` is the only
// ///   action that can schedule a reconcile in our state machine.
// pub open spec fn schedule_controller_reconcile() -> Action<Self, ObjectRef, ()> {
//     Action {
//         precondition: |input: ObjectRef, s: Self| {
//             &&& s.resources().contains_key(input)
//             &&& input.kind.is_CustomResourceKind()
//             &&& K::unmarshal(s.resources()[input]).is_Ok()
//         },
//         transition: |input: ObjectRef, s: Self| {
//             (Self {
//                 controller_state: ControllerState {
//                     scheduled_reconciles: s.controller_state.scheduled_reconciles.insert(input, K::unmarshal(s.resources()[input]).get_Ok_0()),
//                     ..s.controller_state
//                 },
//                 ..s
//             }, ())
//         }
//     }
// }

// /// This action restarts the crashed controller.
// pub open spec fn restart_controller() -> Action<Self, (), ()> {
//     Action {
//         precondition: |input: (), s: Self| {
//             s.crash_enabled
//         },
//         transition: |input: (), s: Self| {
//             (Self {
//                 controller_state: Self::init_controller_state(),
//                 ..s
//             }, ())
//         },
//     }
// }

// /// This action disallows the controller to crash from this point.
// /// This is used to constraint the crash behavior for liveness proof:
// /// the controller eventually stops crashing.
// pub open spec fn disable_crash() -> Action<Self, (), ()> {
//     Action {
//         precondition: |input: (), s: Self| {
//             true
//         },
//         transition: |input: (), s: Self| {
//             (Self {
//                 crash_enabled: false,
//                 ..s
//             }, ())
//         },
//     }
// }

// /// This action fails a request sent to the Kubernetes API in a transient way:
// /// the request fails with timeout error or conflict error (caused by resource version conflicts).
// pub open spec fn fail_request_transiently() -> Action<Self, (Message, APIError), ()> {
//     let result = |input: (Message, APIError), s: Self| {
//         let req_msg = input.0;
//         let api_err = input.1;
//         let resp = Message::form_matched_err_resp_msg(req_msg, api_err);
//         let msg_ops = MessageOps {
//             recv: Some(req_msg),
//             send: Multiset::singleton(resp),
//         };
//         let result = Self::network().next_result(msg_ops, s.network);
//         result
//     };
//     Action {
//         precondition: |input: (Message, APIError), s: Self| {
//             let req_msg = input.0;
//             let api_err = input.1;
//             &&& s.transient_failure_enabled
//             &&& req_msg.dst.is_ApiServer()
//             &&& req_msg.content.is_APIRequest()
//             &&& (api_err.is_Timeout() || api_err.is_ServerTimeout() || api_err.is_Conflict())
//             &&& result(input, s).is_Enabled()
//         },
//         transition: |input: (Message, APIError), s: Self| {
//             (Self {
//                 network: result(input, s).get_Enabled_0(),
//                 ..s
//             }, ())
//         }
//     }
// }

// /// This action disallows the Kubernetes API to have transient failure from this point.
// /// This is used to constraint the transient error of Kubernetes APIs for liveness proof:
// /// the requests from the controller eventually stop being rejected by transient error.
// pub open spec fn disable_transient_failure() -> Action<Self, (), ()> {
//     Action {
//         precondition: |input:(), s: Self| {
//             true
//         },
//         transition: |input: (), s: Self| {
//             (Self {
//                 transient_failure_enabled: false,
//                 ..s
//             }, ())
//         }
//     }
// }

// pub open spec fn stutter() -> Action<Self, (), ()> {
//     Action {
//         precondition: |input: (), s: Self| {
//             true
//         },
//         transition: |input: (), s: Self| {
//             (s, ())
//         },
//     }
// }

// pub open spec fn next_step(s: Self, s_prime: Self, step: Step<Message>) -> bool {
//     match step {
//         Step::ApiServerStep(input) => Self::api_server_next().forward(input)(s, s_prime),
//         Step::BuiltinControllersStep(input) => Self::builtin_controllers_next().forward(input)(s, s_prime),
//         Step::ControllerStep(input) => Self::controller_next().forward(input)(s, s_prime),
//         Step::ClientStep() => Self::client_next().forward(())(s, s_prime),
//         Step::ExternalAPIStep(input) => Self::external_api_next().forward(input)(s, s_prime),
//         Step::ScheduleControllerReconcileStep(input) => Self::schedule_controller_reconcile().forward(input)(s, s_prime),
//         Step::RestartController() => Self::restart_controller().forward(())(s, s_prime),
//         Step::DisableCrash() => Self::disable_crash().forward(())(s, s_prime),
//         Step::FailTransientlyStep(input) => Self::fail_request_transiently().forward(input)(s, s_prime),
//         Step::DisableTransientFailure() => Self::disable_transient_failure().forward(())(s, s_prime),
//         Step::StutterStep() => Self::stutter().forward(())(s, s_prime),
//     }
// }

// /// `next` chooses:
// /// * which host to take the next action (`Step`)
// /// * what input to feed to the chosen action
// pub open spec fn next() -> ActionPred<Self> {
//     |s: Self, s_prime: Self| exists |step: Step<Message>| Self::next_step(s, s_prime, step)
// }

// pub open spec fn sm_spec() -> TempPred<Self> {
//     lift_state(Self::init()).and(always(lift_action(Self::next()))).and(Self::sm_wf_spec())
// }

// pub open spec fn sm_wf_spec() -> TempPred<Self> {
//     tla_forall(|input| Self::api_server_next().weak_fairness(input))
//     .and(tla_forall(|input| Self::builtin_controllers_next().weak_fairness(input)))
//     .and(tla_forall(|input| Self::controller_next().weak_fairness(input)))
//     .and(tla_forall(|input| Self::external_api_next().weak_fairness(input)))
//     .and(tla_forall(|input| Self::schedule_controller_reconcile().weak_fairness(input)))
//     .and(Self::disable_crash().weak_fairness(()))
//     .and(Self::disable_transient_failure().weak_fairness(()))
// }

// pub open spec fn api_server_action_pre(action: ApiServerAction<E::Input, E::Output>, input: Option<Message>) -> StatePred<Self> {
//     |s: Self| {
//         let host_result = Self::api_server().next_action_result(
//             action,
//             ApiServerActionInput{recv: input},
//             s.api_server
//         );
//         let msg_ops = MessageOps {
//             recv: input,
//             send: host_result.get_Enabled_1().send,
//         };
//         let network_result = Self::network().next_result(msg_ops, s.network);

//         &&& received_msg_destined_for(input, HostId::ApiServer)
//         &&& host_result.is_Enabled()
//         &&& network_result.is_Enabled()
//     }
// }

// pub open spec fn external_api_action_pre(action: ExternalAPIAction<E>, input: Option<Message>) -> StatePred<Self> {
//     |s: Self| {
//         let host_result = Self::external_api().next_action_result(
//             action,
//             ExternalAPIActionInput{recv: input, resources: s.api_server.resources},
//             s.external_api_state
//         );
//         let msg_ops = MessageOps {
//             recv: input,
//             send: host_result.get_Enabled_1().send,
//         };
//         let network_result = Self::network().next_result(msg_ops, s.network);

//         &&& received_msg_destined_for(input, HostId::ExternalAPI)
//         &&& host_result.is_Enabled()
//         &&& network_result.is_Enabled()
//     }
// }

// pub open spec fn builtin_controllers_action_pre(action: BuiltinControllersAction<E::Input, E::Output>, input: (BuiltinControllerChoice, ObjectRef)) -> StatePred<Self> {
//     |s: Self| {
//         let host_result = Self::builtin_controllers().next_action_result(
//             action,
//             BuiltinControllersActionInput{
//                 choice: input.0,
//                 key: input.1,
//                 rest_id_allocator: s.rest_id_allocator
//             },
//             s.api_server
//         );
//         let msg_ops = MessageOps {
//             recv: None,
//             send: host_result.get_Enabled_1().send,
//         };
//         let network_result = Self::network().next_result(msg_ops, s.network);

//         &&& host_result.is_Enabled()
//         &&& network_result.is_Enabled()
//     }
// }

// pub open spec fn controller_action_pre(action: ControllerAction, input: (Option<Message>, Option<ObjectRef>)) -> StatePred<Self> {
//     |s: Self| {
//         let host_result = Self::controller().next_action_result(
//             action,
//             ControllerActionInput{recv: input.0, scheduled_cr_key: input.1, rest_id_allocator: s.rest_id_allocator},
//             s.controller_state
//         );
//         let msg_ops = MessageOps {
//             recv: input.0,
//             send: host_result.get_Enabled_1().send,
//         };
//         let network_result = Self::network().next_result(msg_ops, s.network);

//         &&& received_msg_destined_for(input.0, HostId::CustomController)
//         &&& host_result.is_Enabled()
//         &&& network_result.is_Enabled()
//     }
// }

// pub open spec fn crash_disabled() -> StatePred<Self> {
//     |s: Self| !s.crash_enabled
// }

// // TODO: rename it!
// pub open spec fn busy_disabled() -> StatePred<Self> {
//     |s: Self| !s.transient_failure_enabled
// }

// pub open spec fn rest_id_counter_is(rest_id: nat) -> StatePred<Self> {
//     |s: Self| s.rest_id_allocator.rest_id_counter == rest_id
// }

// pub open spec fn rest_id_counter_is_no_smaller_than(rest_id: nat) -> StatePred<Self> {
//     |s: Self| s.rest_id_allocator.rest_id_counter >= rest_id
// }

}
