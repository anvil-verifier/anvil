// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::v2::kubernetes_cluster::spec::{
    api_server::state_machine::api_server,
    api_server::types::*,
    builtin_controllers::state_machine::builtin_controllers,
    builtin_controllers::types::*,
    controller::state_machine::{controller, init_controller_state},
    controller::types::*,
    external::state_machine::external,
    external::types::*,
    message::*,
    network::state_machine::network,
    network::types::*,
};
use vstd::{multiset::*, prelude::*};

verus! {

// The ClusterState includes the state of the api_server (including the key-value store),
// the states of each controller running in the cluster (and the associated external system if exists),
// the state of the network (the pending messages).
// It also has a global rpc_id_allocator that assign a unique id to each RPC call,
// and a req_drop_enabled to enable/disable network message drop.
pub struct ClusterState {
    pub api_server: APIServerState,
    pub controller_and_externals: Map<int, ControllerAndExternalState>,
    pub network: NetworkState,
    pub rpc_id_allocator: RPCIdAllocator,
    pub req_drop_enabled: bool,
}

// The ControllerAndExternalState includes the controller's internal state,
// the associated external system's state (if exists).
// It also has a crash_enabled that to enable/disable controller crash.
pub struct ControllerAndExternalState {
    pub controller: ControllerState,
    pub external: Option<ExternalState>,
    pub crash_enabled: bool,
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

    pub open spec fn has_rpc_id_counter_no_smaller_than(self, rpc_id: nat) -> bool {
        self.rpc_id_allocator.rpc_id_counter >= rpc_id
    }
}

pub open spec fn crash_disabled(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| !s.controller_and_externals[controller_id].crash_enabled
}

pub open spec fn req_drop_disable() -> StatePred<ClusterState> {
    |s: ClusterState| !s.req_drop_enabled
}

pub open spec fn rpc_id_counter_is(rpc_id: nat) -> StatePred<ClusterState> {
    |s: ClusterState| s.rpc_id_allocator.rpc_id_counter == rpc_id
}

pub open spec fn rpc_id_counter_is_no_smaller_than(rpc_id: nat) -> StatePred<ClusterState> {
    |s: ClusterState| s.rpc_id_allocator.rpc_id_counter >= rpc_id
}

#[is_variant]
pub enum Step {
    APIServerStep(Option<Message>),
    BuiltinControllersStep((BuiltinControllerChoice, ObjectRef)),
    ControllerStep((int, Option<Message>, Option<ObjectRef>)),
    ScheduleControllerReconcileStep((int, ObjectRef)),
    RestartControllerStep(int),
    DisableCrashStep(int),
    DropReqStep((Message, APIError)),
    DisableReqDropStep(),
    ExternalStep((int, Option<Message>)),
    StutterStep(),
}

// The Cluster is customized by the custom resource types installed
// and the controllers running in the cluster.
pub struct Cluster {
    pub installed_types: InstalledTypes,
    pub controller_models: Map<int, ControllerModel>,
}

// The ControllerModel includes the reconcile_model that models
// the controller's reconciliation behavior, and the model of
// the external system (if exists).
pub struct ControllerModel {
    pub reconcile_model: ReconcileModel,
    pub external_model: Option<ExternalModel>,
}

// We implement a state machine for each cluster.
// This state machine is a compound state machine that consists of
// host state machines for API server and controllers.
impl Cluster {
    // The init defines the initial state of the state machine.
    pub open spec fn init(self) -> StatePred<ClusterState> {
        |s: ClusterState| {
            // The API server is initialized...
            &&& (api_server(self.installed_types).init)(s.api_server)
            // and the built-in controllers are initialized...
            &&& (builtin_controllers().init)(())
            // and the network is initialized...
            &&& (network().init)(s.network)
            // and message drop is enabled...
            &&& s.req_drop_enabled
            // and for each controller...
            &&& forall |key| self.controller_models.contains_key(key)
                ==> {
                    let model = self.controller_models[key];
                    // its internal state exists...
                    &&& s.controller_and_externals.contains_key(key)
                    // and is initialized...
                    &&& (controller(model.reconcile_model, key).init)(s.controller_and_externals[key].controller)
                    // and crash for this controller is enabled...
                    &&& s.controller_and_externals[key].crash_enabled
                    // and if the controller has an associated external system...
                    &&& model.external_model.is_Some()
                        ==> {
                            // the internal state of that external system exists...
                            &&& s.controller_and_externals[key].external.is_Some()
                            // and is initialized.
                            &&& (external(model.external_model.get_Some_0()).init)(s.controller_and_externals[key].external.get_Some_0())
                        }
                }
        }
    }

    // The next defines the transition of the state machine.
    // In each step, it chooses:
    // (1) which host to take the action
    // (2) and what input to feed to the chosen action.
    pub open spec fn next(self) -> ActionPred<ClusterState> {
        |s, s_prime: ClusterState| exists |step: Step| self.next_step(s, s_prime, step)
    }

    // The next_step takes the step chosen by next and runs the corresponding step.
    pub open spec fn next_step(self, s: ClusterState, s_prime: ClusterState, step: Step) -> bool {
        match step {
            Step::APIServerStep(input) => self.api_server_next().forward(input)(s, s_prime),
            Step::BuiltinControllersStep(input) => self.builtin_controllers_next().forward(input)(s, s_prime),
            Step::ControllerStep(input) => self.controller_next().forward(input)(s, s_prime),
            Step::ScheduleControllerReconcileStep(input) => self.schedule_controller_reconcile().forward(input)(s, s_prime),
            Step::RestartControllerStep(input) => self.restart_controller().forward(input)(s, s_prime),
            Step::DisableCrashStep(input) => self.disable_crash().forward(input)(s, s_prime),
            Step::DropReqStep(input) => self.drop_req().forward(input)(s, s_prime),
            Step::DisableReqDropStep() => self.disable_req_drop().forward(())(s, s_prime),
            Step::ExternalStep(input) => self.external_next().forward(input)(s, s_prime),
            Step::StutterStep() => self.stutter().forward(())(s, s_prime),
        }
    }

    // The api_server_next models the Kubernetes API server and its backend, a key-value store.
    // It handles one request from some controller that gets/lists/creates/updates/deletes some object(s).
    // The Kubernetes cluster state stored in the key-value store is modeled as a Map called resources.
    pub open spec fn api_server_next(self) -> Action<ClusterState, Option<Message>, ()> {
        let result = |input: Option<Message>, s: ClusterState| {
            let host_result = self.api_server().next_result(
                APIServerActionInput{ recv: input },
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
                &&& received_msg_destined_for(input, HostId::APIServer)
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

    // The builtin_controllers_next models the built-in controllers that come with Kubernetes.
    // For now, it only models the garbage collector.
    // To keep things simple, instead of modeling how the built-in controllers sends get/list
    // requests to read the cluster state, the Kubernetes cluster state (i.e., resources) is
    // directly passed to the built-in controller.
    pub open spec fn builtin_controllers_next(self) -> Action<ClusterState, (BuiltinControllerChoice, ObjectRef), ()> {
        let result = |input: (BuiltinControllerChoice, ObjectRef), s: ClusterState| {
            let host_result = self.builtin_controllers().next_result(
                BuiltinControllersActionInput {
                    choice: input.0,
                    key: input.1,
                    rpc_id_allocator: s.rpc_id_allocator,
                    resources: s.api_server.resources,
                },
                ()
            );
            let msg_ops = MessageOps {
                recv: None,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            (host_result, network_result)
        };
        Action {
            precondition: |input: (BuiltinControllerChoice, ObjectRef), s: ClusterState| {
                &&& result(input, s).0.is_Enabled()
                &&& result(input, s).1.is_Enabled()
            },
            transition: |input: (BuiltinControllerChoice, ObjectRef), s: ClusterState| {
                let (host_result, network_result) = result(input, s);
                (ClusterState {
                    network: network_result.get_Enabled_0(),
                    rpc_id_allocator: host_result.get_Enabled_1().rpc_id_allocator,
                    ..s
                }, ())
            },
        }
    }

    // The controller_next models one controller that runs in the cluster.
    // It chooses one controller from controller_models and run it.
    pub open spec fn controller_next(self) -> Action<ClusterState, (int, Option<Message>, Option<ObjectRef>), ()> {
        Action {
            precondition: |input: (int, Option<Message>, Option<ObjectRef>), s: ClusterState| {
                let controller_id = input.0;
                let chosen_action = self.chosen_controller_next(controller_id);
                &&& self.controller_models.contains_key(input.0)
                &&& (chosen_action.precondition)((input.1, input.2), s)
            },
            transition: |input: (int, Option<Message>, Option<ObjectRef>), s: ClusterState| {
                let controller_id = input.0;
                let chosen_action = self.chosen_controller_next(controller_id);
                (chosen_action.transition)((input.1, input.2), s)
            },
        }
    }

    // The chosen_controller_next is called by controller_next.
    // It models the controller that is indexed by controller_id.
    pub open spec fn chosen_controller_next(self, controller_id: int) -> Action<ClusterState, (Option<Message>, Option<ObjectRef>), ()> {
        let result = |input: (Option<Message>, Option<ObjectRef>), s: ClusterState| {
            let host_result = self.controller(controller_id).next_result(
                ControllerActionInput{recv: input.0, scheduled_cr_key: input.1, rpc_id_allocator: s.rpc_id_allocator},
                s.controller_and_externals[controller_id].controller
            );
            let msg_ops = MessageOps {
                recv: input.0,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            (host_result, network_result)
        };
        Action {
            precondition: |input: (Option<Message>, Option<ObjectRef>), s: ClusterState| {
                &&& received_msg_destined_for(input.0, HostId::Controller(controller_id))
                &&& result(input, s).0.is_Enabled()
                &&& result(input, s).1.is_Enabled()
            },
            transition: |input: (Option<Message>, Option<ObjectRef>), s: ClusterState| {
                let (host_result, network_result) = result(input, s);
                let controller_and_external_state_prime = ControllerAndExternalState {
                    controller: host_result.get_Enabled_0(),
                    ..s.controller_and_externals[controller_id]
                };
                (ClusterState {
                    controller_and_externals: s.controller_and_externals.insert(controller_id, controller_and_external_state_prime),
                    network: network_result.get_Enabled_0(),
                    rpc_id_allocator: host_result.get_Enabled_1().rpc_id_allocator,
                    ..s
                }, ())
            },
        }
    }

    // The schedule_controller_reconcile models how the controller shim layer
    // triggers a controller when the corresponding custom resource (cr) object exists.
    // For a particular controller in controller_models, it checks whether any
    // corresponding cr object exists and if so schedules the controller
    // to reconcile for that object.
    //
    // Applying weak fairness to this action gives an important assumption used in the ESR proof:
    // for any cr object, the controller will keep invoking the reconcile function
    // for it as long as the object still exists.
    // Note that this doesn't assume how frequent the controller invokes reconcile. It only says
    // that the controller "eventually" invokes reconcile again if the cr object still
    // exists, as stated by weak fairness.
    // This assumption, together with the premise of ESR that the cr object always exists,
    // gives an argument that the controller will keep invoking the reconcile function.
    //
    // The controller shim layer together with the underlying kube library does the following to
    // make the assumption hold:
    // (1) The kube library always invokes `reconcile_with` (defined in the shim layer) whenever
    // a cr object gets created
    //   -- so the first creation event will schedule a reconcile.
    // (2) The shim layer always re-queues `reconcile_with` unless the corresponding cr object
    // does not exist, and the kube library always eventually invokes the re-queued `reconcile_with`
    //   -- so as long as the cr still exists, the reconcile will still be scheduled over and over again.
    // (3) The shim layer always performs a quorum read to etcd to get the cr object and passes
    // it to `reconcile_core`
    //   -- so the reconcile is scheduled with the most recent view of the cr object when this action happens.
    // (4) The shim layer never invokes `reconcile_core` if the cr object does not exist
    //   -- this is not assumed by `schedule_controller_reconcile` because it never talks about what
    //   should happen if the cr object does not exist, but it is still important because
    //   `schedule_controller_reconcile` is the only action that can schedule a reconcile.
    pub open spec fn schedule_controller_reconcile(self) -> Action<ClusterState, (int, ObjectRef), ()> {
        Action {
            precondition: |input: (int, ObjectRef), s: ClusterState| {
                let controller_id = input.0;
                let object_key = input.1;
                &&& s.resources().contains_key(object_key)
                &&& self.controller_models.contains_key(controller_id)
                &&& object_key.kind == self.controller_models[controller_id].reconcile_model.kind
            },
            transition: |input: (int, ObjectRef), s: ClusterState| {
                let controller_id = input.0;
                let object_key = input.1;
                let controller_and_external_state = s.controller_and_externals[controller_id];
                let controller_and_external_state_prime = ControllerAndExternalState {
                    controller: ControllerState {
                        scheduled_reconciles: controller_and_external_state.controller.scheduled_reconciles.insert(object_key, s.resources()[object_key]),
                        ..controller_and_external_state.controller
                    },
                    ..controller_and_external_state
                };
                (ClusterState {
                    controller_and_externals: s.controller_and_externals.insert(controller_id, controller_and_external_state_prime),
                    ..s
                }, ())
            }
        }
    }

    // The restart_controller sets a controller's internal state back to the initial state.
    // This is used to model the controller crash failures -- in a real-world cluster, we
    // should expect that any controller might crash at any point due to external reasons
    // such as power failures, hardware failures or kernel failures, and might stay offline
    // for arbitrary long time before it restarts.
    //
    // An important simplification we make is that there is no "crash_controller" action.
    // We can model the controller crash failures without having a "crash_controller" action
    // because the behavior that a controller crashes at time t1 and then restarts at t2 (t2 > t1)
    // is equivalent to the behavior that a controller no longer gets scheduled from t1 and
    // then restarts at t2, as long as a crashed controller won't trigger new actions.
    // Note that weak fairness on the controller's action is not a problem here:
    // weak fairness only says that the controller eventually takes a step if it remains enabled,
    // so even with weak fairness the controller can still stay "offline" from t1 to t2.
    pub open spec fn restart_controller(self) -> Action<ClusterState, int, ()> {
        Action {
            precondition: |input: int, s: ClusterState| {
                let controller_id = input;
                &&& self.controller_models.contains_key(controller_id)
                &&& s.controller_and_externals[controller_id].crash_enabled
            },
            transition: |input: int, s: ClusterState| {
                let controller_id = input;
                let controller_and_external_state = s.controller_and_externals[controller_id];
                let controller_and_external_state_prime = ControllerAndExternalState {
                    controller: init_controller_state(),
                    ..controller_and_external_state
                };
                (ClusterState {
                    controller_and_externals: s.controller_and_externals.insert(controller_id, controller_and_external_state_prime),
                    ..s
                }, ())
            },
        }
    }

    // The disable_crash disables the controller crash failure for one controller
    // in controller_models.
    // This is used to constrain the crash behavior for proving liveness:
    // the controller eventually stops crashing.
    pub open spec fn disable_crash(self) -> Action<ClusterState, int, ()> {
        Action {
            precondition: |input: int, s: ClusterState| {
                let controller_id = input;
                self.controller_models.contains_key(controller_id)
            },
            transition: |input: int, s: ClusterState| {
                let controller_id = input;
                let controller_and_external_state = s.controller_and_externals[controller_id];
                let controller_and_external_state_prime = ControllerAndExternalState {
                    crash_enabled: false,
                    ..controller_and_external_state
                };
                (ClusterState {
                    controller_and_externals: s.controller_and_externals.insert(controller_id, controller_and_external_state_prime),
                    ..s
                }, ())
            },
        }
    }

    // The drop_req drops a request sent to the API server and results in a timeout error
    // to the sending controller. This is used to model network failures -- in a real-world
    // cluster, we should expect that a request sent by a controller doesn't arrive at the
    // API server due to various reasons including network configuration faults and
    // hardware or software faults in the networking stack.
    pub open spec fn drop_req(self) -> Action<ClusterState, (Message, APIError), ()> {
        let result = |input: (Message, APIError), s: ClusterState| {
            let req_msg = input.0;
            let api_err = input.1;
            let resp = Message::form_matched_err_resp_msg(req_msg, api_err);
            let msg_ops = MessageOps {
                recv: Some(req_msg),
                send: Multiset::singleton(resp),
            };
            let result = network().next_result(msg_ops, s.network);
            result
        };
        Action {
            precondition: |input: (Message, APIError), s: ClusterState| {
                let req_msg = input.0;
                let api_err = input.1;
                &&& s.req_drop_enabled
                &&& req_msg.dst.is_APIServer()
                &&& req_msg.content.is_APIRequest()
                &&& api_err.is_Timeout() || api_err.is_ServerTimeout()
                &&& result(input, s).is_Enabled()
            },
            transition: |input: (Message, APIError), s: ClusterState| {
                (ClusterState {
                    network: result(input, s).get_Enabled_0(),
                    ..s
                }, ())
            }
        }
    }

    // The disable_req_drop disables the network from dropping the request messages.
    // This is used to constrain the network failures for proving liveness:
    // the network eventually stops dropping request messages.
    pub open spec fn disable_req_drop(self) -> Action<ClusterState, (), ()> {
        Action {
            precondition: |input:(), s: ClusterState| {
                true
            },
            transition: |input: (), s: ClusterState| {
                (ClusterState {
                    req_drop_enabled: false,
                    ..s
                }, ())
            }
        }
    }

    // The external_next models the external system that a controller interacts with.
    // The modelling assumes that the interaction is based on RPC.
    // It chooses one external system from controller_models and run it.
    pub open spec fn external_next(self) -> Action<ClusterState, (int, Option<Message>), ()> {
        Action {
            precondition: |input: (int, Option<Message>), s: ClusterState| {
                let controller_id = input.0;
                let chosen_action = self.chosen_external_next(controller_id);
                &&& self.controller_models.contains_key(input.0)
                &&& self.controller_models[controller_id].external_model.is_Some()
                &&& (chosen_action.precondition)((input.1), s)
            },
            transition: |input: (int, Option<Message>), s: ClusterState| {
                let controller_id = input.0;
                let chosen_action = self.chosen_external_next(controller_id);
                (chosen_action.transition)((input.1), s)
            },
        }
    }

    // The chosen_external_next is called by external_next.
    // It models the external system that is indexed by controller_id.
    pub open spec fn chosen_external_next(self, controller_id: int) -> Action<ClusterState, Option<Message>, ()> {
        let result = |input: Option<Message>, s: ClusterState| {
            let host_result = self.external(controller_id).next_result(
                ExternalActionInput{recv: input, resources: s.api_server.resources},
                s.controller_and_externals[controller_id].external.get_Some_0()
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
                &&& received_msg_destined_for(input, HostId::External(controller_id))
                &&& result(input, s).0.is_Enabled()
                &&& result(input, s).1.is_Enabled()
            },
            transition: |input: Option<Message>, s: ClusterState| {
                let (host_result, network_result) = result(input, s);
                let controller_and_external_state_prime = ControllerAndExternalState {
                    external: Some(host_result.get_Enabled_0()),
                    ..s.controller_and_externals[controller_id]
                };
                (ClusterState {
                    controller_and_externals: s.controller_and_externals.insert(controller_id, controller_and_external_state_prime),
                    network: network_result.get_Enabled_0(),
                    ..s
                }, ())
            },
        }
    }

    // The stutter step does nothing.
    // It's used to ensure that always(next) holds.
    pub open spec fn stutter(self) -> Action<ClusterState, (), ()> {
        Action {
            precondition: |input: (), s: ClusterState| {
                true
            },
            transition: |input: (), s: ClusterState| {
                (s, ())
            },
        }
    }

    // The following state predicates are the preconditions of different actions of
    // the API server, built-in controller, controller and external system hosts.
    // That is, if the state predicate is satisfied, then the action is enabled.
    //
    // Note the subtle difference between these state predicates and enabled():
    // enabled(A) is satisfied by state s if there exists s' so that A(s, s') holds,
    // while the X_action_pre is defined as the exact precondition of the action.
    //
    // They are very useful when proving wf1: using wf1 to prove P ~> Q by action A
    // requires us to prove P ==> enabled(A), but enabled() is defined with an existential
    // quantifier, which means that we often have to write the proof to provide a witness
    // to that quantifier. We can use the following state predicates to avoid writing
    // tedious witness proof. Concretely, we can first prove X_action_pre ==> enabled(A)
    // as a lemma and then when proving P ~> Q using wf1 one can directly prove p ~> X_action_pre.

    pub open spec fn api_server_action_pre(self, step: APIServerStep, input: Option<Message>) -> StatePred<ClusterState> {
        |s: ClusterState| {
            let host_result = self.api_server().next_action_result(
                (self.api_server().step_to_action)(step),
                APIServerActionInput{recv: input},
                s.api_server
            );
            let msg_ops = MessageOps {
                recv: input,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            &&& received_msg_destined_for(input, HostId::APIServer)
            &&& host_result.is_Enabled()
            &&& network_result.is_Enabled()
        }
    }

    pub open spec fn builtin_controllers_action_pre(self, step: BuiltinControllersStep, input: (BuiltinControllerChoice, ObjectRef)) -> StatePred<ClusterState> {
        |s: ClusterState| {
            let host_result = self.builtin_controllers().next_action_result(
                (self.builtin_controllers().step_to_action)(step),
                BuiltinControllersActionInput{
                    choice: input.0,
                    key: input.1,
                    rpc_id_allocator: s.rpc_id_allocator,
                    resources: s.api_server.resources,
                },
                ()
            );
            let msg_ops = MessageOps {
                recv: None,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            &&& host_result.is_Enabled()
            &&& network_result.is_Enabled()
        }
    }

    pub open spec fn controller_action_pre(self, step: ControllerStep, input: (int, Option<Message>, Option<ObjectRef>)) -> StatePred<ClusterState> {
        |s: ClusterState| {
            let controller_id = input.0;
            let host_result = self.controller(controller_id).next_action_result(
                (self.controller(controller_id).step_to_action)(step),
                ControllerActionInput{recv: input.1, scheduled_cr_key: input.2, rpc_id_allocator: s.rpc_id_allocator},
                s.controller_and_externals[controller_id].controller
            );
            let msg_ops = MessageOps {
                recv: input.1,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            &&& self.controller_models.contains_key(input.0)
            &&& received_msg_destined_for(input.1, HostId::Controller(controller_id))
            &&& host_result.is_Enabled()
            &&& network_result.is_Enabled()
        }
    }

    pub open spec fn external_action_pre(self, step: ExternalStep, input: (int, Option<Message>)) -> StatePred<ClusterState> {
        |s: ClusterState| {
            let controller_id = input.0;
            let host_result = self.external(controller_id).next_action_result(
                (self.external(controller_id).step_to_action)(step),
                ExternalActionInput{recv: input.1, resources: s.api_server.resources},
                s.controller_and_externals[controller_id].external.get_Some_0()
            );
            let msg_ops = MessageOps {
                recv: input.1,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            &&& self.controller_models.contains_key(input.0)
            &&& self.controller_models[controller_id].external_model.is_Some()
            &&& received_msg_destined_for(input.1, HostId::External(controller_id))
            &&& host_result.is_Enabled()
            &&& network_result.is_Enabled()
        }
    }

    pub open spec fn api_server(self) -> APIServerStateMachine {
        api_server(self.installed_types)
    }

    pub open spec fn builtin_controllers(self) -> BuiltinControllersStateMachine {
        builtin_controllers()
    }

    pub open spec fn controller(self, controller_id: int) -> ControllerStateMachine {
        controller(self.controller_models[controller_id].reconcile_model, controller_id)
    }

    pub open spec fn external(self, controller_id: int) -> ExternalStateMachine {
        external(self.controller_models[controller_id].external_model.get_Some_0())
    }
}

}
