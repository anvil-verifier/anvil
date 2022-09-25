// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#[allow(unused_imports)]
use crate::apis::*;
#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use crate::custom_controller_var::*;
#[allow(unused_imports)]
use crate::pervasive::{map::*, option::Option, *};
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

// We ask the developers to specify what objects the controller watches on
// The object should come from APIWatchNotification
// In kube-rs, the developers have three ways to specify what to watch on
// 1. Watch on the CR, see https://github.com/kube-rs/kube-rs/blob/0b2f7b88d58a076808b09afb640191eab2fbc84e/kube-runtime/src/controller/mod.rs#L410
// 2. Watch on an object owned by the CR, see https://github.com/kube-rs/kube-rs/blob/0b2f7b88d58a076808b09afb640191eab2fbc84e/kube-runtime/src/controller/mod.rs#L485
// 3. Watch on an object that has some custom relation to the CR, see https://github.com/kube-rs/kube-rs/blob/0b2f7b88d58a076808b09afb640191eab2fbc84e/kube-runtime/src/controller/mod.rs#L524
// The developers are required to implement the same mappings here
#[spec] #[verifier(publish)]
pub fn map_to_triggering_key(object: KubernetesObject) -> Option<ObjectKey> {
    match object {
        KubernetesObject::CustomResourceObject(cro) => {
            match cro {
                CustomResourceObject::ConfigMapGenerator(cmg) => Option::Some(cmg.key()),
            }
        },
        KubernetesObject::ConfigMap(cm) => Option::Some(cm.metadata.owner_key),
        _ => Option::None,
    }
}

pub open spec fn is_cr_type(object_type: StringL) -> bool {
    equal(object_type, StringL::ConfigMapGenerator)
}

pub open spec fn trigger_reconcile(api_event_notification: APIEventNotification) -> bool {
    match map_to_triggering_key(api_event_notification.object()) {
        Option::Some(_) => true,
        Option::None => false,
    }
}

pub open spec fn controller_step_limit_spec() -> int {
    10
}

pub open spec fn distributed_system_step_limit_spec() -> i32 {
    20
}

pub open spec fn configmap_1_key() -> ObjectKey {
    ObjectKey{object_type: StringL::ConfigMap, namespace: StringL::Default, name: StringL::ConfigMap1}
}

pub open spec fn configmap_2_key() -> ObjectKey {
    ObjectKey{object_type: StringL::ConfigMap, namespace: StringL::Default, name: StringL::ConfigMap2}
}

// TODO: it would be nicer if this spec was simpler than controller_logic, but that seems unlikely
pub open spec fn controller_logic_spec(controller_step: ReconcileStep, triggering_key: ObjectKey, cluster_state: ClusterState, api_result: Option<APIOpResponse>, next_step: ReconcileStep, api_op_request: Option<APIOpRequest>) -> bool {
    let configmap_1 = StringL::ConfigMap1;
    let configmap_2 = StringL::ConfigMap2;
    let default = StringL::Default;
    let configmap = StringL::ConfigMap;

    match controller_step {
        ReconcileStep::Init =>
            equal(next_step, ReconcileStep::CustomReconcileStep(CustomReconcileStep::CheckIfCMGExists))
            && api_op_request.is_Some()
            && equal(api_op_request.get_Some_0(), APIOpRequest{api_op:APIOp::Get{
                object_key: triggering_key
            }}),
        ReconcileStep::CustomReconcileStep(step) =>
            match step {
                CustomReconcileStep::CheckIfCMGExists =>
                    if !cluster_state.contains(triggering_key) {
                        equal(next_step, ReconcileStep::Done)
                        && api_op_request.is_None()
                    } else {
                        equal(next_step, ReconcileStep::CustomReconcileStep(CustomReconcileStep::CheckIfCMExists))
                        && api_op_request.is_Some()
                        && equal(api_op_request.get_Some_0(), APIOpRequest{api_op:APIOp::Get{
                            object_key: configmap_1_key()
                        }})
                    },
                CustomReconcileStep::CheckIfCMExists =>
                    if !cluster_state.contains(configmap_1_key()) {
                        equal(next_step, ReconcileStep::CustomReconcileStep(CustomReconcileStep::CreateCM1))
                        && api_op_request.is_Some()
                        && equal(api_op_request.get_Some_0(), APIOpRequest{
                            api_op:APIOp::Create{
                                object_key:configmap_1_key(),
                                object:KubernetesObject::ConfigMap(ConfigMapL{
                                    metadata: MetadataL{
                                        name: configmap_1,
                                        namespace: default,
                                        owner_key: triggering_key,
                                    },
                                }),
                            }
                        })
                    } else {
                        equal(next_step, ReconcileStep::Done)
                        && api_op_request.is_None()
                    },
                CustomReconcileStep::CreateCM1 =>
                    if cluster_state.contains(configmap_1_key()) {
                        equal(next_step, ReconcileStep::CustomReconcileStep(CustomReconcileStep::CreateCM2))
                        && api_op_request.is_Some()
                        && equal(api_op_request.get_Some_0(), APIOpRequest{
                            api_op:APIOp::Create{
                                object_key:configmap_2_key(),
                                object:KubernetesObject::ConfigMap(ConfigMapL{
                                    metadata: MetadataL{
                                        name: configmap_2,
                                        namespace: default,
                                        owner_key: triggering_key,
                                    },
                                }),
                            }
                        })
                    } else {
                        equal(next_step, ReconcileStep::Retry)
                        && api_op_request.is_None()
                    },
                CustomReconcileStep::CreateCM2 =>
                    if cluster_state.contains(configmap_2_key()) {
                        equal(next_step, ReconcileStep::Done)
                        && api_op_request.is_None()
                    } else {
                        equal(next_step, ReconcileStep::Retry)
                        && api_op_request.is_None()
                    }
            },
        ReconcileStep::Retry =>
            equal(next_step, ReconcileStep::Retry)
            && api_op_request.is_None(),
        ReconcileStep::Done =>
            equal(next_step, ReconcileStep::Done)
            && api_op_request.is_None(),
    }
}

// controller_logic is not supposed to modify any heap variables or issue any side effects
//
// TODO: would the monitored object(s) show up as an argument here?
// UPDATE (Jul. 6): We pass the ObjectKey of the triggering object (the custom resource object) to contorller_logic
//
// We can change to passing the triggering object itself later if that is better
// The current controller_logic is trivialized as it does not even look into the triggering object
// Typically the controller will get the object with the key either from cache or from etcd,
// if the object does not exist, the reconcile will return
// otherwise the reconcile often name the core objects after the triggering cr object
//
// One common practice to handle object deletion is that the cr object should have a finalizer
// And the controller will delete the core objects if the controller has a deletion timestamp
// and then removes the finalizer from the cr object
pub fn controller_logic(controller_step: ReconcileStep, triggering_key: ObjectKey, cluster_state: ClusterStateImpl, api_result: Option<APIOpResponse>) -> (ReconcileStep, Option<APIOpRequest>) {
    ensures(|ret: (ReconcileStep, Option<APIOpRequest>)| controller_logic_spec(controller_step, triggering_key, ClusterState{state: cluster_state.state.view()}, api_result, ret.0, ret.1));
    // These would normally be global consts but verus does not support that yet
    let configmap_1 = StringL::ConfigMap1;
    let configmap_2 = StringL::ConfigMap2;
    let default = StringL::Default;
    let configmap = StringL::ConfigMap;

    let configmap_1_key = ObjectKey{ object_type: configmap, namespace: default, name: configmap_1 };
    let configmap_2_key = ObjectKey{ object_type: configmap, namespace: default, name: configmap_2 };

    match controller_step {
        ReconcileStep::Init => {
            (ReconcileStep::CustomReconcileStep(CustomReconcileStep::CheckIfCMGExists),
            Option::Some(APIOpRequest{api_op:APIOp::Get{object_key:triggering_key}}))
        },
        ReconcileStep::CustomReconcileStep(step) => {
            match step {
                CustomReconcileStep::CheckIfCMGExists => {
                    if !cluster_state.state.contains(&triggering_key) {
                        (ReconcileStep::Done, Option::None)
                    } else {
                        (ReconcileStep::CustomReconcileStep(CustomReconcileStep::CheckIfCMExists),
                        Option::Some(APIOpRequest{api_op:APIOp::Get{object_key:configmap_1_key}}))
                    }
                },
                CustomReconcileStep::CheckIfCMExists => {
                    if !cluster_state.state.contains(&configmap_1_key) {
                        (ReconcileStep::CustomReconcileStep(CustomReconcileStep::CreateCM1),
                        Option::Some(APIOpRequest{
                            api_op:APIOp::Create{
                                object_key:configmap_1_key,
                                object:KubernetesObject::ConfigMap(ConfigMapL{
                                    metadata: MetadataL{
                                        name: configmap_1,
                                        namespace: default,
                                        owner_key: triggering_key,
                                    },
                                }),
                            }
                        }))
                    } else {
                        // This is a crash-safety bug the verifier should catch!!!
                        (ReconcileStep::Done, Option::None)
                    }
                },
                CustomReconcileStep::CreateCM1 => {
                    if cluster_state.state.contains(&configmap_1_key) {
                        (ReconcileStep::CustomReconcileStep(CustomReconcileStep::CreateCM2),
                        Option::Some(APIOpRequest{
                            api_op:APIOp::Create{
                                object_key:configmap_2_key,
                                object:KubernetesObject::ConfigMap(ConfigMapL{
                                    metadata: MetadataL{
                                        name: configmap_2,
                                        namespace: default,
                                        owner_key: triggering_key,
                                    },
                                }),
                            }
                        }))
                    } else {
                        (ReconcileStep::Retry, Option::None)
                    }
                },
                CustomReconcileStep::CreateCM2 => {
                    if cluster_state.state.contains(&configmap_2_key) {
                        (ReconcileStep::Done, Option::None)
                    } else {
                        (ReconcileStep::Retry, Option::None)
                    }
                }
            }
        },
        // The Retry and Done branch should never be executed since the shim layer should just return when seeing Retry or Done
        // TODO: should we panic if these cases should never be executed?
        ReconcileStep::Retry => (ReconcileStep::Retry, Option::None),
        ReconcileStep::Done => (ReconcileStep::Done, Option::None),
    }
}

fn main() { }

}
