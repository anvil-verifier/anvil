// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
// use crate::v_replica_set_controller::model::reconciler as model_reconciler;
// use crate::v_replica_set_controller::model::resource as model_resource;
use crate::v_replica_set_controller::trusted::exec_types::*;
use crate::v_replica_set_controller::trusted::spec_types;
use crate::v_replica_set_controller::trusted::step::*;
use crate::vstd_ext::{string_map::StringMap, string_view::*};
use std::convert::TryInto;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct VReplicaSetReconciler {}

impl Reconciler for VReplicaSetReconciler {
    type R = VReplicaSet;
    type T = VReplicaSetReconcileState;
    type ExternalAPIType = EmptyAPIShimLayer;

    open spec fn well_formed(v_replica_set: &VReplicaSet) -> bool { v_replica_set@.well_formed() }

    fn reconcile_init_state() -> VReplicaSetReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(v_replica_set: &VReplicaSet, resp_o: Option<Response<EmptyType>>, state: VReplicaSetReconcileState) -> (VReplicaSetReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(v_replica_set, resp_o, state)
    }

    fn reconcile_done(state: &VReplicaSetReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(state: &VReplicaSetReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for VReplicaSetReconciler {
    fn default() -> VReplicaSetReconciler { VReplicaSetReconciler{} }
}

pub fn reconcile_init_state() -> (state: VReplicaSetReconcileState)
    // ensures state@ == model_reconciler::reconcile_init_state(),
{
    VReplicaSetReconcileState {
        reconcile_step: VReplicaSetReconcileStep::Init,
        filtered_pods: None,
    }
}

pub fn reconcile_done(state: &VReplicaSetReconcileState) -> (res: bool)
    // ensures res == model_reconciler::reconcile_done(state@),
{
    match state.reconcile_step {
        VReplicaSetReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &VReplicaSetReconcileState) -> (res: bool)
    // ensures res == model_reconciler::reconcile_error(state@),
{
    match state.reconcile_step {
        VReplicaSetReconcileStep::Error => true,
        _ => false,
    }
}

#[verifier(external_body)]
pub fn reconcile_core(v_replica_set: &VReplicaSet, resp_o: Option<Response<EmptyType>>, state: VReplicaSetReconcileState) -> (res: (VReplicaSetReconcileState, Option<Request<EmptyType>>))
    requires v_replica_set@.well_formed(),
    // ensures (res.0@, opt_request_to_view(&res.1)) == model_reconciler::reconcile_core(v_replica_set@, opt_response_to_view(&resp_o), state@),
{
    let namespace = v_replica_set.metadata().namespace().unwrap();
    match &state.reconcile_step {
        VReplicaSetReconcileStep::Init => {
            let req = KubeAPIRequest::ListRequest(KubeListRequest {
                api_resource: Pod::api_resource(),
                namespace: namespace,
            });
            let state_prime = VReplicaSetReconcileState {
                reconcile_step: VReplicaSetReconcileStep::AfterListPods,
                ..state
            };
            return (state_prime, Some(Request::KRequest(req)));
        },
        VReplicaSetReconcileStep::AfterListPods => {
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_list_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_list_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            let objs = resp_o.unwrap().into_k_response().into_list_response().res.unwrap();
            let pods_or_none = objects_to_pods(objs);
            if pods_or_none.is_none() {
                return (error_state(state), None);
            }
            let pods = pods_or_none.unwrap();
            let filtered_pods = filter_pods(pods, v_replica_set);
            let replicas = v_replica_set.spec().replicas().unwrap_or(0);
            if replicas < 0 {
                return (error_state(state), None);
            }
            let desired_replicas: usize = replicas.try_into().unwrap();
            if filtered_pods.len() == desired_replicas {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            } else if filtered_pods.len() > desired_replicas {
                let diff = filtered_pods.len() - desired_replicas;
                let pod = make_pod(v_replica_set);
                let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                    api_resource: Pod::api_resource(),
                    namespace: namespace,
                    obj: pod.marshal(),
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterCreatePod(diff - 1),
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req)));
            } else {
                let diff = desired_replicas - filtered_pods.len();
                let pod_name_or_none = filtered_pods[diff].metadata().name();
                if pod_name_or_none.is_none() {
                    return (error_state(state), None);
                }
                let req = KubeAPIRequest::DeleteRequest(KubeDeleteRequest {
                    api_resource: Pod::api_resource(),
                    name: pod_name_or_none.unwrap(),
                    namespace: namespace,
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterDeletePod(diff - 1),
                    filtered_pods: Some(filtered_pods),
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req)));
            }
        },
        VReplicaSetReconcileStep::AfterCreatePod(diff) => {
            let diff = *diff;
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            if diff == 0 {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            } else {
                let pod = make_pod(v_replica_set);
                let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                    api_resource: Pod::api_resource(),
                    namespace: namespace,
                    obj: pod.marshal(),
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterCreatePod(diff - 1),
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req)));
            }
        },
        VReplicaSetReconcileStep::AfterDeletePod(diff) => {
            let diff = *diff;
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_delete_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_delete_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            if diff == 0 {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            } else {
                if state.filtered_pods.is_none() {
                    return (error_state(state), None);
                }
                let pod_name_or_none = state.filtered_pods.as_ref().unwrap()[diff].metadata().name();
                if pod_name_or_none.is_none() {
                    return (error_state(state), None);
                }
                let req = KubeAPIRequest::DeleteRequest(KubeDeleteRequest {
                    api_resource: Pod::api_resource(),
                    name: pod_name_or_none.unwrap(),
                    namespace: namespace,
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterDeletePod(diff - 1),
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req)));
            }
        },
        _ => {
            return (state, None);
        }
    }
}

pub fn error_state(state: VReplicaSetReconcileState) -> (state_prime: VReplicaSetReconcileState)
{
    VReplicaSetReconcileState {
        reconcile_step: VReplicaSetReconcileStep::Error,
        ..state
    }
}

pub fn make_owner_references(v_replica_set: &VReplicaSet) -> (owner_references: Vec<OwnerReference>)
    // requires v_replica_set@.well_formed(),
    // ensures owner_references@.map_values(|or: OwnerReference| or@) ==  model_resource::make_owner_references(v_replica_set@),
{
    let mut owner_references = Vec::new();
    owner_references.push(v_replica_set.controller_owner_ref());
    // proof {
    //     assert_seqs_equal!(
    //         owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
    //         model_resource::make_owner_references(v_replica_set@)
    //     );
    // }
    owner_references
}

// TODO: This function can be replaced by a map.
// Revisit it if Verus supports Vec.map.
fn objects_to_pods(objs: Vec<DynamicObject>) -> (pods_or_none: Option<Vec<Pod>>)
{
    let mut pods = Vec::new();
    let mut idx = 0;
    while idx < objs.len() {
        let pod_or_error = Pod::unmarshal(objs[idx].clone());
        if pod_or_error.is_ok() {
            pods.push(pod_or_error.unwrap());
        } else {
            return None;
        }
        idx = idx + 1;
    }
    Some(pods)
}

// TODO: This function can be replaced by a map.
// Revisit it if Verus supports Vec.map.
fn filter_pods(pods: Vec<Pod>, v_replica_set: &VReplicaSet) -> (filtered_pods: Vec<Pod>)
{
    let mut filtered_pods = Vec::new();
    let mut idx = 0;
    while idx < pods.len() {
        let pod = &pods[idx];
        // TODO: check other conditions such as pod status and deletion timestamp
        if pod.metadata().owner_references_contains(v_replica_set.controller_owner_ref())
        && v_replica_set.spec().selector().matches(pod.metadata().labels().unwrap_or(StringMap::new())) {
            filtered_pods.push(pod.clone());
        }
        idx = idx + 1;
    }
    filtered_pods
}

fn make_pod(v_replica_set: &VReplicaSet) -> (pod: Pod)
    requires v_replica_set@.well_formed(),
{
    let template = v_replica_set.spec().template().unwrap();
    let mut pod = Pod::default();
    pod.set_metadata({
        let mut metadata = ObjectMeta::default();
        let labels = template.metadata().unwrap().labels();
        if labels.is_some() {
            metadata.set_labels(labels.unwrap());
        }
        let labels = template.metadata().unwrap().labels();
        if labels.is_some() {
            metadata.set_labels(labels.unwrap());
        }
        let annotations = template.metadata().unwrap().annotations();
        if annotations.is_some() {
            metadata.set_annotations(annotations.unwrap());
        }
        let finalizers = template.metadata().unwrap().finalizers();
        if finalizers.is_some() {
            metadata.set_finalizers(finalizers.unwrap());
        }
        metadata.set_generate_name(v_replica_set.metadata().name().unwrap().concat(new_strlit("-")));
        metadata.set_owner_references(make_owner_references(v_replica_set));
        metadata
    });
    pod.set_spec(template.spec().unwrap());
    pod
}

}
