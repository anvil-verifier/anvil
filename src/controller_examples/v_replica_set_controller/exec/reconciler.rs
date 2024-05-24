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

pub fn reconcile_core(v_replica_set: &VReplicaSet, resp_o: Option<Response<EmptyType>>, state: VReplicaSetReconcileState) -> (res: (VReplicaSetReconcileState, Option<Request<EmptyType>>))
    requires v_replica_set@.well_formed(),
    // ensures (res.0@, opt_request_to_view(&res.1)) == model_reconciler::reconcile_core(v_replica_set@, opt_response_to_view(&resp_o), state@),
{
    let namespace = v_replica_set.metadata().namespace().unwrap();
    match &state.reconcile_step {
        VReplicaSetReconcileStep::Init => {
            match v_replica_set.spec().replicas() {
                Some(r) => {
                    if r == 0 {
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
                            reconcile_step: VReplicaSetReconcileStep::AfterCreatePod(1),
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req)));
                    }
                }
                None => {
                    let state_prime = VReplicaSetReconcileState {
                        reconcile_step: VReplicaSetReconcileStep::Done,
                        ..state
                    };
                    return (state_prime, None);
                }
            }
        },
        VReplicaSetReconcileStep::AfterCreatePod(counter) => {
            if resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok() {
                match v_replica_set.spec().replicas() {
                    Some(r) => {
                        if r <= *counter { // we don't consider deletion case for now
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
                                reconcile_step: VReplicaSetReconcileStep::AfterCreatePod(counter + 1),
                                ..state
                            };
                            return (state_prime, Some(Request::KRequest(req)));
                        }
                    }
                    None => {
                        let state_prime = VReplicaSetReconcileState {
                            reconcile_step: VReplicaSetReconcileStep::Done,
                            ..state
                        };
                        return (state_prime, None);
                    }
                }
            } else {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Error,
                    ..state
                };
                return (state_prime, None);
            }
        },
        _ => {
            return (state, None);
        }
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
        metadata.set_generate_name(v_replica_set.metadata().name().unwrap());
        metadata.set_owner_references(make_owner_references(v_replica_set));
        metadata
    });
    pod.set_spec(template.spec().unwrap());
    pod
}

}
