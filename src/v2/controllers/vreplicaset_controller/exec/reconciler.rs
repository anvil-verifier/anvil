// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vreplicaset_controller::model::reconciler as model_reconciler;
use crate::vreplicaset_controller::trusted::{exec_types::*, step::*};
use crate::vstd_ext::{option_lib::*, string_map::StringMap, seq_lib::*};
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

// TODO:
// + Skip reconciling if ReplicaSet has non-nil deletion_timestamp
//
// + Adopt and release pods based on ownership and labels
//
// + Update ReplicaSet status based on Pod status

// VReplicaSetReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct VReplicaSetReconcileState {
    pub reconcile_step: VReplicaSetReconcileStep,
    pub filtered_pods: Option<Vec<Pod>>,
}

impl View for VReplicaSetReconcileState {
    type V = model_reconciler::VReplicaSetReconcileState;

    open spec fn view(&self) -> model_reconciler::VReplicaSetReconcileState {
        model_reconciler::VReplicaSetReconcileState {
            reconcile_step: self.reconcile_step@,
            filtered_pods: match self.filtered_pods {
                Some(fp) => Some(fp@.map_values(|p: Pod| p@)),
                None => None,
            },
        }
    }
}

pub struct VReplicaSetReconciler {}

impl Reconciler for VReplicaSetReconciler {
    type S = VReplicaSetReconcileState;
    type K = VReplicaSet;
    type EReq = VoidEReq;
    type EResp = VoidEResp;
    type M = model_reconciler::VReplicaSetReconciler;

    fn reconcile_init_state() -> Self::S {
        reconcile_init_state()
    }

    fn reconcile_core(vrs: &Self::K, resp_o: Option<Response<Self::EResp>>, state: Self::S) -> (Self::S, Option<Request<Self::EReq>>) {
        reconcile_core(vrs, resp_o, state)
    }

    fn reconcile_done(state: &Self::S) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(state: &Self::S) -> bool {
        reconcile_error(state)
    }
}

pub fn reconcile_init_state() -> (state: VReplicaSetReconcileState)
    ensures state@ == model_reconciler::reconcile_init_state(),
{
    VReplicaSetReconcileState {
        reconcile_step: VReplicaSetReconcileStep::Init,
        filtered_pods: None,
    }
}

pub fn reconcile_done(state: &VReplicaSetReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_done(state@),
{
    match state.reconcile_step {
        VReplicaSetReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &VReplicaSetReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_error(state@),
{
    match state.reconcile_step {
        VReplicaSetReconcileStep::Error => true,
        _ => false,
    }
}

pub fn reconcile_core(v_replica_set: &VReplicaSet, resp_o: Option<Response<VoidEResp>>, state: VReplicaSetReconcileState) -> (res: (VReplicaSetReconcileState, Option<Request<VoidEReq>>))
    requires v_replica_set@.well_formed(),
    ensures (res.0@, res.1.deep_view()) == model_reconciler::reconcile_core(v_replica_set@, resp_o.deep_view(), state@),
{
    let namespace = v_replica_set.metadata().namespace().unwrap();
    match &state.reconcile_step {
        VReplicaSetReconcileStep::Init => {
            if v_replica_set.metadata().has_deletion_timestamp() {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            } else {
                let req = KubeAPIRequest::ListRequest(KubeListRequest {
                    api_resource: Pod::api_resource(),
                    namespace: namespace,
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterListPods,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req)));
            }
        },
        VReplicaSetReconcileStep::AfterListPods => {
            if !(is_some_k_list_resp!(resp_o) && extract_some_k_list_resp_as_ref!(resp_o).is_ok()) {
                return (error_state(state), None);
            }
            let objs = extract_some_k_list_resp!(resp_o).unwrap();
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
            let desired_replicas: usize = replicas as usize;
            if filtered_pods.len() == desired_replicas {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            } else if filtered_pods.len() < desired_replicas {
                let diff =  desired_replicas - filtered_pods.len();
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
                let diff = filtered_pods.len() - desired_replicas;
                let pod_name_or_none = filtered_pods[diff - 1].metadata().name();
                if pod_name_or_none.is_none() {
                    return (error_state(state), None);
                }
                let req = KubeAPIRequest::GetThenDeleteRequest(KubeGetThenDeleteRequest {
                    api_resource: Pod::api_resource(),
                    name: pod_name_or_none.unwrap(),
                    namespace: namespace,
                    owner_ref: v_replica_set.controller_owner_ref(),
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
            if !(is_some_k_create_resp!(resp_o) && extract_some_k_create_resp!(resp_o).is_ok()) {
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
            if !(is_some_k_get_then_delete_resp!(resp_o) && extract_some_k_get_then_delete_resp!(resp_o).is_ok()) {
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
                if diff > state.filtered_pods.as_ref().unwrap().len() {
                    return (error_state(state), None);
                }
                let pod_name_or_none = state.filtered_pods.as_ref().unwrap()[diff - 1].metadata().name();
                if pod_name_or_none.is_none() {
                    return (error_state(state), None);
                }
                let req = KubeAPIRequest::GetThenDeleteRequest(KubeGetThenDeleteRequest {
                    api_resource: Pod::api_resource(),
                    name: pod_name_or_none.unwrap(),
                    namespace: namespace,
                    owner_ref: v_replica_set.controller_owner_ref(),
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
    ensures state_prime@ == model_reconciler::error_state(state@),
{
    VReplicaSetReconcileState {
        reconcile_step: VReplicaSetReconcileStep::Error,
        ..state
    }
}

pub fn make_owner_references(v_replica_set: &VReplicaSet) -> (owner_references: Vec<OwnerReference>)
    requires v_replica_set@.well_formed(),
    ensures owner_references@.map_values(|or: OwnerReference| or@) ==  model_reconciler::make_owner_references(v_replica_set@),
{
    let mut owner_references = Vec::new();
    owner_references.push(v_replica_set.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
            model_reconciler::make_owner_references(v_replica_set@)
        );
    }
    owner_references
}

// TODO: This function can be replaced by a map.
// Revisit it if Verus supports Vec.map.
fn objects_to_pods(objs: Vec<DynamicObject>) -> (pods_or_none: Option<Vec<Pod>>)
    ensures option_vec_view(pods_or_none) == model_reconciler::objects_to_pods(objs@.map_values(|o: DynamicObject| o@))
{
    let mut pods = Vec::new();
    let mut idx = 0;

    proof {
        let model_result = model_reconciler::objects_to_pods(objs@.map_values(|o: DynamicObject| o@));
        if model_result.is_some() {
            assert_seqs_equal!(
                pods@.map_values(|p: Pod| p@),
                model_result.unwrap().take(0)
            );
        }
    }
    
    for idx in 0..objs.len()
        invariant
            idx <= objs.len(),
            ({
                let model_result = model_reconciler::objects_to_pods(objs@.map_values(|o: DynamicObject| o@));
                &&& (model_result.is_some() ==>
                        pods@.map_values(|p: Pod| p@) == model_result.unwrap().take(idx as int))
                &&& forall|i: int| 0 <= i < idx ==> PodView::unmarshal(#[trigger] objs@[i]@).is_ok()
            }),
    {
        let pod_or_error = Pod::unmarshal(objs[idx].clone());
        if pod_or_error.is_ok() {
            pods.push(pod_or_error.unwrap());
            proof {
                // Show that the pods Vec and the model_result are equal up to index idx + 1.
                let model_result = model_reconciler::objects_to_pods(objs@.map_values(|o: DynamicObject| o@));
                if (model_result.is_some()) {
                    assert(model_result.unwrap().take((idx + 1) as int)
                        == model_result.unwrap().take(idx as int) + seq![model_result.unwrap()[idx as int]]);
                    assert_seqs_equal!(
                        pods@.map_values(|p: Pod| p@),
                        model_result.unwrap().take((idx + 1) as int)
                    );
                }
            }
        } else {
            proof {
                // Show that if a pod was unable to be serialized, the model would return None.
                let model_input = objs@.map_values(|o: DynamicObject| o@);
                let model_result = model_reconciler::objects_to_pods(model_input);
                assert(
                    model_input
                        .filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err())
                        .contains(model_input[idx as int])
                );
                assert(model_result == None::<Seq<PodView>>);
            }
            return None;
        }
    }

    proof {
        let model_input = objs@.map_values(|o: DynamicObject| o@);
        let model_result = model_reconciler::objects_to_pods(model_input);

        // Prove, by contradiction, that the model_result can't be None.
        let filter_result = model_input.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err());
        assert(filter_result.len() == 0) by {
            if filter_result.len() != 0 {
                seq_filter_contains_implies_seq_contains(
                    model_input,
                    |o: DynamicObjectView| PodView::unmarshal(o).is_err(),
                    filter_result[0]
                );
            }
        };
        assert(model_result.is_some());

        assert(model_result.unwrap().take(objs.len() as int) == model_result.unwrap());
    }

    Some(pods)
}

// TODO: This function can be replaced by a map.
// Revisit it if Verus supports Vec.map.
fn filter_pods(pods: Vec<Pod>, v_replica_set: &VReplicaSet) -> (filtered_pods: Vec<Pod>)
    requires v_replica_set@.well_formed(),
    ensures filtered_pods@.map_values(|p: Pod| p@) == model_reconciler::filter_pods(pods@.map_values(|p: Pod| p@), v_replica_set@),
{
    let mut filtered_pods = Vec::new();
    let mut idx = 0;

    proof {
        assert_seqs_equal!(
            filtered_pods@.map_values(|p: Pod| p@),
            model_reconciler::filter_pods(pods@.map_values(|p: Pod| p@).take(0), v_replica_set@)
        );
    }

    for idx in 0..pods.len()
        invariant
            idx <= pods.len(),
            filtered_pods@.map_values(|p: Pod| p@)
                == model_reconciler::filter_pods(pods@.map_values(|p: Pod| p@).take(idx as int), v_replica_set@),
    {
        let pod = &pods[idx];

        // TODO: check other conditions such as pod status
        // Check the following conditions:
        // (1) the pod's label should match the replica set's selector
        if pod.metadata().owner_references_contains(&v_replica_set.controller_owner_ref())
        && v_replica_set.spec().selector().matches(pod.metadata().labels().unwrap_or(StringMap::new()))
        // (2) the pod should not be terminating (its deletion timestamp is nil)
        && !pod.metadata().has_deletion_timestamp() {
            filtered_pods.push(pod.clone());
        }

        proof {
            let spec_filter = |pod: PodView|
                pod.metadata.owner_references_contains(v_replica_set@.controller_owner_ref())
                && v_replica_set@.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                && pod.metadata.deletion_timestamp.is_None();
            let old_filtered = if spec_filter(pod@) {
                filtered_pods@.map_values(|p: Pod| p@).drop_last()
            } else {
                filtered_pods@.map_values(|p: Pod| p@)
            };
            assert(old_filtered == pods@.map_values(|p: Pod| p@).take(idx as int).filter(spec_filter));
            push_filter_and_filter_push(pods@.map_values(|p: Pod| p@).take(idx as int), spec_filter, pod@);
            assert(pods@.map_values(|p: Pod| p@).take(idx as int).push(pod@)
                   == pods@.map_values(|p: Pod| p@).take((idx + 1) as int));
            assert(spec_filter(pod@) ==> filtered_pods@.map_values(|p: Pod| p@) == old_filtered.push(pod@));
        }
    }
    assert(pods@.map_values(|p: Pod| p@) == pods@.map_values(|p: Pod| p@).take(pods.len() as int));
    filtered_pods
}

fn make_pod(v_replica_set: &VReplicaSet) -> (pod: Pod)
    requires v_replica_set@.well_formed(),
    ensures pod@ == model_reconciler::make_pod(v_replica_set@),
{
    let template = v_replica_set.spec().template().unwrap();
    let mut pod = Pod::default();
    pod.set_metadata({
        let mut metadata = ObjectMeta::default();
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
        metadata.set_generate_name(v_replica_set.metadata().name().unwrap().concat("-"));
        metadata.set_owner_references(make_owner_references(v_replica_set));
        metadata
    });
    pod.set_spec(template.spec().unwrap());
    pod
}

}
