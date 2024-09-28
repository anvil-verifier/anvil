// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::resource::ResourceWrapper;
use crate::kubernetes_api_objects::exec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_api_objects::spec::prelude::DynamicObjectView;
use crate::kubernetes_api_objects::spec::prelude::PodView;
use crate::kubernetes_api_objects::spec::resource::ResourceView;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vreplicaset_controller::model::reconciler as model_reconciler;
use crate::vreplicaset_controller::trusted::exec_types::*;
use crate::vreplicaset_controller::trusted::spec_types;
use crate::vreplicaset_controller::trusted::step::*;
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

pub fn reconcile_core(v_replica_set: &VReplicaSet, resp_o: Option<Response<EmptyType>>, state: VReplicaSetReconcileState) -> (res: (VReplicaSetReconcileState, Option<Request<EmptyType>>))
    requires v_replica_set@.well_formed(),
    ensures (res.0@, opt_request_to_view(&res.1)) == model_reconciler::reconcile_core(v_replica_set@, opt_response_to_view(&resp_o), state@),
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
                let req = KubeAPIRequest::DeleteRequest(KubeDeleteRequest {
                    api_resource: Pod::api_resource(),
                    name: pod_name_or_none.unwrap(),
                    namespace: namespace,
                    preconditions: None,
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
                if diff > state.filtered_pods.as_ref().unwrap().len() {
                    return (error_state(state), None);
                }
                let pod_name_or_none = state.filtered_pods.as_ref().unwrap()[diff - 1].metadata().name();
                if pod_name_or_none.is_none() {
                    return (error_state(state), None);
                }
                let req = KubeAPIRequest::DeleteRequest(KubeDeleteRequest {
                    api_resource: Pod::api_resource(),
                    name: pod_name_or_none.unwrap(),
                    namespace: namespace,
                    // TODO: set the resource version to be the precondition
                    preconditions: None,
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
    ensures opt_podvec_to_view(&pods_or_none) == model_reconciler::objects_to_pods(objs@.map_values(|o: DynamicObject| o@))
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

    while idx < objs.len()
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
        idx = idx + 1;
    }

    proof {
        let model_input = objs@.map_values(|o: DynamicObject| o@);
        let model_result = model_reconciler::objects_to_pods(model_input);

        // Prove, by contradiction, that the model_result can't be None.
        let filter_result = model_input.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err());
        assert(filter_result.len() == 0) by {
            if filter_result.len() != 0 {
                lemma_filter_contains_implies_contains(
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

proof fn lemma_filter_contains_implies_contains<A>(s: Seq<A>, pred: spec_fn(A) -> bool, e: A)
    requires s.filter(pred).contains(e),
    ensures s.contains(e),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() == 0 {
        // Trivially true.
    } else {
        // Induction structure follows implementation of .filter().
        if s.last() == e {
            // The witness for .contains() is the last index.
        } else {
            // Inductive step.
            lemma_filter_contains_implies_contains(s.drop_last(), pred, e);
        }
    }
}

pub open spec fn opt_podvec_to_view(vec_or_none: &Option<Vec<Pod>>) -> Option<Seq<PodView>> {
    match vec_or_none {
        Some(vec) => Some(vec@.map_values(|p: Pod| p@)),
        None => None,
    }
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

    while idx < pods.len()
        invariant
            idx <= pods.len(),
            filtered_pods@.map_values(|p: Pod| p@)
                == model_reconciler::filter_pods(pods@.map_values(|p: Pod| p@).take(idx as int), v_replica_set@),
    {
        let pod = &pods[idx];

        // TODO: check other conditions such as pod status
        // Check the following conditions:
        // (1) the pod's label should match the replica set's selector
        if pod.metadata().owner_references_contains(v_replica_set.controller_owner_ref())
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
            lemma_filter_maintained_after_add(
                pods@.map_values(|p: Pod| p@).take(idx as int),
                spec_filter,
                old_filtered,
                pod@
            );
            assert(pods@.map_values(|p: Pod| p@).take(idx as int).push(pod@)
                    == pods@.map_values(|p: Pod| p@).take((idx + 1) as int));
            assert(spec_filter(pod@) ==> filtered_pods@.map_values(|p: Pod| p@) == old_filtered.push(pod@));
        }

        idx = idx + 1;
    }
    assert(pods@.map_values(|p: Pod| p@) == pods@.map_values(|p: Pod| p@).take(pods.len() as int));
    filtered_pods
}

proof fn lemma_filter_maintained_after_add<A>(s: Seq<A>, pred: spec_fn(A) -> bool, filtered_s: Seq<A>, new_elt: A)
    requires filtered_s == s.filter(pred),
    ensures
        (pred(new_elt) ==> filtered_s.push(new_elt) == s.push(new_elt).filter(pred)),
        (!pred(new_elt) ==> filtered_s == s.push(new_elt).filter(pred)),
{
    // Lemma follows from body of Seq::filter.
    reveal(Seq::filter);
    // For some reason, this law needs to be explicitly asserted.
    assert(s.push(new_elt).drop_last() == s);
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
