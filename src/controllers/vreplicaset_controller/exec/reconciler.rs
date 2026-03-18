// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use crate::vreplicaset_controller::model::reconciler as model_reconciler;
use crate::vreplicaset_controller::trusted::{spec_types::VReplicaSetView, exec_types::*, step::*};
use crate::vstd_ext::{seq_lib::*, string_map::StringMap, string_view::*};
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
            filtered_pods: self.filtered_pods.deep_view(),
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

pub fn reconcile_core(vrs: &VReplicaSet, resp_o: Option<Response<VoidEResp>>, state: VReplicaSetReconcileState) -> (res: (VReplicaSetReconcileState, Option<Request<VoidEReq>>))
    requires vrs@.well_formed(),
    ensures (res.0@, res.1.deep_view()) == model_reconciler::reconcile_core(vrs@, resp_o.deep_view(), state@),
{
    let namespace = vrs.metadata().namespace().unwrap();
    match &state.reconcile_step {
        VReplicaSetReconcileStep::Init => {
            if vrs.metadata().has_deletion_timestamp() {
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
            assert(objs.deep_view() == extract_some_k_list_resp_view(resp_o.deep_view()).unwrap());
            let pods_or_none = objects_to_pods(objs);
            if pods_or_none.is_none() {
                return (error_state(state), None);
            }
            let pods = pods_or_none.unwrap();
            let filtered_pods = filter_pods(pods, vrs);
            let replicas = vrs.spec().replicas().unwrap_or(1);
            if replicas < 0 {
                return (error_state(state), None);
            }
            let desired_replicas: usize = replicas as usize;
            if filtered_pods.len() == desired_replicas {
                return update_vrs_replicas(state, vrs);
            } else if filtered_pods.len() < desired_replicas {
                let diff =  desired_replicas - filtered_pods.len();
                let pod = make_pod(vrs);
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
                    owner_ref: vrs.controller_owner_ref(),
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
                return update_vrs_replicas(state, vrs);
            } else {
                let pod = make_pod(vrs);
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
                return update_vrs_replicas(state, vrs);
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
                    owner_ref: vrs.controller_owner_ref(),
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterDeletePod(diff - 1),
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req)));
            }
        },
        VReplicaSetReconcileStep::AfterUpdateVRSStatus => {
            if !(is_some_k_get_then_update_status_resp!(resp_o) && extract_some_k_get_then_update_status_resp!(resp_o).is_ok()) {
                return (error_state(state), None);
            }
            let state_prime = VReplicaSetReconcileState {
                reconcile_step: VReplicaSetReconcileStep::Done,
                ..state
            };
            return (state_prime, None);
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

pub fn make_owner_references(vrs: &VReplicaSet) -> (owner_references: Vec<OwnerReference>)
    requires vrs@.well_formed(),
    ensures owner_references.deep_view() ==  model_reconciler::make_owner_references(vrs@),
{
    let mut owner_references = Vec::new();
    owner_references.push(vrs.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references.deep_view(),
            model_reconciler::make_owner_references(vrs@)
        );
    }
    owner_references
}

// TODO: This function can be replaced by a map.
// Revisit it if Verus supports Vec.map.
fn objects_to_pods(objs: Vec<DynamicObject>) -> (pods_or_none: Option<Vec<Pod>>)
    ensures pods_or_none.deep_view() == model_reconciler::objects_to_pods(objs.deep_view())
{
    let mut pods = Vec::new();
    let mut idx = 0;

    proof {
        let model_result = model_reconciler::objects_to_pods(objs.deep_view());
        if model_result.is_some() {
            assert_seqs_equal!(
                pods.deep_view(),
                model_result.unwrap().take(0)
            );
        }
    }

    for idx in 0..objs.len()
        invariant
            idx <= objs.len(),
            ({
                let model_result = model_reconciler::objects_to_pods(objs.deep_view());
                &&& (model_result.is_some() ==>
                        pods.deep_view() == model_result.unwrap().take(idx as int))
                &&& forall|i: int| 0 <= i < idx ==> PodView::unmarshal(#[trigger] objs@[i]@).is_ok()
            }),
    {
        let pod_or_error = Pod::unmarshal(objs[idx].clone());
        if pod_or_error.is_ok() {
            pods.push(pod_or_error.unwrap());
            proof {
                // Show that the pods Vec and the model_result are equal up to index idx + 1.
                let model_result = model_reconciler::objects_to_pods(objs.deep_view());
                if (model_result.is_some()) {
                    assert(model_result.unwrap().take((idx + 1) as int)
                        == model_result.unwrap().take(idx as int) + seq![model_result.unwrap()[idx as int]]);
                    assert_seqs_equal!(
                        pods.deep_view(),
                        model_result.unwrap().take((idx + 1) as int)
                    );
                }
            }
        } else {
            proof {
                // Show that if a pod was unable to be serialized, the model would return None.
                let model_input = objs.deep_view();
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
        let model_input = objs.deep_view();
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
fn filter_pods(pods: Vec<Pod>, vrs: &VReplicaSet) -> (filtered_pods: Vec<Pod>)
    requires vrs@.well_formed(),
    ensures filtered_pods.deep_view() == model_reconciler::filter_pods(pods.deep_view(), vrs@),
{
    let mut filtered_pods = Vec::new();
    let mut idx = 0;

    proof {
        assert_seqs_equal!(
            filtered_pods.deep_view(),
            model_reconciler::filter_pods(pods.deep_view().take(0), vrs@)
        );
    }

    for idx in 0..pods.len()
        invariant
            idx <= pods.len(),
            filtered_pods.deep_view()
                == model_reconciler::filter_pods(pods.deep_view().take(idx as int), vrs@),
    {
        let pod = &pods[idx];

        // TODO: check other conditions such as pod status
        // Check the following conditions:
        // (1) the pod's label should match the replica set's selector
        if pod.metadata().owner_references_contains(&vrs.controller_owner_ref())
        && vrs.spec().selector().matches(pod.metadata().labels().unwrap_or(StringMap::new()))
        // (2) the pod should not be terminating (its deletion timestamp is nil)
        && !pod.metadata().has_deletion_timestamp()
        && pod.metadata().name().is_some()
        && has_vrs_prefix(&pod.metadata().name().unwrap()){
            filtered_pods.push(pod.clone());
        }

        proof {
            let spec_filter = model_reconciler::pod_filter(vrs@);
            let old_filtered = if spec_filter(pod@) {
                filtered_pods.deep_view().drop_last()
            } else {
                filtered_pods.deep_view()
            };
            assert(old_filtered == pods.deep_view().take(idx as int).filter(spec_filter));
            lemma_filter_push(pods.deep_view().take(idx as int), spec_filter, pod@);
            assert(pods.deep_view().take(idx as int).push(pod@)
                   == pods.deep_view().take((idx + 1) as int));
            assert(spec_filter(pod@) ==> filtered_pods.deep_view() == old_filtered.push(pod@));
        }
    }
    assert(pods.deep_view() == pods.deep_view().take(pods.len() as int));
    filtered_pods
}

fn has_vrs_prefix(name: &String) -> (res: bool)
    ensures res == model_reconciler::has_vrs_prefix(name@),
{
    let res = starts_with(&name, "vreplicaset-");
    proof {
        assert("vreplicaset-"@ == "vreplicaset"@ + "-"@) by {
            vrs_prefix_equality();
        }
        if res {
            assert(exists |suffix| name@ == "vreplicaset-"@ + suffix);
            assert("vreplicaset"@ == VReplicaSetView::kind()->CustomResourceKind_0);
            assert(exists |suffix| name@ == VReplicaSetView::kind()->CustomResourceKind_0 + "-"@ + suffix);
        }
    }
    return res;
}

fn pod_generate_name(vrs: &VReplicaSet) -> (name: String) 
    requires vrs@.well_formed(),
    ensures name@ == model_reconciler::pod_generate_name(vrs@) 
{
    let prefix = "vreplicaset".to_string().concat("-");
    prefix.concat(vrs.metadata().name().unwrap().concat("-").as_str())
}

fn make_pod(vrs: &VReplicaSet) -> (pod: Pod)
    requires vrs@.well_formed(),
    ensures pod@ == model_reconciler::make_pod(vrs@),
{
    let template = vrs.spec().template().unwrap();
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
        metadata.set_generate_name(pod_generate_name(vrs));
        metadata.set_owner_references(make_owner_references(vrs));
        metadata
    });
    pod.set_spec(template.spec().unwrap());
    pod
}

fn update_vrs_replicas(state: VReplicaSetReconcileState, vrs: &VReplicaSet) -> (res: (VReplicaSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vrs@.well_formed(),
    ensures
        res.0@ == model_reconciler::update_vrs_replicas(state@, vrs@).0,
        res.1.deep_view() == model_reconciler::update_vrs_replicas(state@, vrs@).1,
{
    if vrs.metadata().owner_references().is_some() && filter_by_controller_owner(vrs.metadata().owner_references().unwrap()).len() == 1 {
        let mut new_status = VReplicaSetStatus::default();
        new_status.set_replicas(vrs.spec().replicas().unwrap_or(1));
        let mut new_vrs = vrs.clone();
        new_vrs.set_status(new_status);
        let state_prime = VReplicaSetReconcileState {
            reconcile_step: VReplicaSetReconcileStep::AfterUpdateVRSStatus,
            ..state
        };
        let filtered = filter_by_controller_owner(vrs.metadata().owner_references().unwrap());
        let owner_ref = filtered[0].clone();
        let req = KubeAPIRequest::GetThenUpdateStatusRequest(KubeGetThenUpdateStatusRequest {
            api_resource: VReplicaSet::api_resource(),
            name: vrs.metadata().name().unwrap(),
            namespace: vrs.metadata().namespace().unwrap(),
            owner_ref: owner_ref,
            obj: new_vrs.marshal(),
        });
        return (state_prime, Some(Request::KRequest(req)));
    } else {
        return (error_state(state), None);
    }
}

fn filter_by_controller_owner(owner_refs: Vec<OwnerReference>) -> (res: Vec<OwnerReference>)
    ensures
        res.deep_view() == owner_refs.deep_view().filter(controller_owner_filter()),
{
    let mut filtered = Vec::new();

    proof {
        assert_seqs_equal!(
            filtered.deep_view(),
            owner_refs.deep_view().take(0).filter(controller_owner_filter())
        );
    }

    for idx in 0..owner_refs.len()
        invariant
            idx <= owner_refs.len(),
            filtered.deep_view()
                == owner_refs.deep_view().take(idx as int).filter(controller_owner_filter()),
    {
        let owner_ref = &owner_refs[idx];
        if is_controller_owner(owner_ref.clone()) {
            filtered.push(owner_ref.clone());
        }

        proof {
            let pred = controller_owner_filter();
            let old_filtered = if pred(owner_ref@) {
                filtered.deep_view().drop_last()
            } else {
                filtered.deep_view()
            };
            assert(old_filtered == owner_refs.deep_view().take(idx as int).filter(pred));
            lemma_filter_push(owner_refs.deep_view().take(idx as int), pred, owner_ref@);
            assert(owner_refs.deep_view().take(idx as int).push(owner_ref@)
                   == owner_refs.deep_view().take((idx + 1) as int));
            assert(pred(owner_ref@) ==> filtered.deep_view() == old_filtered.push(owner_ref@));
        }
    }
    assert(owner_refs.deep_view() == owner_refs.deep_view().take(owner_refs.len() as int));
    filtered
}

fn is_controller_owner(owner_ref: OwnerReference) -> (res: bool)
    ensures res == controller_owner_filter()(owner_ref@)
{
    return owner_ref.controller().is_some() && owner_ref.controller().unwrap()
}

}
