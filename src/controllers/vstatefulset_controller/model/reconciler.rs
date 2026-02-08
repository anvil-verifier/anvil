use crate::kubernetes_api_objects::spec::{prelude::*, volume::*};
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vstatefulset_controller::trusted::{spec_types::*, step::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// TODO: Make the shim layer's requeue time configurable as we need multiple reconcile() to finish the job and the queue
// time is critical now

// TODO: Directly jump to DeleteOutdated if we already have desired number of replicas

pub struct VStatefulSetReconciler {}

pub struct VStatefulSetReconcileState {
    pub reconcile_step: VStatefulSetReconcileStepView,
    // needed contains all the pods that should be running
    // if the pod doesn't exist yet, the cell will be None
    pub needed: Seq<Option<PodView>>,
    // needed_index tracks how many pods have been created (or already exists) so far
    pub needed_index: nat,
    // condemned contains all the pods that should be deleted because their ordinal is larger than desired replicas
    pub condemned: Seq<PodView>,
    // condemned_index tracks how many pods have been deleted
    pub condemned_index: nat,
    // pvcs contains the persistent volume claims that need to be created for each needed pod
    pub pvcs: Seq<PersistentVolumeClaimView>,
    // pvc_index tracks how many persistent volume claims have been created (or already exists) for each pod
    // pvc_index will be reset when we move to a new pod
    pub pvc_index: nat,
}

impl Reconciler<VStatefulSetReconcileState, VStatefulSetView, VoidEReqView, VoidERespView> for VStatefulSetReconciler {
    open spec fn reconcile_init_state() -> VStatefulSetReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(vrs: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
        reconcile_core(vrs, resp_o, state)
    }

    open spec fn reconcile_done(state: VStatefulSetReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: VStatefulSetReconcileState) -> bool {
        reconcile_error(state)
    }
}

pub open spec fn reconcile_init_state() -> VStatefulSetReconcileState {
    VStatefulSetReconcileState {
        reconcile_step: VStatefulSetReconcileStepView::Init,
        needed: Seq::empty(),
        needed_index: 0,
        condemned: Seq::empty(),
        condemned_index: 0,
        pvcs: Seq::empty(),
        pvc_index: 0,
    }
}

pub open spec fn reconcile_done(state: VStatefulSetReconcileState) -> bool {
    match state.reconcile_step {
        VStatefulSetReconcileStepView::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: VStatefulSetReconcileState) -> bool {
    match state.reconcile_step {
        VStatefulSetReconcileStepView::Error => true,
        _ => false,
    }
}

// The VSTS controller manages pods and volumes to run stateful, distributed applications.
// The controller does two things: managing replicas and versions.
//
// Managing replicas:
// The controller first lists all the pods managed by it, and then checks how many pods
// it needs to create or delete. For example, if the desired replicas is 5 and list returns
// [pod-0, pod-2, pod-4, pod-5], the controller will first create pod-1 and pod-3, and then
// delete pod-5. For the already running pod-0, pod-2, and pod-4, the controller will configure
// their network and storage to make sure the pods are running well.
//
// Managing versions:
// After creating and deleting the pods, the controller now has desired number of pods.
// Next, the controller will make sure all pods are running the desired version (the pod template).
// Since many pod fields are immutable, the controller will pick the outdated pod with
// the largest ordinal and then delete the pod, instead of updating the pod.
// After this deletion, the controller will end reconcile(), which means that the desired
// state will not be achieved in just one round of reconciliation. The remaining job will
// be done by the next round of reconcile---the controller will get [pod-0, ...pod-3] by list,
// and then it will create a new pod-4 with the new template, and then delete the next outdated pod.
pub open spec fn reconcile_core(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    match state.reconcile_step {
        VStatefulSetReconcileStepView::Init => {
            handle_init(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::AfterListPod => {
            handle_after_list_pod(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::GetPVC => {
            handle_get_pvc(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::AfterGetPVC => {
            handle_after_get_pvc(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::CreatePVC => {
            handle_create_pvc(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::AfterCreatePVC => {
            handle_after_create_pvc(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::SkipPVC => {
            handle_skip_pvc(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::CreateNeeded => {
            handle_create_needed(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::AfterCreateNeeded => {
            handle_after_create_needed(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::UpdateNeeded => {
            handle_update_needed(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::AfterUpdateNeeded => {
            handle_after_update_needed(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::DeleteCondemned => {
            handle_delete_condemned(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::AfterDeleteCondemned => {
            handle_after_delete_condemned(vsts, resp_o, state)
        },
        // At this point, we should have desired number of replicas running (tho with old versions).
        // The next step DeleteOutdated deletes the old replica with largest ordinal, and the next
        // reconcile will do the remaining jobs to start a new one (and delete the next old one).
        VStatefulSetReconcileStepView::DeleteOutdated => {
            handle_delete_outdated(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::AfterDeleteOutdated => {
            handle_after_delete_outdated(vsts, resp_o, state)
        },
        _ => {
            (state, None)
        }
    }
}

pub open spec fn handle_init(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if vsts.metadata.deletion_timestamp.is_some() {
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStepView::Done,
            ..state
        };
        (state_prime, None)
    } else {
        let req = APIRequest::ListRequest(ListRequest {
            kind: PodView::kind(),
            namespace: vsts.metadata.namespace->0,
        });
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStepView::AfterListPod,
            ..state
        };
        (state_prime, Some(RequestView::KRequest(req)))
    }
}

pub open spec fn handle_after_list_pod(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if is_some_k_list_resp_view(resp_o) && extract_some_k_list_resp_view(resp_o) is Ok {
        let objs = extract_some_k_list_resp_view(resp_o)->Ok_0;
        let pods_or_none = objects_to_pods(objs);
        if pods_or_none is None {
            (error_state(state), None)
        } else {
            let pods = pods_or_none->0;
            let filtered_pods = pods.filter(pod_filter(vsts));
            let replicas = vsts.spec.replicas.unwrap_or(1); // 1 by default
            if replicas >= 0 {
                let (needed, condemned) = partition_pods(vsts.metadata.name->0, replicas as nat, filtered_pods);
                let needed_index = 0;
                let condemned_index = 0;
                let pvc_index = 0;
                let pvcs = make_pvcs(vsts, 0);

                let state_without_step = VStatefulSetReconcileState {
                    needed: needed,
                    condemned: condemned,
                    pvcs: pvcs,
                    needed_index: needed_index,
                    condemned_index: condemned_index,
                    pvc_index: pvc_index,
                    ..state
                };

                if needed_index < needed.len() {
                    // There are more pods to create/update
                    if pvcs.len() > 0 {
                        // There is at least one pvc for the next pod to handle
                        (VStatefulSetReconcileState {
                            reconcile_step: VStatefulSetReconcileStepView::GetPVC,
                            ..state_without_step
                        }, None)
                    } else {
                        // There is no pvc to handle, so handle the next pod directly
                        if needed[needed_index as int] is None {
                            // Create the pod
                            (VStatefulSetReconcileState {
                                reconcile_step: VStatefulSetReconcileStepView::CreateNeeded,
                                ..state_without_step
                            }, None)
                        } else {
                            // Update the pod
                            (VStatefulSetReconcileState {
                                reconcile_step: VStatefulSetReconcileStepView::UpdateNeeded,
                                ..state_without_step
                            }, None)
                        }
                    }
                } else {
                    if condemned_index < condemned.len() {
                        (VStatefulSetReconcileState {
                            reconcile_step: VStatefulSetReconcileStepView::DeleteCondemned,
                            pvc_index: pvcs.len(), // reset the index when entering DeleteCondemned state
                            ..state_without_step
                        }, None)
                    } else {
                        (VStatefulSetReconcileState {
                            reconcile_step: VStatefulSetReconcileStepView::DeleteOutdated,
                            pvc_index: pvcs.len(),
                            ..state_without_step
                        }, None)
                    }
                }
            } else {
                (error_state(state), None)
            }
        }
    } else {
        (error_state(state), None)
    }
}

pub open spec fn handle_get_pvc(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if state.pvc_index < state.pvcs.len() && state.pvcs[state.pvc_index as int].metadata.name is Some {
        let req = APIRequest::GetRequest(GetRequest {
            key: ObjectRef {
                kind: PersistentVolumeClaimView::kind(),
                name: state.pvcs[state.pvc_index as int].metadata.name->0,
                namespace: vsts.metadata.namespace->0,
            }
        });
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStepView::AfterGetPVC,
            ..state
        };
        (state_prime, Some(RequestView::KRequest(req)))
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub open spec fn handle_after_get_pvc(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if is_some_k_get_resp_view(resp_o) {
        let result = extract_some_k_get_resp_view(resp_o);
        if result is Ok {
            // The pvc exists, so we don't do anything to it
            let state_prime = VStatefulSetReconcileState {
                reconcile_step: VStatefulSetReconcileStepView::SkipPVC,
                ..state
            };
            (state_prime, None)
        } else {
            if result->Err_0 is ObjectNotFound {
                // The pvc doesn't exists, so we create it in the next step
                let state_prime = VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::CreatePVC,
                    ..state
                };
                (state_prime, None)
            } else {
                (error_state(state), None)
            }
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub open spec fn handle_create_pvc(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if state.pvc_index < state.pvcs.len() {
        let req = APIRequest::CreateRequest(CreateRequest {
            namespace: vsts.metadata.namespace->0,
            obj: state.pvcs[state.pvc_index as int].marshal(),
        });
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStepView::AfterCreatePVC,
            pvc_index: state.pvc_index + 1,
            ..state
        };
        (state_prime, Some(RequestView::KRequest(req)))
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub open spec fn handle_after_create_pvc(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if is_some_k_create_resp_view(resp_o) {
        let result = extract_some_k_create_resp_view(resp_o);
        if result is Ok || result->Err_0 is ObjectAlreadyExists {
            handle_after_create_or_skip_pvc_helper(vsts, state)
        } else {
            (error_state(state), None)
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub open spec fn handle_skip_pvc(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if state.pvc_index < state.pvcs.len() {
        // skip is done here, no AfterSkipPVC state
        let state_prime = VStatefulSetReconcileState {
            pvc_index: state.pvc_index + 1,
            ..state
        };
        handle_after_create_or_skip_pvc_helper(vsts, state_prime)
    } else {
        (error_state(state), None)
    }
}

pub open spec fn handle_after_create_or_skip_pvc_helper(vsts: VStatefulSetView, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if state.pvc_index < state.pvcs.len() {
        (VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStepView::GetPVC,
            ..state
        }, None)
    } else {
        if state.needed_index < state.needed.len() {
            // There is no pvc to handle, so handle the next pod
            if state.needed[state.needed_index as int] is None {
                // Create the pod
                (VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::CreateNeeded,
                    ..state
                }, None)
            } else {
                // Update the pod
                (VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::UpdateNeeded,
                    ..state
                }, None)
            }
        } else {
            // This should be unreachable
            (error_state(state), None)
        }
    }
}

pub open spec fn handle_create_needed(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if state.needed_index < state.needed.len() {
        let req = APIRequest::CreateRequest(CreateRequest {
            namespace: vsts.metadata.namespace->0,
            obj: make_pod(vsts, state.needed_index).marshal(),
        });
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStepView::AfterCreateNeeded,
            needed_index: state.needed_index + 1,
            ..state
        };
        (state_prime, Some(RequestView::KRequest(req)))
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub open spec fn handle_after_create_needed(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if is_some_k_create_resp_view(resp_o) {
        let result = extract_some_k_create_resp_view(resp_o);
        if result is Ok || result->Err_0 is ObjectAlreadyExists {
            handle_after_create_or_after_update_needed_helper(vsts, state)
        } else {
            (error_state(state), None)
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

// TODO: skip updating the pod if identity and storage already matches
pub open spec fn handle_update_needed(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if state.needed_index < state.needed.len() && state.needed[state.needed_index as int] is Some {
        let old_pod = state.needed[state.needed_index as int]->0;
        
        // addede this to be defensive, but it should actually be unreachable
        if old_pod.metadata.name is Some {
            let ordinal = state.needed_index;
            let new_pod = update_storage(vsts, update_identity(vsts, old_pod, ordinal), ordinal);
            let req = APIRequest::GetThenUpdateRequest(GetThenUpdateRequest {
                name: new_pod.metadata.name->0,
                namespace: vsts.metadata.namespace->0,
                owner_ref: vsts.controller_owner_ref(),
                obj: new_pod.marshal(),
            });
            let state_prime = VStatefulSetReconcileState {
                reconcile_step: VStatefulSetReconcileStepView::AfterUpdateNeeded,
                needed_index: state.needed_index + 1,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req)))
        } else {
            (error_state(state), None)
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub open spec fn handle_after_update_needed(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if is_some_k_get_then_update_resp_view(resp_o) {
        let result = extract_some_k_get_then_update_resp_view(resp_o);
        if result is Ok {
            handle_after_create_or_after_update_needed_helper(vsts, state)
        } else {
            (error_state(state), None)
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub open spec fn handle_after_create_or_after_update_needed_helper(vsts: VStatefulSetView, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if state.needed_index < state.needed.len() {
        // There are more pods to create/update
        let new_pvcs = make_pvcs(vsts, state.needed_index);
        let new_pvc_index = 0;
        if new_pvcs.len() > 0 {
            // There is at least one pvc for the next pod to handle
            (VStatefulSetReconcileState {
                reconcile_step: VStatefulSetReconcileStepView::GetPVC,
                pvcs: new_pvcs,
                pvc_index: new_pvc_index,
                ..state
            }, None)
        } else {
            // There is no pvc to handle, so handle the next pod directly
            if state.needed[state.needed_index as int] is None {
                // Create the pod
                (VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::CreateNeeded,
                    ..state
                }, None)
            } else {
                // Update the pod
                (VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::UpdateNeeded,
                    ..state
                }, None)
            }
        }
    } else {
        if state.condemned_index < state.condemned.len() {
            (VStatefulSetReconcileState {
                reconcile_step: VStatefulSetReconcileStepView::DeleteCondemned,
                ..state
            }, None)
        } else {
            (delete_outdated_state(state), None)
        }
    }
}

pub open spec fn handle_delete_condemned(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if state.condemned_index < state.condemned.len() {
        let condemned_pod = state.condemned[state.condemned_index as int];
        if condemned_pod.metadata.name is Some {
            let req = APIRequest::GetThenDeleteRequest(GetThenDeleteRequest {
                key: ObjectRef {
                    kind: PodView::kind(),
                    name: state.condemned[state.condemned_index as int].metadata.name->0,
                    namespace: vsts.metadata.namespace->0,
                },
                owner_ref: vsts.controller_owner_ref(),
            });
            let state_prime = VStatefulSetReconcileState {
                reconcile_step: VStatefulSetReconcileStepView::AfterDeleteCondemned,
                condemned_index: state.condemned_index + 1,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req)))
        } else {
            (error_state(state), None)
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub open spec fn handle_after_delete_condemned(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if is_some_k_get_then_delete_resp_view(resp_o) {
        let result = extract_some_k_get_then_delete_resp_view(resp_o);
        if result is Ok || result->Err_0 is ObjectNotFound {
            if state.condemned_index < state.condemned.len() {
                (VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::DeleteCondemned,
                    ..state
                }, None)
            } else {
                (delete_outdated_state(state), None)
            }
        } else {
            (error_state(state), None)
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub open spec fn handle_delete_outdated(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if let Some(pod) = get_largest_unmatched_pods(vsts, state.needed) {
        if pod.metadata.name is Some {
            let req = APIRequest::GetThenDeleteRequest(GetThenDeleteRequest {
                key: ObjectRef {
                    kind: PodView::kind(),
                    name: pod.metadata.name->0,
                    namespace: vsts.metadata.namespace->0,
                },
                owner_ref: vsts.controller_owner_ref(),
            });
            let state_prime = VStatefulSetReconcileState {
                reconcile_step: VStatefulSetReconcileStepView::AfterDeleteOutdated,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req)))
        } else {
            (error_state(state), None)
        }
    } else {
        (done_state(state), None)
    }
}

pub open spec fn handle_after_delete_outdated(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if is_some_k_get_then_delete_resp_view(resp_o) {
        let result = extract_some_k_get_then_delete_resp_view(resp_o);
        if result is Ok || result->Err_0 is ObjectNotFound {
            (done_state(state), None)
        } else {
            (error_state(state), None)
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub open spec fn delete_outdated_state(state: VStatefulSetReconcileState) -> VStatefulSetReconcileState {
    VStatefulSetReconcileState {
        reconcile_step: VStatefulSetReconcileStepView::DeleteOutdated,
        ..state
    }
}

pub open spec fn done_state(state: VStatefulSetReconcileState) -> VStatefulSetReconcileState {
    VStatefulSetReconcileState {
        reconcile_step: VStatefulSetReconcileStepView::Done,
        ..state
    }
}

pub open spec fn error_state(state: VStatefulSetReconcileState) -> VStatefulSetReconcileState {
    VStatefulSetReconcileState {
        reconcile_step: VStatefulSetReconcileStepView::Error,
        ..state
    }
}

pub open spec fn objects_to_pods(objs: Seq<DynamicObjectView>) -> Option<Seq<PodView>> {
    if objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() != 0 {
        None
    } else {
        Some(objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()))
    }
}

pub open spec fn pod_name_without_vsts_prefix(parent_name: StringView, ordinal: nat) -> StringView {
    parent_name + "-"@ + int_to_string_view(ordinal as int)
}

pub open spec fn pod_name(parent_name: StringView, ordinal: nat) -> StringView {
    VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + pod_name_without_vsts_prefix(parent_name, ordinal)
}

pub open spec fn pod_filter(vsts: VStatefulSetView) -> spec_fn(PodView) -> bool {
    |pod: PodView| {
        // See https://github.com/kubernetes/kubernetes/blob/master/pkg/controller/controller_ref_manager.go#L72-L82
        pod.metadata.owner_references_contains(vsts.controller_owner_ref())
        // && vsts.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
        // See https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/controller/statefulset/stateful_set.go#L311-L314
        && vsts.metadata.name is Some
        && pod.metadata.name is Some
        && get_ordinal(vsts.metadata.name->0, pod.metadata.name->0) is Some
    }
}

pub open spec fn get_ordinal(parent_name: StringView, compared_pod_name: StringView) -> Option<nat> {
    if (exists |ord| compared_pod_name == pod_name(parent_name, ord)) {
        Some(choose |ord| compared_pod_name == pod_name(parent_name, ord))
    } else {
        None
    }
}

pub open spec fn pod_has_ord(parent_name: StringView, ord: nat) -> (spec_fn(PodView) -> bool) {
    |pod: PodView| get_ordinal(parent_name, pod.metadata.name->0) == Some(ord)
}

pub open spec fn get_pod_with_ord(parent_name: StringView, pods: Seq<PodView>, ord: nat) -> Option<PodView> {
    let filtered = pods.filter(pod_has_ord(parent_name, ord));
    if filtered.len() > 0 {
        Some(filtered[0])
    } else {
        None
    }
}

pub open spec fn partition_pods(parent_name: StringView, replicas: nat, pods: Seq<PodView>) -> (Seq<Option<PodView>>, Seq<PodView>) {
    // needed includes all the pods that should be created or updated
    // creation/update will start with the beginning of needed where ordinal == 0
    let needed = Seq::<Option<PodView>>::new(replicas,
        |ord: int| get_pod_with_ord(parent_name, pods, ord as nat)
    );
    // condemned includes all the pods that should be deleted
    // condemned is sorted by the decreasing order of the ordinal number of each pod
    // deletion will start with the pod with the largest ordinal number
    let condemned = pods
        .filter(|pod: PodView| get_ordinal(parent_name, pod.metadata.name->0) is Some && get_ordinal(parent_name, pod.metadata.name->0)->0 >= replicas)
        .sort_by(|p1: PodView, p2: PodView| get_ordinal(parent_name, p1.metadata.name->0)->0 >= get_ordinal(parent_name, p2.metadata.name->0)->0);
    (needed, condemned)
}

pub open spec fn make_owner_references(vsts: VStatefulSetView) -> Seq<OwnerReferenceView> {
    seq![vsts.controller_owner_ref()]
}

// make_pod models https://github.com/kubernetes/kubernetes/blob/release-1.30/pkg/controller/statefulset/stateful_set_utils.go#L523
pub open spec fn make_pod(vsts: VStatefulSetView, ordinal: nat) -> PodView {
    let pod = PodView {
        metadata: {
            ObjectMetaView {
                name: Some(pod_name(vsts.metadata.name->0, ordinal)),
                labels: vsts.spec.template.metadata->0.labels,
                annotations: vsts.spec.template.metadata->0.annotations,
                finalizers: vsts.spec.template.metadata->0.finalizers,
                owner_references: Some(make_owner_references(vsts)),
                ..ObjectMetaView::default()
            }
        },
        spec: vsts.spec.template.spec,
        ..PodView::default()
    };
    // Set network identity and storage related fields
    update_storage(vsts, init_identity(vsts, pod, ordinal), ordinal)
}

pub open spec fn init_identity(vsts: VStatefulSetView, pod: PodView, ordinal: nat) -> PodView {
    let updated_pod = update_identity(vsts, pod, ordinal);
    PodView {
        spec: Some(PodSpecView {
            hostname: updated_pod.metadata.name,
            subdomain: Some(vsts.spec.service_name),
            ..updated_pod.spec->0
        }),
        ..updated_pod
    }
}

pub open spec fn update_identity(vsts: VStatefulSetView, pod: PodView, ordinal: nat) -> PodView {
    PodView {
        metadata: ObjectMetaView {
            labels: Some(vsts.spec.template.metadata->0.labels
                    .unwrap_or(Map::<StringView, StringView>::empty())
                    .insert(StatefulSetPodNameLabel, pod.metadata.name->0)
                    .insert(StatefulSetOrdinalLabel, int_to_string_view(ordinal as int))),
            ..pod.metadata
        },
        ..pod
    }
}

pub open spec fn pvc_name(pvc_template_name: StringView, vsts_name: StringView, ordinal: nat) -> StringView {
    VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + pvc_template_name + "-"@ + pod_name_without_vsts_prefix(vsts_name, ordinal)
}

pub open spec fn make_pvc(vsts: VStatefulSetView, ordinal: nat, i: int) -> PersistentVolumeClaimView {
    let pvc_template = vsts.spec.volume_claim_templates->0[i];
    PersistentVolumeClaimView {
        metadata: ObjectMetaView {
            name: Some(pvc_name(pvc_template.metadata.name->0, vsts.metadata.name->0, ordinal)),
            namespace: vsts.metadata.namespace,
            labels: if pvc_template.metadata.labels is Some {
                if vsts.spec.selector.match_labels is Some {
                    Some(pvc_template.metadata.labels->0.union_prefer_right(vsts.spec.selector.match_labels->0))
                } else {
                    pvc_template.metadata.labels
                }
            } else {
                vsts.spec.selector.match_labels
            },
            ..ObjectMetaView::default()
        },
        spec: vsts.spec.volume_claim_templates->0[i].spec,
        ..PersistentVolumeClaimView::default()
    }
}

pub open spec fn make_pvcs(vsts: VStatefulSetView, ordinal: nat) -> Seq<PersistentVolumeClaimView> {
    if vsts.spec.volume_claim_templates is Some {
        Seq::new(vsts.spec.volume_claim_templates->0.len(), |i| make_pvc(vsts, ordinal, i))
    } else {
        Seq::empty()
    }
}

pub open spec fn update_storage(vsts: VStatefulSetView, pod: PodView, ordinal: nat) -> PodView {
    let pvcs = make_pvcs(vsts, ordinal);
    let templates = vsts.spec.volume_claim_templates->0;
    let current_volumes = if pod.spec->0.volumes is Some { pod.spec->0.volumes->0 } else { Seq::<VolumeView>::empty() };
    let new_volumes = if vsts.spec.volume_claim_templates is Some {
        Seq::new(templates.len(), |i| VolumeView {
            name: templates[i].metadata.name->0,
            persistent_volume_claim: Some(PersistentVolumeClaimVolumeSourceView {
                claim_name: pvcs[i].metadata.name->0,
                read_only: Some(false),
            }),
            ..VolumeView::default()
        })
    } else {
        Seq::empty()
    };
    // We only want to keep the current volumes whose names don't appear in templates
    let filtered_current_volumes = current_volumes
        .filter(|vol: VolumeView| templates.all(|template: PersistentVolumeClaimView| vol.name != template.metadata.name->0));
    PodView {
        spec: Some(PodSpecView {
            volumes: Some(new_volumes.add(filtered_current_volumes)),
            ..pod.spec->0
        }),
        ..pod
    }
}

pub open spec fn identity_matches(vsts: VStatefulSetView, pod: PodView) -> bool {
    pod.metadata.labels is Some
    && pod.metadata.labels->0.contains_key("statefulset.kubernetes.io/pod-name"@)
    && pod.metadata.labels->0["statefulset.kubernetes.io/pod-name"@] == pod.metadata.name->0
}

pub open spec fn storage_matches(vsts: VStatefulSetView, pod: PodView) -> bool {
    let claims = vsts.spec.volume_claim_templates->0;
    let volumes = pod.spec->0.volumes->0;
    let ordinal = get_ordinal(vsts.metadata.name->0, pod.metadata.name->0);
    vsts.spec.volume_claim_templates is Some
    ==> pod.spec->0.volumes is Some
        && forall |i: int| #![trigger claims[i]] 0 <= i < claims.len()
            ==> exists |j: int| #![trigger volumes[j]] 0 <= j < volumes.len()
                    && volumes[j].name == claims[i].metadata.name->0
                    && volumes[j].persistent_volume_claim is Some
                    && ordinal is Some
                    && volumes[j].persistent_volume_claim->0.claim_name == pvc_name(claims[i].metadata.name->0, vsts.metadata.name->0, ordinal->0)
}

// TODO: compare other fields of the pod if necessary
pub open spec fn pod_spec_matches(vsts: VStatefulSetView, pod: PodView) -> bool {
    // from validation we know vsts.spec.template.spec is Some
    &&& pod.spec is Some
    &&& pod.spec->0.without_volumes().without_hostname().without_subdomain()
        == vsts.spec.template.spec->0.without_volumes().without_hostname().without_subdomain()
}

pub open spec fn outdated_pod_filter(vsts: VStatefulSetView) -> spec_fn(Option<PodView>) -> bool {
    |pod_or_none: Option<PodView>| {
        let pod = pod_or_none->0;
        &&& pod_or_none is Some
        &&& !pod_spec_matches(vsts, pod)
    }
} 

pub open spec fn get_largest_unmatched_pods(vsts: VStatefulSetView, pods: Seq<Option<PodView>>) -> Option<PodView> {
    let filtered = pods.filter(outdated_pod_filter(vsts));
    if filtered.len() > 0 {
        filtered.last()
    } else {
        None
    }
}

}
