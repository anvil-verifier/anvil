use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vreplicaset_controller::trusted::{spec_types::*, step::*};
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;


verus! {

pub struct VReplicaSetReconciler {}

pub struct VReplicaSetReconcileState {
    pub reconcile_step: VReplicaSetRecStepView,
    pub filtered_pods: Option<Seq<PodView>>,
}

impl Reconciler<VReplicaSetReconcileState, VReplicaSetView, VoidEReqView, VoidERespView> for VReplicaSetReconciler {
    open spec fn reconcile_init_state() -> VReplicaSetReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(vrs: VReplicaSetView, resp_o: Option<ResponseView<VoidERespView>>, state: VReplicaSetReconcileState) -> (VReplicaSetReconcileState, Option<RequestView<VoidEReqView>>) {
        reconcile_core(vrs, resp_o, state)
    }

    open spec fn reconcile_done(state: VReplicaSetReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: VReplicaSetReconcileState) -> bool {
        reconcile_error(state)
    }
}

pub open spec fn reconcile_init_state() -> VReplicaSetReconcileState {
    VReplicaSetReconcileState {
        reconcile_step: VReplicaSetRecStepView::Init,
        filtered_pods: None,
    }
}

pub open spec fn reconcile_done(state: VReplicaSetReconcileState) -> bool {
    match state.reconcile_step {
        VReplicaSetRecStepView::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: VReplicaSetReconcileState) -> bool {
    match state.reconcile_step {
        VReplicaSetRecStepView::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(vrs: VReplicaSetView, resp_o: Option<ResponseView<VoidERespView>>, state: VReplicaSetReconcileState) -> (VReplicaSetReconcileState, Option<RequestView<VoidEReqView>>) {
    let namespace = vrs.metadata.namespace.unwrap();
    match &state.reconcile_step {
        VReplicaSetRecStepView::Init => {
            if vrs.metadata.deletion_timestamp.is_some() {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetRecStepView::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                let req = APIRequest::ListRequest(ListRequest {
                    kind: PodView::kind(),
                    namespace: namespace,
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetRecStepView::AfterListPods,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req)))
            }
        },
        VReplicaSetRecStepView::AfterListPods => {
            if !(is_some_k_list_resp_view(resp_o) && extract_some_k_list_resp_view(resp_o) is Ok) {
                (error_state(state), None)
            } else {
                let objs = extract_some_k_list_resp_view(resp_o).unwrap();
                let pods_or_none = objects_to_pods(objs);
                if pods_or_none.is_none() {
                    (error_state(state), None)
                } else {
                    let pods = pods_or_none.unwrap();
                    let filtered_pods = filter_pods(pods, vrs);
                    let replicas = vrs.spec.replicas.unwrap_or(1);
                    if replicas < 0 {
                        (error_state(state), None)
                    } else {
                        let desired_replicas = replicas;
                        if filtered_pods.len() == desired_replicas {
                            update_vrs_replicas(state, vrs)
                        } else if filtered_pods.len() < desired_replicas {
                            let diff =  desired_replicas - filtered_pods.len();
                            let pod = make_pod(vrs);
                            let req = APIRequest::CreateRequest(CreateRequest {
                                namespace: namespace,
                                obj: pod.marshal(),
                            });
                            let state_prime = VReplicaSetReconcileState {
                                reconcile_step: VReplicaSetRecStepView::AfterCreatePod((diff - 1) as nat),
                                ..state
                            };
                            (state_prime, Some(RequestView::KRequest(req)))
                        } else {
                            let diff = filtered_pods.len() - desired_replicas;
                            let pod_name_or_none = filtered_pods[diff - 1].metadata.name;
                            if pod_name_or_none.is_none() {
                                (error_state(state), None)
                            } else {
                                let req = APIRequest::GetThenDeleteRequest(GetThenDeleteRequest {
                                    key: ObjectRef {
                                        kind: PodView::kind(),
                                        name: pod_name_or_none.unwrap(),
                                        namespace: namespace,
                                    },
                                    owner_ref: vrs.controller_owner_ref(),
                                });
                                let state_prime = VReplicaSetReconcileState {
                                    reconcile_step: VReplicaSetRecStepView::AfterDeletePod((diff - 1) as nat),
                                    filtered_pods: Some(filtered_pods),
                                    ..state
                                };
                                (state_prime, Some(RequestView::KRequest(req)))
                            }
                        }
                    }
                }
            }
        },
        VReplicaSetRecStepView::AfterCreatePod(diff) => {
            let diff = *diff;
            if !(is_some_k_create_resp_view(resp_o) && extract_some_k_create_resp_view(resp_o) is Ok) {
                (error_state(state), None)
            } else if diff == 0 {
                update_vrs_replicas(state, vrs)
            } else {
                let pod = make_pod(vrs);
                let req = APIRequest::CreateRequest(CreateRequest {
                    namespace: namespace,
                    obj: pod.marshal(),
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetRecStepView::AfterCreatePod((diff - 1) as nat),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req)))
            }
        },
        VReplicaSetRecStepView::AfterDeletePod(diff) => {
            let diff = *diff;
            if !(is_some_k_get_then_delete_resp_view(resp_o) && extract_some_k_get_then_delete_resp_view(resp_o) is Ok) {
                (error_state(state), None)
            } else if diff == 0 {
                update_vrs_replicas(state, vrs)
            } else {
                if state.filtered_pods.is_none() {
                    (error_state(state), None)
                } else if diff > state.filtered_pods.unwrap().len() {
                    (error_state(state), None)
                } else {
                    let pod_name_or_none = state.filtered_pods.unwrap()[diff - 1].metadata.name;
                    if pod_name_or_none.is_none() {
                        (error_state(state), None)
                    } else {
                        let req = APIRequest::GetThenDeleteRequest(GetThenDeleteRequest {
                            key: ObjectRef {
                                kind: PodView::kind(),
                                name: pod_name_or_none.unwrap(),
                                namespace: namespace,
                            },
                            owner_ref: vrs.controller_owner_ref(),
                        });
                        let state_prime = VReplicaSetReconcileState {
                            reconcile_step: VReplicaSetRecStepView::AfterDeletePod((diff - 1) as nat),
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req)))
                    }
                }
            }
        },
        VReplicaSetRecStepView::AfterUpdateVRSStatus => {
            if !(is_some_k_get_then_update_status_resp_view(resp_o) && extract_some_k_get_then_update_status_resp_view(resp_o) is Ok) {
                (error_state(state), None)
            } else {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetRecStepView::Done,
                    ..state
                };
                (state_prime, None)
            }
        },
        _ => {
            (state, None)
        }
    }
}

pub open spec fn error_state(state: VReplicaSetReconcileState) -> (state_prime: VReplicaSetReconcileState)
{
    VReplicaSetReconcileState {
        reconcile_step: VReplicaSetRecStepView::Error,
        ..state
    }
}

pub open spec fn objects_to_pods(objs: Seq<DynamicObjectView>) -> (pods_or_none: Option<Seq<PodView>>) {
    if objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() != 0 {
        None
    } else {
        Some(objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()))
    }
}

pub open spec fn filter_pods(pods: Seq<PodView>, vrs: VReplicaSetView) -> (filtered_pods: Seq<PodView>) {
    pods.filter(pod_filter(vrs))
}

pub open spec fn pod_filter(vrs: VReplicaSetView) -> spec_fn(pod: PodView) -> bool {
    |pod: PodView| {
        &&& pod.metadata.owner_references_contains(vrs.controller_owner_ref())
        &&& vrs.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
        &&& pod.metadata.deletion_timestamp is None
        &&& pod.metadata.name is Some
        &&& has_vrs_prefix(pod.metadata.name.unwrap())
    }
}

pub open spec fn has_vrs_prefix(name: StringView) -> bool {
    exists |suffix| name == VReplicaSetView::kind()->CustomResourceKind_0 + "-"@ + suffix
}

pub open spec fn pod_generate_name(vrs: VReplicaSetView) -> StringView {
    VReplicaSetView::kind()->CustomResourceKind_0 + "-"@ + vrs.metadata.name.unwrap() + "-"@
}

pub open spec fn make_pod(vrs: VReplicaSetView) -> (pod: PodView) {
    let template = vrs.spec.template.unwrap();
    let pod = PodView::default();
    let pod = PodView {
        spec: template.spec,
        metadata: {
            let tm = template.metadata.unwrap();
            let metadata = ObjectMetaView::default();
            let metadata = ObjectMetaView {
                labels: tm.labels,
                annotations: tm.annotations,
                finalizers: tm.finalizers,
                ..metadata
            };
            let metadata = metadata.with_generate_name(
                pod_generate_name(vrs)
            );
            let metadata = metadata.with_owner_references(
                make_owner_references(vrs)
            );
            metadata
        },
        ..pod
    };
    pod
}

pub open spec fn make_owner_references(vrs: VReplicaSetView) -> Seq<OwnerReferenceView> { seq![vrs.controller_owner_ref()] }

pub open spec fn update_vrs_replicas(
    state: VReplicaSetReconcileState, vrs: VReplicaSetView
) -> (res: (VReplicaSetReconcileState, Option<RequestView<VoidEReqView>>)) {
    if vrs.metadata.owner_references is Some && vrs.metadata.owner_references.unwrap().filter(controller_owner_filter()).len() == 1 {
        let vrs_with_new_status = VReplicaSetView {
            status: Some(VReplicaSetStatusView {
                replicas: vrs.spec.replicas.unwrap_or(1),
            }),
            ..vrs
        };
        let state_prime = VReplicaSetReconcileState {
            reconcile_step: VReplicaSetRecStepView::AfterUpdateVRSStatus,
            ..state
        };
        let req = APIRequest::GetThenUpdateStatusRequest(GetThenUpdateStatusRequest {
            name: vrs.metadata.name.unwrap(),
            namespace: vrs.metadata.namespace.unwrap(),
            owner_ref: vrs.metadata.owner_references.unwrap().filter(controller_owner_filter())[0],
            obj: vrs_with_new_status.marshal(),
        });
        (state_prime, Some(RequestView::KRequest(req)))
    } else {
        (error_state(state), None)
    }
}

}
