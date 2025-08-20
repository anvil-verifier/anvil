use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vreplicaset_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;

verus! {

pub struct VStatefulSetReconciler {}

pub struct VStatefulSetReconcileState {
    pub reconcile_step: VStatefulSetReconcileStepView,
    pub needed: Option<Seq<PodView>>,
    pub condemned: Option<Seq<PodView>>,
}

impl Reconciler<VStatefulSetReconcileState, VStatefulSetView, VoidEReqView, VoidERespView> for VStatefulSetReconciler {
    open spec fn reconcile_init_state() -> VStatefulSetReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(vrs: VStatefulSetView, resp_o: Option<ResponseView<VoidERespView>>, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, Option<RequestView<VoidEReqView>>) {
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
        needed: None,
        condemned: None,
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

pub open spec fn reconcile_core(vsts: VStatefulSetView, resp_o: Option<ResponseView<VoidERespView>>, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, Option<RequestView<VoidEReqView>>) {
    let namespace = vsts.metadata.namespace.unwrap();
    match &state.reconcile_step {
        VStatefulSetReconcileStepView::Init => {
            if vsts.metadata.deletion_timestamp.is_some() {
                let state_prime = VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                let req = APIRequest::ListRequest(ListRequest {
                    kind: PodView::kind(),
                    namespace: namespace,
                });
                let state_prime = VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::AfterListPods,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req)))
            }
        },
        VStatefulSetReconcileStepView::AfterListPods => {
            if !(is_some_k_list_resp_view!(resp_o) && extract_some_k_list_resp_view!(resp_o) is Ok) {
                (error_state(state), None)
            } else {
                let objs = extract_some_k_list_resp_view!(resp_o).unwrap();
                let pods_or_none = objects_to_pods(objs);
                if pods_or_none.is_none() {
                    (error_state(state), None)
                } else {
                    let pods = pods_or_none.unwrap();
                    let filtered_pods = filter_pods(pods, vsts);
                    let replicas = vsts.spec.replicas.unwrap_or(0);
                    if replicas < 0 {
                        (error_state(state), None)
                    } else {
                        let desired_replicas = replicas;
                        if filtered_pods.len() == desired_replicas {
                            let state_prime = VStatefulSetReconcileState {
                                reconcile_step: VStatefulSetReconcileStepView::Done,
                                ..state
                            };
                            (state_prime, None)
                        } else if filtered_pods.len() < desired_replicas {
                            let diff =  desired_replicas - filtered_pods.len();
                            let pod = make_pod(vsts);
                            let req = APIRequest::CreateRequest(CreateRequest {
                                namespace: namespace,
                                obj: pod.marshal(),
                            });
                            let state_prime = VStatefulSetReconcileState {
                                reconcile_step: VStatefulSetReconcileStepView::AfterCreatePod((diff - 1) as nat),
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
                                    owner_ref: vsts.controller_owner_ref(),
                                });
                                let state_prime = VStatefulSetReconcileState {
                                    reconcile_step: VStatefulSetReconcileStepView::AfterDeletePod((diff - 1) as nat),
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
        VStatefulSetReconcileStepView::AfterCreatePod(diff) => {
            let diff = *diff;
            if !(is_some_k_create_resp_view!(resp_o) && extract_some_k_create_resp_view!(resp_o) is Ok) {
                (error_state(state), None)
            } else if diff == 0 {
                let state_prime = VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                let pod = make_pod(vsts);
                let req = APIRequest::CreateRequest(CreateRequest {
                    namespace: namespace,
                    obj: pod.marshal(),
                });
                let state_prime = VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::AfterCreatePod((diff - 1) as nat),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req)))
            }
        },
        VStatefulSetReconcileStepView::AfterDeletePod(diff) => {
            let diff = *diff;
            if !(is_some_k_get_then_delete_resp_view!(resp_o) && extract_some_k_get_then_delete_resp_view!(resp_o) is Ok) {
                (error_state(state), None)
            } else if diff == 0 {
                let state_prime = VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::Done,
                    ..state
                };
                (state_prime, None)
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
                            owner_ref: vsts.controller_owner_ref(),
                        });
                        let state_prime = VStatefulSetReconcileState {
                            reconcile_step: VStatefulSetReconcileStepView::AfterDeletePod((diff - 1) as nat),
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req)))
                    }
                }
            }
        },
        _ => {
            (state, None)
        }
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

pub open spec fn filter_pods(pods: Seq<PodView>, vsts: VStatefulSetView) -> Seq<PodView> {
    pods.filter(|pod: PodView|
        // See https://github.com/kubernetes/kubernetes/blob/master/pkg/controller/controller_ref_manager.go#L72-L82
        pod.metadata.owner_references_contains(vsts.controller_owner_ref())
        && vsts.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
        // See https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/controller/statefulset/stateful_set.go#L311-L314
        && exists |i: nat| pod.metadata.name->0 == vsts.metadata.name->0 + int_to_string_view(i as int)
    )
}

pub open spec fn make_owner_references(vsts: VStatefulSetView) -> Seq<OwnerReferenceView> {
    seq![vsts.controller_owner_ref()]
}

pub open spec fn pod_name(vsts_name: StringView, ordinal: nat) -> StringView {
    vsts_name + "-"@ + int_to_string_view(ordinal as int)
}

pub open spec fn make_pod(vsts: VStatefulSetView, ordinal: nat) -> PodView {
    let template = vsts.spec.template.unwrap();
    let tm = template.metadata.unwrap();
    PodView {
        metadata: {
            ObjectMetaView {
                name: Some(pod_name(vsts.metadata.name->0, ordinal)),
                labels: tm.labels,
                annotations: tm.annotations,
                finalizers: tm.finalizers,
                owner_references: Some(make_owner_references(vsts)),
                ..ObjectMetaView::default()
            }
        },
        spec: template.spec,
        ..PodView::default()
    }
}

pub open spec fn init_identity(vsts: VStatefulSetView, pod: PodView, ordinal: nat) -> PodView {
    let updated_pod = update_identity(vsts, pod, ordinal);
    PodView {
        spec: Some(PodSpecView {
            hostname: updated_pod.metadata.name,
            subdomain: Some(vsts.spec.service_name),
            ..updated_pod.spec->0
        }),
        ....updated_pod
    }
}

pub open spec fn update_identity(vsts: VStatefulSetView, pod: PodView, ordinal: nat) -> PodView {
    PodView {
        metadata: ObjectMeta {
            labels: if pod.metadata.labels is None {
                    Map::<StringView, StringView>::empty()
                } else {
                    pod.metadata.labels->0
                }.insert("statefulset.kubernetes.io/pod-name"@, pod.metadata.name->0)
                .insert("apps.kubernetes.io/pod-index"@, int_to_string_view(ordinal)),
            ..pod.metadata
        }
    }
}

pub open spec fn pvc_name(pvc_template_name: StringView, vsts_name: StringView, ordinal: nat) -> StringView {
    pvc_template_name + "-"@ + pod_name(vsts_name, ordinal)
}

// TODO: pvc_template.metadata.name should not be None; implement the check in validation logic
pub open spec fn make_pvc(vsts: VStatefulSetView, ordinal: nat, i: int) -> PersistentVolumeClaimView {
    let pvc_template = vsts.spec.volume_claim_templates->0[i];
    PersistentVolumeClaim {
        metadata: ObjectMetaView {
            name: Some(pvc_name(pvc_template.metadata.name->0, vsts.metadata.name->0, ordinal)),
            namespace: vsts.metadata.namespace,
            labels: {
                if pvc_template.metadata.labels is Some {
                    if vsts.metadata.selector.match_labels is Some {
                        Some(pvc_template.metadata.labels->0.extend(vsts.metadata.selector.match_labels->0))
                    } else {
                        pvc_template.metadata.labels
                    }
                } else {
                    vsts.metadata.selector.match_labels
                }
            }
        },
        spec: vsts.spec.volume_claim_templates[i].spec,
    }
}

pub open spec fn make_pvcs(vsts: VStatefulSetView, ordinal: nat) -> Map<StringView, PersistentVolumeClaimView> {
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
            name: templates[i].name->0,
            persistent_volume_claim: Some(PersistentVolumeClaimVolumeSourceView {
                claim_name: pvcs[i].name,
                read_only: Some(false),
            })
        })
    } else {
        Seq::empty()
    };
    // We only want to keep the current volumes whose names don't appear in templates
    let filtered_current_volumes = current_volumes.filter(|vol| templates.all(|template| vol.name != template.name->0));
    PodView {
        spec: Some(PodSpecView {
            volumes: Some(new_volumes.add(filtered_current_volumes)),
            ..pod.spec->0
        })
    }
}


}
