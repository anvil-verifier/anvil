use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vreplicaset_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;

verus! {

pub struct VStatefulSetReconciler {}

pub struct VStatefulSetReconcileState {
    pub reconcile_step: VStatefulSetReconcileStepView,
    pub needed: Seq<Option<PodView>>,
    pub needed_index: nat,
    pub condemned: Seq<PodView>,
    pub condemned_index: nat,
    pub pvcs: Seq<PersistentVolumeClaimView>,
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

pub enum VStatefulSetReconcileStepView {
    Init,
    AfterListPod,
    GetPVC,
    AfterGetPVC,
    CreatePVC,
    AfterCreatePVC,
    CreatePod,
    AfterCreatePod,
    DeletePod,
    AfterDeletePod,
    Done,
    Error,
}

pub open spec fn reconcile_core(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    let namespace = vsts.metadata.namespace.unwrap();
    match state.reconcile_step {
        VStatefulSetReconcileStepView::Init => {
            handle_init(vsts, resp_o, state)
        },
        VStatefulSetReconcileStepView::AfterListPods => {

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
            namespace: vsts.metadata.namespace.unwrap(),
        });
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStepView::AfterListPods,
            ..state
        };
        (state_prime, Some(RequestView::KRequest(req)))
    }
}

pub open spec fn handle_after_list_pod(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
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
            let desired_replicas = vsts.spec.replicas.unwrap_or(0);
            if desired_replicas < 0 {
                (error_state(state), None)
            } else {
                let (needed, condemned) = partition_pods(vsts, filter_pods);
                // Ensure the pvcs are ready before creating or updating the pod
                let state_prime = VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStepView::GetPVC,
                    needed_pods: needed,
                    needed_index: 0,
                    condemned_pods: condemned,
                    condemned_index: 0,
                    pvcs: make_pvcs(vsts, 0),
                    pvc_index: 0,
                };
                (state_prime, None)
            }
        }
    }
}

pub open spec fn handle_get_pvc(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if state.pvc_index < state.pvcs.len() {
        let req = APIRequest::GetRequest(GetRequest {
            key: ObjectRef {
                kind: PersistentVolumeClaimView::kind(),
                name: pvcs[state.pvc_index].metadata.name->0,
                namespace: vsts.metadata.namespace->0,
            }
        });
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStepView::AfterGetPVC,
            ..state
        };
        (state_prime, Some(RequestView::KRequest(req)))
    } else {
        // There is no more pvc to handle, now create/update the pod
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStepView::CreatePod,
            ..state
        };
        (state_prime, None)
    }
}

pub open spec fn handle_after_get_pvc(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if is_some_k_get_resp_view!(resp_o) {
        let result = extract_some_k_get_resp_view!(resp_o);
        if result is Err && result->Err_0 is ObjectNotFound {
            // The pvc doesn't exists, so we create it in the next step
            let state_prime = VStatefulSetReconcileState {
                reconcile_step: VStatefulSetReconcileStepView::CreatePVC,
                ..state
            };
            (state_prime, None)
        } else {
            (error_state(state), None)
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub open spec fn handle_create_pvc(vsts: VStatefulSetView, resp_o: DefaultResp, state: VStatefulSetReconcileState) -> (VStatefulSetReconcileState, DefaultReq) {
    if state.pvc_index < state.pvcs.len() {
        let req = APIRequest::CreateRequest(CreateRequest {
            namespace: namespace,
            obj: state.pvcs[state.pvc_index].marshal(),
        });
        let state_prime = VReplicaSetReconcileState {
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
    if is_some_k_create_resp_view!(resp_o) {
        let result = extract_some_k_create_resp_view!(resp_o);
        if result is Ok || (result is Err && result->Err_0 is ObjectAlreadyExists) {
            // The pvc is already there, now we handle the next pvc
            let state_prime = VStatefulSetReconcileState {
                reconcile_step: VStatefulSetReconcileStepView::GetPVC,
                ..state
            };
            (state_prime, None)
        } else {
            (error_state(state), None)
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
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

pub open spec fn pod_name(parent_name: StringView, ordinal: nat) -> StringView {
    parent_name + "-"@ + int_to_string_view(ordinal as int)
}

pub open spec fn filter_pods(pods: Seq<PodView>, vsts: VStatefulSetView) -> Seq<PodView> {
    pods.filter(|pod: PodView|
        // See https://github.com/kubernetes/kubernetes/blob/master/pkg/controller/controller_ref_manager.go#L72-L82
        pod.metadata.owner_references_contains(vsts.controller_owner_ref())
        && vsts.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
        // See https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/controller/statefulset/stateful_set.go#L311-L314
        && exists |ord: nat| pod.metadata.name->0 == pod_name(vsts.metadata.name->0, ord)
    )
}

pub open spec fn get_ordinal(parent_name: StringView, pod: PodView) -> nat {
    choose |ord| pod.metadata.name->0 == pod_name(parent_name, ord)
}

pub open spec fn partition_pods(vsts: VStatefulSetView, pods: Seq<PodView>) -> (Seq<Option<PodView>>, Seq<PodView>) {
    let replicas = vsts.spec.replicas.unwrap_or(0);
    let parent_name = vsts.metadata.name->0;
    // needed includes all the pods that should be created or updated
    // creation/update will start with the beginning of needed where ordinal == 0
    let needed = Seq::<Option<PodView>>::new(replicas,
        |ord| if exists |i| pods[i].metadata.name->0 == pod_name(parent_name, ord) {
            let i = choose |i| pods[i].metadata.name->0 == pod_name(parent_name, ord);
            Some(pods[i]) // The pod exists but might need to be updated
        } else {
            None // The pod doesn't exist so it needs to be created
        }
    );
    // condemned includes all the pods that should be deleted
    // condemned is sorted by the decreasing order of the ordinal number of each pod
    // deletion will start with the pod with the largest ordinal number
    let condemned = pods
        .filter(|pod| exists |ord: nat| ord >= replicas && pod.metadata.name->0 == pod_name(parent_name, ord))
        .sort_by(|p1, p2| get_ordinal(p1, parent_name) >= get_ordinal(p2, parent_name));
    (needed, condemned)
}

pub open spec fn make_owner_references(vsts: VStatefulSetView) -> Seq<OwnerReferenceView> {
    seq![vsts.controller_owner_ref()]
}

// make_pod models https://github.com/kubernetes/kubernetes/blob/release-1.30/pkg/controller/statefulset/stateful_set_utils.go#L523
pub open spec fn make_pod(vsts: VStatefulSetView, ordinal: nat) -> PodView {
    // Get pod from template
    let template = vsts.spec.template->0;
    let pod = PodView {
        metadata: {
            ObjectMetaView {
                name: Some(pod_name(vsts.metadata.name->0, ordinal)),
                labels: template.metadata->0.labels,
                annotations: template.metadata->0.annotations,
                finalizers: template.metadata->0.finalizers,
                owner_references: Some(make_owner_references(vsts)),
                ..ObjectMetaView::default()
            }
        },
        spec: vsts.spec.template->0.spec,
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
