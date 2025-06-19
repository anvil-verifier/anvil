#![allow(unused_imports)]

use crate::kubernetes_api_objects::spec::{
    prelude::*,
    pod_template_spec::PodTemplateSpecView,
    label_selector::LabelSelectorView,
};
use crate::vstd_ext::string_view::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::{spec_types::*, step::*, util::*};
use vstd::prelude::*;

verus! {

pub struct VDeploymentReconciler {}

pub struct VDeploymentReconcileState {
    pub reconcile_step: VDeploymentReconcileStepView,
    pub new_vrs: Option<VReplicaSetView>,
    pub old_vrs_list: Seq<VReplicaSetView>,
}

impl Reconciler<VDeploymentReconcileState, VDeploymentView, VoidEReqView, VoidERespView> for VDeploymentReconciler {
    open spec fn reconcile_init_state() -> VDeploymentReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(vd: VDeploymentView, resp_o: Option<ResponseView<VoidERespView>>, state: VDeploymentReconcileState) -> (VDeploymentReconcileState, Option<RequestView<VoidEReqView>>) {
        reconcile_core(vd, resp_o, state)
    }

    open spec fn reconcile_done(state: VDeploymentReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: VDeploymentReconcileState) -> bool {
        reconcile_error(state)
    }
}

pub open spec fn reconcile_init_state() -> VDeploymentReconcileState {
    VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStepView::Init,
        new_vrs: None,
        old_vrs_list: Seq::empty(),
    }
}

pub open spec fn reconcile_done(state: VDeploymentReconcileState) -> bool {
    match state.reconcile_step {
        VDeploymentReconcileStepView::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: VDeploymentReconcileState) -> bool {
    match state.reconcile_step {
        VDeploymentReconcileStepView::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(vd: VDeploymentView, resp_o: Option<ResponseView<VoidERespView>>, state: VDeploymentReconcileState) -> (res: (VDeploymentReconcileState, Option<RequestView<VoidEReqView>>)) {
    let namespace = vd.metadata.namespace.unwrap();
    match &state.reconcile_step {
        VDeploymentReconcileStepView::Init => {
            let req = APIRequest::ListRequest(ListRequest {
                kind: VReplicaSetView::kind(),
                namespace: namespace,
            });
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStepView::AfterListVRS,
                new_vrs: None,
                old_vrs_list: Seq::<VReplicaSetView>::empty(),
            };
            (state_prime, Some(RequestView::KRequest(req)))
        },
        VDeploymentReconcileStepView::AfterListVRS => {
            if !(is_some_k_list_resp_view!(resp_o) && extract_some_k_list_resp_view!(resp_o).is_Ok()) {
                (error_state(state), None)
            } else {
                let objs = extract_some_k_list_resp_view!(resp_o).unwrap();
                let vrs_list_or_none = objects_to_vrs_list(objs);
                if vrs_list_or_none.is_None() {
                    (error_state(state), None)
                } else {
                    let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, filter_vrs_list(vrs_list_or_none.get_Some_0(), vd));
                    let state = VDeploymentReconcileState {
                        new_vrs: new_vrs,
                        old_vrs_list: old_vrs_list,
                        ..state
                    };
                    if new_vrs.is_None() {
                        // create the new vrs
                        create_new_vrs(state, vd)
                    } else {
                        if !match_replicas(new_vrs.get_Some_0(), vd) {
                            // scale new vrs to desired replicas
                            scale_new_vrs(state, vd)
                        } else {
                            if old_vrs_list.len() > 0 {
                                if !state.old_vrs_list.last().well_formed() {
                                    (error_state(state), None)
                                } else {
                                    // scale down old vrs to 0 replicas
                                    scale_down_old_vrs(state, vd)
                                }
                            } else {
                                // all good
                                (done_state(state), None)
                            }
                        }
                    }
                }
            }
        },
        VDeploymentReconcileStepView::AfterCreateNewVRS => {
            if !(is_some_k_create_resp_view!(resp_o) && extract_some_k_create_resp_view!(resp_o).is_Ok()) {
                (error_state(state), None)
            } else {
                if state.new_vrs.is_None() {
                    (error_state(state), None)
                } else {
                    let new_vrs = state.new_vrs.unwrap();
                    if !new_vrs.well_formed() {
                        (error_state(state), None)
                    } else {
                        if !match_replicas(new_vrs, vd) {
                            scale_new_vrs(state, vd)
                        } else {
                            if state.old_vrs_list.len() > 0 {
                                if !state.old_vrs_list.last().well_formed() {
                                    (error_state(state), None)
                                } else {
                                    scale_down_old_vrs(state, vd)
                                }
                            } else {
                                (done_state(state), None)
                            }
                        }
                    }
                }
            }
        },
        VDeploymentReconcileStepView::AfterScaleNewVRS => {
            if !(is_some_k_get_then_update_resp_view!(resp_o) && extract_some_k_get_then_update_resp_view!(resp_o).is_Ok()) {
                (error_state(state), None)
            } else {
                if state.old_vrs_list.len() > 0 {
                    if !state.old_vrs_list.last().well_formed() {
                        (error_state(state), None)
                    } else {
                        scale_down_old_vrs(state, vd)
                    }
                } else {
                    (done_state(state), None)
                }
            }
        },
        VDeploymentReconcileStepView::AfterScaleDownOldVRS => {
            if !(is_some_k_get_then_update_resp_view!(resp_o) && extract_some_k_get_then_update_resp_view!(resp_o).is_Ok()) {
                (error_state(state), None)
            } else {
                if state.old_vrs_list.len() > 0 {
                    if !state.old_vrs_list.last().well_formed() {
                        (error_state(state), None)
                    } else {
                        scale_down_old_vrs(state, vd)
                    }
                } else {
                    (done_state(state), None)
                }
            }
        },
        _ => {
            (state, None)
        }
    }
}

pub open spec fn error_state(state: VDeploymentReconcileState) -> (state_prime: VDeploymentReconcileState) {
    VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStepView::Error,
        ..state
    }
}

pub open spec fn done_state(state: VDeploymentReconcileState) -> (state_prime: VDeploymentReconcileState) {
    VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStepView::Done,
        ..state
    }
}

// wrapper functions to avoid duplication

// create new vrs
pub open spec fn create_new_vrs(state: VDeploymentReconcileState, vd: VDeploymentView) -> (res: (VDeploymentReconcileState, Option<RequestView<VoidEReqView>>)) {
    let new_vrs = make_replica_set(vd);
    let req = APIRequest::CreateRequest(CreateRequest {
        namespace: vd.metadata.namespace.unwrap(),
        obj: new_vrs.marshal(),
    });
    let state_prime = VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStepView::AfterCreateNewVRS,
        new_vrs: Some(new_vrs),
        ..state
    };
    (state_prime, Some(RequestView::KRequest(req)))
}

//  scale new vrs to desired replicas
pub open spec fn scale_new_vrs(state: VDeploymentReconcileState, vd: VDeploymentView) -> (res: (VDeploymentReconcileState, Option<RequestView<VoidEReqView>>)) {
    let new_vrs = state.new_vrs.unwrap();
    let new_vrs = VReplicaSetView {
        spec: VReplicaSetSpecView {
            replicas: Some(vd.spec.replicas.unwrap_or(1)),
            ..new_vrs.spec
        },
        ..new_vrs
    };
    let req = APIRequest::GetThenUpdateRequest(GetThenUpdateRequest {
        name: new_vrs.metadata.name.unwrap(),
        namespace: vd.metadata.namespace.unwrap(),
        owner_ref: vd.controller_owner_ref(),
        obj: new_vrs.marshal(),
    });
    let state_prime = VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStepView::AfterScaleNewVRS,
        new_vrs: Some(new_vrs),
        ..state
    };
    (state_prime, Some(RequestView::KRequest(req)))
}

// scale down old vrs to 0 replicas
pub open spec fn scale_down_old_vrs(state: VDeploymentReconcileState, vd: VDeploymentView) -> (res: (VDeploymentReconcileState, Option<RequestView<VoidEReqView>>)) {
    let old_vrs_list = state.old_vrs_list;
    let old_vrs = old_vrs_list.last();
    let req = APIRequest::GetThenUpdateRequest(GetThenUpdateRequest {
        name: old_vrs.metadata.name.unwrap(),
        namespace: vd.metadata.namespace.unwrap(),
        owner_ref: vd.controller_owner_ref(),
        obj: VReplicaSetView {
            spec: VReplicaSetSpecView {
                replicas: Some(0 as int),
                ..old_vrs.spec
            },
            ..old_vrs
        }.marshal(),
    });
    let state_prime = VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStepView::AfterScaleDownOldVRS,
        old_vrs_list: old_vrs_list.drop_last(),
        ..state
    };
    (state_prime, Some(RequestView::KRequest(req)))
}

pub open spec fn match_replicas(vrs: VReplicaSetView, vd: VDeploymentView) -> bool {
    vd.spec.replicas.unwrap_or(1) == vrs.spec.replicas.unwrap_or(1 as int)
}

// See https://github.com/kubernetes/kubernetes/blob/cdc807a9e849b651fb48c962cc18e25d39ec5edf/pkg/controller/deployment/sync.go#L196-L210
// pod template hash is used to prevent old and new vrs from owning the same pod
// here we use resource_version of vd as a hash
//
// TODO: now we scale up the new vrs' replicas at once,
// we may consider existing pods in old vrs later to satisfy maxSurge
pub open spec fn make_replica_set(vd: VDeploymentView) -> (vrs: VReplicaSetView)
{
    let pod_template_hash = int_to_string_view(vd.metadata.resource_version.unwrap());
    let match_labels = vd.spec.template.metadata.unwrap().labels.unwrap().insert("pod-template-hash"@, pod_template_hash);
    VReplicaSetView {
        metadata: ObjectMetaView {
            name: Some(vd.metadata.name.unwrap() + "-"@ + pod_template_hash),
            namespace: vd.metadata.namespace,
            labels: vd.metadata.labels,
            owner_references: Some(make_owner_references(vd)),
            ..ObjectMetaView::default()
        }.add_label("pod-template-hash"@, pod_template_hash),
        spec: VReplicaSetSpecView {
            replicas: vd.spec.replicas,
            selector: LabelSelectorView {
                match_labels: Some(match_labels),
            },
            template: Some(template_with_hash(vd, pod_template_hash))
        },
        ..VReplicaSetView::default()
    }
}

pub open spec fn template_with_hash(vd: VDeploymentView, hash: StringView) -> PodTemplateSpecView
{
    PodTemplateSpecView {
        metadata: Some(ObjectMetaView {
            labels: Some(vd.spec.template.metadata.unwrap().labels.unwrap().insert("pod-template-hash"@, hash)),
            ..ObjectMetaView::default()
        }),
        spec: Some(vd.spec.template.spec.unwrap()),
        ..PodTemplateSpecView::default()
    }
}

pub open spec fn make_owner_references(vd: VDeploymentView) -> Seq<OwnerReferenceView> {
    seq![vd.controller_owner_ref()]
}

}