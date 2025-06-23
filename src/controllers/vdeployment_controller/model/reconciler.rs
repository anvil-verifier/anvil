#![allow(unused_imports)]

use crate::kubernetes_api_objects::spec::{
    prelude::*,
    pod_template_spec::PodTemplateSpecView,
    label_selector::LabelSelectorView,
};
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
                    let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, filter_vrs_list(vd, vrs_list_or_none.get_Some_0()));
                    let state = VDeploymentReconcileState {
                        new_vrs: new_vrs,
                        old_vrs_list: old_vrs_list,
                        ..state
                    };
                    if new_vrs.is_None() {
                        // create the new vrs
                        create_new_vrs(state, vd)
                    } else {
                        if !match_replicas(vd, new_vrs.get_Some_0()) {
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
                        if !match_replicas(vd, new_vrs) {
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

}