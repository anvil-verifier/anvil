use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vreplicaset_controller::trusted::spec_types::VReplicaSetView;
use crate::vdeployment_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;

verus! {

pub struct VDeploymentReconciler {}

pub struct VDeploymentReconcileState {
    pub reconcile_step: VDeploymentReconcileStepViewView,
    pub vrs_pod_map: Option<HashMapWithView<VReplicaSetView, Seq<PodView>>>,
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
        reconcile_step: VDeploymentReconcileStepViewView::Init,
        filtered_pods: None,
    }
}

pub open spec fn reconcile_done(state: VDeploymentReconcileState) -> bool {
    match state.reconcile_step {
        VDeploymentReconcileStepViewView::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: VDeploymentReconcileState) -> bool {
    match state.reconcile_step {
        VDeploymentReconcileStepViewView::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(vd: &VDeployment, resp_o: Option<Response<VoidEResp>>, state: VDeploymentReconcileState) -> (res: (VDeploymentReconcileState, Option<Request<VoidReq>>)) {
    let namespace = vd.metadata().namespace().unwrap();
    match state.reconcile_step {
        VDeploymentReconcileStepView::Init => {
            let req = KubeAPIRequest::ListRequest(KubeListRequest {
                // VReplicaSet instead of ReplicaSet here ???
                api_resource: VReplicaSet::api_resource(),
                namespace: namespace,
            });
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStepView::AfterGetReplicaSets,
                ..state
            };
            return (state_prime, Some(RequestView::KubeAPIRequest(req)));
        },
        VDeploymentReconcileStepView::AfterGetReplicaSets => {
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_list_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_list_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            let objs = resp_o.unwrap().into_k_response().into_list_response().res.unwrap();
            let vrs_list_or_none = objects_to_vrs_list(objs);
            if vrs_list_or_none.is_none() {
                return (error_state(state), None);
            }
            let vrs_list = vrs_list_or_none.unwrap();
            let filtered_vrs_list = filter_vrs_list(vrs_list, vd);
            let mut vrs_pod_map = Map<VReplicaSet, Vec<Pod>>::new();
            for idx in 0..filtered_vrs_list.len() {
                vrs_pod_map.insert(filtered_vrs_list[idx].clone(), Vec::new());
            }
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStepView::AfterGetPodMap,
                vrs_pod_map: Some(vrs_pod_map),
                ..state
            };
            let req = KubeAPIRequest::ListRequest(KubeListRequest {
                api_resource: Pod::api_resource(),
                namespace: namespace,
            });
            return (state_prime, Some(RequestView::KubeAPIRequest(req)));
        },
        VDeploymentReconcileStepView::AfterGetPodMap => {
            // first, group pods by vrs
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_list_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_list_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            let pods = objects_to_pods(resp_o.unwrap().into_k_response().into_list_response().res.unwrap());
            for (vrs, _) in state.vrs_pod_map.into_iter() {
                state.vrs_pod_map[vrs] = filter_pods(pods, vrs);
            }
            // second, do we need to update new vrs?
            // TODO: support different policy (order of scaling of new and old vrs)
            let new_vrs, old_vrs = filter_old_and_new_vrs(state.vrs_pod_map.keys().cloned().collect(), vd);
            if new_vrs.is_Some() {
                let diff = vd.spec.replicas - new_vrs.spec.replicas;
                if diff != 0 {
                    // scale up new vrs up to desired vrs
                    let state_prime = VDeploymentReconcileState {
                        reconcile_step: VDeploymentReconcileStepView::ScaleReplicaSet(new_vrs.get_Some_0(), diff),
                        ..state
                    };
                    (state_prime, None)
                } else if old_vrs.len() > 0 {
                    // scale down old vrs down to 0 replicas
                    let state_prime = VDeploymentReconcileState {
                        reconcile_step: VDeploymentReconcileStepView::ScaleReplicaSet(old_vrs[0], -old_vrs[0].spec.replicas),
                        ..state
                    };
                    (state_prime, None)
                } else {
                    // all good
                    let state_prime = VDeploymentReconcileState {
                        reconcile_step: VDeploymentReconcileStepView::Done,
                        ..state
                    };
                    (state_prime, None)
                }
            }
        },
        VDeploymentReconcileStepView::ScaleReplicaSet(rs, diff) => {
            if diff == 0 {

                let error_state = VDeploymentReconcileState {
                    reconcile_step: VDeploymentReconcileStepView::Error,
                    ..state
                };
                (error_state, None)
            }
            let req = KubeAPIRequest::UpdateRequest(UpdateRequest {
                namespace: namespace,
                name: rs.metadata.name,
                obj: VReplicaSet {
                    spec: VReplicaSetSpec {
                        replicas: Some(rs.spec.replicas + diff),
                        ..rs.spec
                    },
                    ..rs
                }
            });
            // figure out if there's other vrs to update
            let new vrs, old_vrs = filter_old_and_new_vrs(state.vrs_pod_map.keys().cloned().collect(), vd);
            if new_vrs.is_Some() && new_vrs.spec.replicas != vd.spec.replicas {
                let state_prime = VDeploymentReconcileState {
                    reconcile_step: VDeploymentReconcileStepView::ScaleReplicaSet(new_vrs.get_Some_0(), vd.spec.replicas - new_vrs.spec.replicas),
                    ..state
                };
            } else if old_vrs.len() > 0 {
                let state_prime = VDeploymentReconcileState {
                    reconcile_step: VDeploymentReconcileStepView::ScaleReplicaSet(old_vrs[0], -old_vrs[0].spec.replicas),
                    ..state
                };
            } else {
                let state_prime = VDeploymentReconcileState {
                    reconcile_step: VDeploymentReconcileStepView::Done,
                    ..state
                };
            }
            (state_prime, Some(RequestView::KubeAPIRequest(req)))
        },
    }
}
    
pub open spec fn error_state(state: VDeploymentReconcileState) -> (state_prime: VDeploymentReconcileState) {
    VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStepViewView::Error,
        ..state
    }
}

pub open spec fn objects_to_vrs_list(objs: Seq<DynamicObjectView>) -> (vrs_list_or_none: Option<Seq<VReplicaSetView>>) {
    if objs.filter(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err()).len() != 0 {
        None
    } else {
        Some(objs.map_values(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).unwrap()))
    }
}
pub open spec fn filter_vrs_list(vrs_list: Seq<VReplicaSetView>, vd: VDeploymentView) -> (filtered_vrs_list: Seq<VReplicaSetView>) {
    vrs_list.filter(|vrs: VReplicaSetView|
        vrs.metadata.owner_references_contains(vd.controller_owner_ref())
        && vrs.metadata.deletion_timestamp.is_None())
}

}