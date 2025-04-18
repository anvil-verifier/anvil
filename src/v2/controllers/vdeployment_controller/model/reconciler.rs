use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vreplicaset_controller::trusted::{spec_types::VReplicaSetView};
use crate::vdeployment_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;

verus! {

pub struct VDeploymentReconciler {}

pub struct VDeploymentReconcileState {
    pub reconcile_step: VDeploymentReconcileStepView,
    pub vrs_list: Seq<VReplicaSetView>,
    pub pod_list: Seq<PodView>,
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
        filtered_pods: None,
    }
}

pub open spec fn reconcile_done(state: VDeploymentReconcileState) -> bool {
    match state.reconcile_step {
        VDeploymentReconcileStepView::Done => true,
        _ => false,filtered_vrs_list
    }
}

pub open spec fn reconcile_error(state: VDeploymentReconcileState) -> bool {
    match state.reconcile_step {
        VDeploymentReconcileStepView::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(vd: VDeploymentView, resp_o: Option<ResponseView<VoidERespView>>, state: VDeploymentReconcileState) -> (res: (VDeploymentReconcileState, Option<ResponseView<VoidERespView>>)) {
    let namespace = vd.metadata.namespace.unwrap();
    match state.reconcile_step {
        VDeploymentReconcileStepView::Init => {
            let req = APIRequest::ListRequest(KubeListRequest {
                kind: VReplicaSetView::kind(),
                namespace: namespace,
            });
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStepView::AfterGetReplicaSets,
                ..state
            };
            return (state_prime, Some(RequestView::KRequest(req)));
        },
        VDeploymentReconcileStepView::AfterGetReplicaSets => {
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_list_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_list_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            let objs = resp_o.unwrap().into_k_response().into_list_response().res.unwrap();
            let vrs_list_or_none = objects_to_vrs_list(objs);
            if vrs_list_or_none.is_none() { // error in unmarshalling
                return (error_state(state), None);
            }
            let vrs_list = filter_vrs_list(vrs_list_or_none.unwrap(), vd);
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStepView::AfterGetPods,
                vrs_list: vrs_list,
                ..state
            };
            let req = APIRequest::ListRequest(KubeListRequest {
                kind: PodView::kind(),
                namespace: namespace,
            });
            return (state_prime, Some(RequestView::KRequest(req)));
        },
        VDeploymentReconcileStepView::AfterGetPods => {
            // first, group pods by vrs
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_list_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_list_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            let pods_or_none = objects_to_pods(resp_o.unwrap().into_k_response().into_list_response().res.unwrap());
            if pods_or_none.is_none() { // error in unmarshalling
                return (error_state(state), None);
            }
            let pods = pods_or_none.unwrap();
            // second, do we need to update new vrs?
            // TODO: support different policy (order of scaling of new and old vrs)
            let (new_vrs, old_vrs) = filter_old_and_new_vrs(state.vrs_list, vd);
            if new_vrs.is_None() {
                // create the new vrs
                let new_vrs = make_replica_set(vd);
                let req = APIRequest::CreateRequest(KubeCreateRequest {
                    kind: VReplicaSetView::kind(),
                    namespace: namespace,
                    obj: vrs.marshal(),
                });
            }
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
            let req = APIRequest::UpdateRequest(UpdateRequest {
                kind: VReplicaSetView::kind(),
                name: rs.metadata.name,
                namespace: namespace,
                obj: VReplicaSet {
                    spec: VReplicaSetSpec {
                        replicas: Some(rs.spec.replicas + diff),
                        ..rs.spec
                    },
                    ..rs
                }
            });
            // figure out if there's other vrs to update
            let (new_vrs, old_vrs) = filter_old_and_new_vrs(state.vrs_list, vd);
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
            (state_prime, Some(RequestView::KRequest(req)))
        },
    }
}

pub open spec fn error_state(state: VDeploymentReconcileState) -> (state_prime: VDeploymentReconcileState) {
    VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStepView::Error,
        ..state
    }
}

pub open spec fn objects_to_vrs_list(objs: Seq<DynamicObjectView>) -> (vrs_list: Option<Seq<VReplicaSetView>>) {
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

pub open spec fn filter_old_and_new_vrs(vrs_list: Seq<VReplicaSetView>, vd: VDeploymentView) -> (Option<VReplicaSetView>, Seq<VReplicaSetView>)
// we don't consider there is more than one new vrs controlled by vd, check discussion/kubernetes-model/deployment_controller.md for details
    recommends vrs_list.filter(|vrs: VReplicaSetView| vrs.spec.replicas > 0).len() <= 1,
{
    let new_vrs = vrs_list.filter(|vrs: VReplicaSetView| vrs.spec.replicas > 0);
    let old_vrs = vrs_list.filter(|vrs: VReplicaSetView| vrs.spec.replicas == 0);
    if new_vrs.len() > 0 {
        (Some(new_vrs[0]), old_vrs)
    } else {
        (None, old_vrs)
    }
}

// see https://github.com/kubernetes/kubernetes/blob/cdc807a9e849b651fb48c962cc18e25d39ec5edf/pkg/controller/deployment/sync.go#L196-L210
// pod template hash is used to prevent old and new vrs from owning the same pod
// here we use resource_version of vd as a hash
//
// TODO: now we scale up the new vrs' replicas at once,
// we may consider existing pods in old vrs later to satisfy maxSurge
pub open spec fn make_replica_set(vd: VDeploymentView) -> (vrs: VReplicaSetView) {
    let pod_template_hash = vd.metadata.resource_version.unwrap().to_string();
    let template = PodTemplateSpecView {
        metadata: Some(ObjectMetaView {
            labels: Some(
                "pod-template-hash": pod_template_hash,
                ..vd.spec.template.metadata.labels,
            ),
            ..vd.spec.template.metadata,
        });
        spec: Some(vd.spec.template.spec),
        ..PodTemplateSpecView::default()
    };
    let spec = VReplicaSetSpecView {
        replicas: Some(vd.spec.replicas),
        selector: LabelSelectorView {
            match_labels: Some(
                "pod-template-hash": pod_template_hash,
                ..vd.spec.selector.match_labels.unwrap()
            ),
        }
        template: Some(template),
        ..VReplicaSetSpecView::default()
    };
    let metadata = ObjectMetaView {
        name: Some(vd.metadata.name.unwrap() + "-"@ + pod_template_hash),
        namespace: vd.metadata.namespace,
        owner_references: Some(make_owner_references(vd)),
        ..vd.metadata,
    };
    VReplicaSetView {
        metadata: metadata,
        spec: spec,
        ..VReplicaSetView::default()
    }
}

pub open spec fn make_owner_references(vd: VDeploymentView) -> Seq<OwnerReferenceView> {
    seq![vd.controller_owner_ref()]
}

}