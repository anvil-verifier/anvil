#![allow(unused_imports)]

use crate::kubernetes_api_objects::spec::{
    prelude::*,
    pod_template_spec::PodTemplateSpecView,
    label_selector::LabelSelectorView,
};
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::{spec_types::*, step::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct VDeploymentReconciler {}

pub struct VDeploymentReconcileState {
    pub reconcile_step: VDeploymentReconcileStepView,
    pub vrs_list: Seq<VReplicaSetView>,
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
        vrs_list: Seq::empty(),
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
                reconcile_step: VDeploymentReconcileStepView::AfterGetReplicaSets,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req)))
        },
        VDeploymentReconcileStepView::AfterGetReplicaSets => {
            if !(resp_o.is_Some() && resp_o.get_Some_0().is_KResponse()
            && resp_o.get_Some_0().get_KResponse_0().is_ListResponse()
            && resp_o.get_Some_0().get_KResponse_0().get_ListResponse_0().res.is_ok()) {
                (error_state(state), None)
            } else {
                let objs = resp_o.unwrap().get_KResponse_0().get_ListResponse_0().res.unwrap();
                let vrs_list_or_none = objects_to_vrs_list(objs);
                if vrs_list_or_none.is_none() { // error in unmarshalling
                    (error_state(state), None)
                } else {
                    let vrs_list = vrs_list_or_none.unwrap();
                    let state_prime = VDeploymentReconcileState {
                        reconcile_step: VDeploymentReconcileStepView::RollReplicas,
                        vrs_list: vrs_list,
                        ..state
                    };
                    (state_prime, None)
                }
            }
        },
        VDeploymentReconcileStepView::RollReplicas => {
            // TODO: support different policy (order of scaling of new and old vrs)
            //       and maxSurge and maxUnavailable
            let (new_vrs_list, old_vrs_list) = filter_old_and_new_vrs(filter_vrs_list(state.vrs_list, vd), vd);
            if new_vrs_list.len() == 0 {
                // create the new vrs
                let new_vrs = make_replica_set(vd);
                let req = APIRequest::CreateRequest(CreateRequest {
                    namespace: namespace,
                    obj: new_vrs.marshal(),
                });
                let state_prime = VDeploymentReconcileState {
                    reconcile_step: VDeploymentReconcileStepView::Done,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req)))
            } else {
                // update existing new vrs
                let new_vrs = new_vrs_list[0]; // k8s deterministically chooses the "oldest" vrs, we just use the first one
                let existing_replicas = if new_vrs.spec.replicas.is_None() {1} else {new_vrs.spec.replicas.unwrap()};
                let expected_replicas = if vd.spec.replicas.is_None() {1} else {vd.spec.replicas.unwrap()};
                if existing_replicas != expected_replicas {
                    let req = APIRequest::UpdateRequest(UpdateRequest {
                        name: new_vrs.metadata.name.unwrap(),
                        namespace: namespace,
                        obj: VReplicaSetView {
                            spec: VReplicaSetSpecView {
                                replicas: Some(expected_replicas),
                                ..new_vrs.spec
                            },
                            ..new_vrs
                        }.marshal(),
                    });
                    let state_prime = VDeploymentReconcileState {
                        reconcile_step: VDeploymentReconcileStepView::Done,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req)))
                } else if old_vrs_list.len() > 0 {
                    // scale down old vrs down to 0 replicas
                    let old_vrs = old_vrs_list[0];
                    let req = APIRequest::UpdateRequest(UpdateRequest {
                        name: old_vrs.metadata.name.unwrap(),
                        namespace: namespace,
                        obj: VReplicaSetView {
                            spec: VReplicaSetSpecView {
                                replicas: Some(0),
                                ..old_vrs.spec
                            },
                            ..old_vrs
                        }.marshal(),
                    });
                    let state_prime = VDeploymentReconcileState {
                        reconcile_step: VDeploymentReconcileStepView::Done,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req)))
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
        && vrs.metadata.deletion_timestamp.is_None()
        && vrs.well_formed())
}

pub open spec fn filter_old_and_new_vrs(vrs_list: Seq<VReplicaSetView>, vd: VDeploymentView) -> (res: (Seq<VReplicaSetView>, Seq<VReplicaSetView>))
// we don't consider there is more than one new vrs controlled by vd, check discussion/kubernetes-model/deployment_controller.md for details
{
    // even if we know vrs controlled by vd should have spec.template.metadata.is_Some() because we add the pot-template-hash label
    // we still need to check it here and pretend we don't know it

    let new_spec_filter = |vrs: VReplicaSetView|
        vrs.spec.template.unwrap() == template_with_hash(vd, int_to_string_view(vd.metadata.resource_version.unwrap()));
    let old_spec_filter = |vrs: VReplicaSetView|
        !new_spec_filter(vrs)
        && vrs.spec.replicas.is_None() || vrs.spec.replicas.unwrap() > 0;
    let new_vrs_list = vrs_list.filter(new_spec_filter);
    let old_vrs_list = vrs_list.filter(old_spec_filter);
    (new_vrs_list, old_vrs_list)
}

// see https://github.com/kubernetes/kubernetes/blob/cdc807a9e849b651fb48c962cc18e25d39ec5edf/pkg/controller/deployment/sync.go#L196-L210
// pod template hash is used to prevent old and new vrs from owning the same pod
// here we use resource_version of vd as a hash
//
// TODO: now we scale up the new vrs' replicas at once,
// we may consider existing pods in old vrs later to satisfy maxSurge
pub open spec fn make_replica_set(vd: VDeploymentView) -> (vrs: VReplicaSetView)
{
    let pod_template_hash = int_to_string_view(vd.metadata.resource_version.unwrap());
    let match_labels = vd.spec.template.unwrap().metadata.unwrap().labels.unwrap().insert("pod-template-hash"@, pod_template_hash);
    VReplicaSetView {
        metadata: ObjectMetaView {
            name: Some(vd.metadata.name.unwrap() + "-"@ + pod_template_hash),
            namespace: vd.metadata.namespace,
            labels: vd.metadata.labels,
            owner_references: Some(make_owner_references(vd)),
            ..ObjectMetaView::default()
        },
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
        metadata: Some(vd.spec.template.unwrap().metadata.unwrap().add_label("pod-template-hash"@, hash)),
        spec: Some(vd.spec.template.unwrap().spec.unwrap()),
        ..PodTemplateSpecView::default()
    }
}

pub open spec fn make_owner_references(vd: VDeploymentView) -> Seq<OwnerReferenceView> {
    seq![vd.controller_owner_ref()]
}

}