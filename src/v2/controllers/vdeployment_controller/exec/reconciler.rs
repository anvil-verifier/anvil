use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::model::reconciler as model_reconciler;
use crate::vdeployment_controller::trusted::{exec_types::*, step::*};
use vstd::prelude::*;

pub struct VDeploymentReconcileState {
    pub reconcile_step: VDeploymentReconcileStep,
    pub vvrs_list: Option<Vec<VReplicaSet>>,
    pub vrs_pod_map: Option<Map<VReplicaSet, Vec<Pod>>>,
}

impl Vire for VDeploymentReconcileState {
    type V = model_reconciler::VDeploymentReconcileState;

    open spec fn view(&self) -> model_reconciler::VDeploymentReconcileState {
        model_reconciler::VDeploymentReconcileState {
            reconcile_step: self.reconcile_step@,
            vvrs_list: match self.vvrs_list {
                Some(vvrs_list) => Some(vvrs_list@.map_values(|rs| rs@)),
                None => None,
            },
            vrs_pod_map: match self.vrs_pod_map {
                // ???
                Some(rpm) => Some(rpm@.dom().mk_map(|rs: VReplicaSet| rs@).values().mk_map()),
                None => None,
            },
        }
    }
}

pub struct VDeploymentReconciler {}

impl Reconciler for VDeploymentReconciler {
    type S = VDeploymentReconcileState;
    type K = VDeployment;
    type EReq = VoidEReq;
    type EResp = VoidEResp;
    type M = model_reconciler::VDeploymentReconciler;

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

pub fn reconcile_init_state() -> (state: VDeploymentReconcileState)
    ensures state@ == model_reconciler::reconcile_init_state(),
{
    VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStep::Init,
        filtered_pods: None,
    }
}

pub fn reconcile_done(state: &VDeploymentReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_done(state@),
{
    match state.reconcile_step {
        VDeploymentReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &VDeploymentReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_error(state@),
{
    match state.reconcile_step {
        VDeploymentReconcileStep::Error => true,
        _ => false,
    }
}

// ???
// 1. how to keep deployment's rollout history
// https://kubernetes.io/docs/concepts/workloads/controllers/deployment/#rolling-back-a-deployment
// 2. User manages deployments, dc updates pods by rollout or rollback. There should be a user-monkey step just like pod-monkey
// 2.5 How rollout and rollback works with rs

pub fn reconcile_core(vd: &VDeployment, resp_o: Option<Response<VoidEResp>>, state: VDeploymentReconcileState) -> (res: (VDeploymentReconcileState, Option<Request<VoidReq>>))
    require vd@.well_formed(),
    ensures (res.0@, option_view(res.1) == model_reconciler::reconcile_core(vd@, option_view(resp_o), state@)),
{
    let namespace = vd.metadata().namespace().unwrap();
    match state.reconcile_step {
        VDeploymentReconcileStep::Init => {
            let req = KubeAPIRequest::ListRequest(KubeListRequest {
                // VReplicaSet instead of ReplicaSet here ???
                api_resource: VReplicaSet::api_resource(),
                namespace: namespace,
            });
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStep::AfterGetReplicaSets,
                ..state
            };
            return (state_prime, Some(Request::KubeAPIRequest(req)));
        },
        VDeploymentReconcileStep::AfterGetReplicaSets => {
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_list_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_list_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            let objs = resp_o.unwrap().into_k_response().into_list_response().res.unwrap();
        },
        VDeploymentReconcileStep::AfterGetPodMap => {},
        VDeploymentReconcileStep::ScaleDeployment(rs, operation) => {},
    }
}

#[verifier(external_body)]
fn objects_to_vrs_list(objs: Vec<DynamicObject>) -> (vrs_list_or_none: Option<Vec<VReplicaSet>>)
    ensures
        vrs_list.is_Some() ==> vrs_list.get_Some_0()@.map_values(|vrs: VReplicaSet| vrs@) == model_reconciler::objects_to_vrs_list(objs@),
{
    let mut vrs_list: Vec<VReplicaSet> = Vec::new();
    let mut idx = 0;

    while idx < objs.len() {
        let vrs_or_error = VReplicaSet::unmarshal(objs[idx].clone());
        if vrs_or_error.is_OK() {
            vrs_list.push(vrs_or_error.unwrap());
        }
        else {
            return None;
        }
        idx = idx + 1;
    }
    Some(vrs_list)
}

// what's the correct way of encoding owner reference?
#[verifier(external_body)]
fn filter_vrs_list(vrs_list: Vec<VReplicaSet>, vd: &VDeployment) -> (filtered_vrs_list: Vec<VReplicaSet>)
    requires vd@.well_formed(),
    ensures option_vec_view(vrs_or_none) == model_reconciler::filter_vrs_list(objs@map_values(|vrs: VReplicaSet| vrs@), vd@),
{
    let mut filtered_vrs_list = Vec::new();
    let mut idx = 0;
    while idx < vrs_list.len() {
        let vrs = &vrs_list[idx];
        if vrs.metadata().owner_references_contains(vd.controller_owner_ref()) 
        && !vrs.metadata().has_deletion_timestamp() {
            filtered_vrs_list.push(vrs.clone());
        }
        idx = idx + 1;
    }
    filtered_vrs_list
}