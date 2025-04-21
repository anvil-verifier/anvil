#![allow(unused_imports)]

use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::exec::{
    prelude::*,
    pod_template_spec::PodTemplateSpec,
    label_selector::LabelSelector,
};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vreplicaset_controller::trusted::exec_types::*;
use crate::vdeployment_controller::model::reconciler as model_reconciler;
use crate::vdeployment_controller::trusted::{exec_types::*, step::*};
use crate::vstd_ext::option_lib::*;
use vstd::{prelude::*, seq_lib::*};

verus! {

pub struct VDeploymentReconcileState {
    pub reconcile_step: VDeploymentReconcileStep,
    pub vrs_list: Vec<VReplicaSet>,
}

impl View for VDeploymentReconcileState {
    type V = model_reconciler::VDeploymentReconcileState;

    open spec fn view(&self) -> model_reconciler::VDeploymentReconcileState {
        model_reconciler::VDeploymentReconcileState {
            reconcile_step: self.reconcile_step@,
            vrs_list: self.vrs_list@.map_values(|vrs: VReplicaSet| vrs@),
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
        vrs_list: Vec::new(),
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

pub fn reconcile_core(vd: &VDeployment, resp_o: Option<Response<VoidEResp>>, state: VDeploymentReconcileState) -> (res: (VDeploymentReconcileState, Option<Request<VoidEReq>>))
    requires vd@.well_formed(),
    ensures (res.0@, option_view(res.1)) == model_reconciler::reconcile_core(vd@, option_view(resp_o), state@),
{
    let namespace = vd.metadata().namespace().unwrap();
    match state.reconcile_step {
        VDeploymentReconcileStep::Init => {
            let req = KubeAPIRequest::ListRequest(KubeListRequest {
                api_resource: VReplicaSet::api_resource(),
                namespace: namespace,
            });
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStep::AfterGetReplicaSets,
                ..state
            };
            (state_prime, Some(Request::KRequest(req)))
        },
        VDeploymentReconcileStep::AfterGetReplicaSets => {
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().is_list_response()
            && resp_o.as_ref().unwrap().as_k_response_ref().as_list_response_ref().res.is_Ok()) {
                return (error_state(state), None);
            }
            let objs = resp_o.unwrap().into_k_response().into_list_response().res.unwrap();
            let vrs_list_or_none = objects_to_vrs_list(objs);
            if vrs_list_or_none.is_none() {
                return (error_state(state), None);
            }
            let vrs_list = filter_vrs_list(vrs_list_or_none.unwrap(), vd);
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStep::RollReplicas,
                vrs_list: vrs_list,
                ..state
            };
            (state_prime, None)
        },
        VDeploymentReconcileStep::RollReplicas => {
            // second, do we need to update new vrs?
            // TODO: support different policy (order of scaling of new and old vrs)
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStep::RollReplicas,
                ..state
            };
            let (new_vrs_or_none, old_vrs_list) = filter_old_and_new_vrs(state.vrs_list, vd);
            if new_vrs_or_none.is_none() {
                // create new vrs
                let new_vrs = make_replica_set(vd);
                let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                    api_resource: VReplicaSet::api_resource(),
                    namespace: namespace,
                    obj: new_vrs.marshal(),
                });
                (state_prime, Some(Request::KRequest(req)))
            }
            else if new_vrs_or_none.is_Some() && new_vrs_or_none.get_Some_0().spec().replicas().unwrap() != vd.spec().replicas().unwrap(    ) {
                let new_vrs = new_vrs_or_none.get_Some_0();
                let new_spec = new_vrs.spec();
                new_spec.set_replicas(vd.spec().replicas().unwrap());
                new_vrs.set_spec(new_spec);
                let req = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                    api_resource: VReplicaSet::api_resource(),
                    namespace: namespace,
                    name: new_vrs.metadata().name().unwrap(),
                    obj: new_vrs.marshal()
                });
                (state_prime, Some(Request::KRequest(req)))
            }
            else if old_vrs_list.len() > 0 {
                let old_vrs = old_vrs_list[0];
                let new_spec = old_vrs.spec();
                new_spec.set_replicas(0);
                old_vrs.set_spec(new_spec);
                let req = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                    api_resource: VReplicaSet::api_resource(),
                    namespace: namespace,
                    name: old_vrs.metadata().name().unwrap(),
                    obj: old_vrs.marshal()
                });
                (state_prime, Some(Request::KRequest(req)))
            }
            else {
                // all good
                let state_prime = VDeploymentReconcileState {
                    reconcile_step: VDeploymentReconcileStep::Done,
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

pub open spec fn error_state(state: VDeploymentReconcileState) -> (state_prime: VDeploymentReconcileState) {
    VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStep::Error,
        ..state
    }
}

#[verifier(external_body)]
fn objects_to_vrs_list(objs: Vec<DynamicObject>) -> (vrs_list_or_none: Option<Vec<VReplicaSet>>)
    ensures
    vrs_list_or_none.is_Some() ==> vrs_list_or_none.get_Some_0()@.map_values(|vrs: VReplicaSet| vrs@) == model_reconciler::objects_to_vrs_list(objs@.map_values(|obj: DynamicObject| obj@)).get_Some_0(),
{
    let mut vrs_list_or_none: Vec<VReplicaSet> = Vec::new();
    for obj in objs.into_iter() {
        let vrs_or_error = VReplicaSet::unmarshal(obj);
        if vrs_or_error.is_Ok() {
            vrs_list_or_none.push(vrs_or_error.unwrap());
        }
        else {
            return None;
        }
    }
    Some(vrs_list_or_none)
}

// what's the correct way of encoding owner reference?
#[verifier(external_body)]
fn filter_vrs_list(vrs_list: Vec<VReplicaSet>, vd: &VDeployment) -> (filtered_vrs_list: Vec<VReplicaSet>)
    requires vd@.well_formed(),
    ensures filtered_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == model_reconciler::filter_vrs_list(vrs_list@.map_values(|vrs: VReplicaSet| vrs@), vd@),
{
    let filtered_vrs_list = Vec::new();
    for vrs in vrs_list.into_iter() {
        // double check
        if vrs.metadata().owner_references_contains(vd.controller_owner_ref()) 
        && !vrs.metadata().has_deletion_timestamp() {
            filtered_vrs_list.push(vrs);
        }
    }
    filtered_vrs_list
}

fn filter_old_and_new_vrs(vrs_list: Vec<VReplicaSet>, vd: &VDeployment) -> (Option<VReplicaSet>, Vec<VReplicaSet>)
    requires vd@.well_formed(),
{
    let mut new_vrs = None;
    let old_vrs_list = Vec::new();
    let pod_template_hash = vd.metadata().resource_version().unwrap();
    // the trait `vstd::pervasive::ForLoopGhostIteratorNew` is not implemented for `std::vec::IntoIter<vreplicaset_controller::trusted::exec_types::VReplicaSet>`
    let idx = 0;
    while idx < vrs_list.len() {
        let vrs = vrs_list[idx];
        if vrs.spec().template().unwrap().eq(&template_with_hash(vd)) {
            new_vrs = Some(vrs);
        } else if vrs.spec().replicas().unwrap() > 0 {
            old_vrs_list.push(vrs);
        }
    }
    (new_vrs, old_vrs_list)
}

// TODO
// proof lemma_filter_old_and_new_vrs_match_model();

fn make_replica_set(vd: &VDeployment) -> (vrs: VReplicaSet) {
    let pod_template_hash = vd.metadata().resource_version().unwrap();
    let template = template_with_hash(vd);
    let labels = vd.spec().template().unwrap().metadata().unwrap().labels().unwrap();
    labels.insert("pod_template_hash".to_string(), pod_template_hash);
    let spec = VReplicaSetSpec::default();
    spec.set_replicas(vd.spec().replicas().unwrap());
    let label_selector = LabelSelector::default();
    label_selector.set_match_labels(labels);
    spec.set_selector(label_selector);
    let template = template_with_hash(vd);
    spec.set_template(template);
    let metadata = vd.metadata();
    metadata.set_name(vd.metadata().name().unwrap() + "-" + &pod_template_hash);
    metadata.set_namespace(vd.metadata().namespace().unwrap());
    metadata.set_owner_references(make_owner_references(vd));
    let vrs = VReplicaSet::default();
    vrs.set_metadata(metadata);
    vrs.set_spec(spec);
    vrs
}

pub fn template_with_hash(vd: &VDeployment) -> PodTemplateSpec {
    let pod_template_hash = vd.metadata().resource_version().unwrap();
    let labels = vd.spec().template().unwrap().metadata().unwrap().labels().unwrap();
    labels.insert("pod_template_hash".to_string(), pod_template_hash);
    let template_meta = ObjectMeta::default();
    template_meta.set_labels(labels);
    let pod_template_spec = PodTemplateSpec::default();
    pod_template_spec.set_metadata(template_meta);
    pod_template_spec.set_spec(vd.spec().template().unwrap().spec().unwrap());
    pod_template_spec
}

pub fn make_owner_references(vd: &VDeployment) -> (owner_references: Vec<OwnerReference>)
    requires vd@.well_formed(),
    ensures owner_references@.map_values(|or: OwnerReference| or@) ==  model_reconciler::make_owner_references(vd@),
{
    let mut owner_references = Vec::new();
    owner_references.push(vd.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
            model_reconciler::make_owner_references(vd@)
        );
    }
    owner_references
}

} // verus!