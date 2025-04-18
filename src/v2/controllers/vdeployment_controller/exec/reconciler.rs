use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vreplicaset_controller::{trusted::exec_types::VReplicaSet};
use crate::vdeployment_controller::model::reconciler as model_reconciler;
use crate::vdeployment_controller::trusted::{exec_types::*, step::*};
use vstd::{prelude::*, map::*, hash_map::*};

verus! {

pub struct VDeploymentReconcileState {
    pub reconcile_step: VDeploymentReconcileStep,
    pub vrs_list: Vec<VReplicaSet>,
    pub pod_list: Vec<Pod>,
}

impl View for VDeploymentReconcileState {
    type V = model_reconciler::VDeploymentReconcileState;

    open spec fn view(&self) -> model_reconciler::VDeploymentReconcileState {
        model_reconciler::VDeploymentReconcileState {
            reconcile_step: self.reconcile_step@,
            vrs_list: self.vrs_list@,
            pod_list: self.pod_list@,
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
    requires vd@.well_formed(),
    ensures (res.0@, option_view(res.1) == model_reconciler::reconcile_core(vd@, option_view(resp_o), state@)),
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
            return (state_prime, Some(Request::KubeAPIRequest(req)));
        },
        VDeploymentReconcileStep::AfterGetReplicaSets => {
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
            let mut vrs_pod_map = HashMapWithView::<VReplicaSet, Vec<Pod>>::new();
            for idx in 0..filtered_vrs_list.len() {
                vrs_pod_map.insert(filtered_vrs_list[idx].clone(), Vec::new());
            }
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStep::AfterGetPods,
                vrs_pod_map: Some(vrs_pod_map),
                ..state
            };
            let req = KubeAPIRequest::ListRequest(KubeListRequest {
                api_resource: Pod::api_resource(),
                namespace: namespace,
            });
            return (state_prime, Some(Request::KubeAPIRequest(req)));
        },
        VDeploymentReconcileStep::AfterGetPods => {
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
            let (new_vrs, old_vrs) = filter_old_and_new_vrs(state.vrs_pod_map.keys().cloned().collect(), vd);
            if new_vrs.is_Some() {
                let diff = vd.spec.replicas - new_vrs.spec.replicas;
                if diff != 0 {
                    // scale up new vrs up to desired vrs
                    let state_prime = VDeploymentReconcileState {
                        reconcile_step: VDeploymentReconcileStep::ScaleReplicaSet(new_vrs.get_Some_0(), diff),
                        ..state
                    };
                    (state_prime, None)
                } else if old_vrs.len() > 0 {
                    // scale down old vrs down to 0 replicas
                    let state_prime = VDeploymentReconcileState {
                        reconcile_step: VDeploymentReconcileStep::ScaleReplicaSet(old_vrs[0], -old_vrs[0].spec.replicas),
                        ..state
                    };
                    (state_prime, None)
                } else {
                    // all good
                    let state_prime = VDeploymentReconcileState {
                        reconcile_step: VDeploymentReconcileStep::Done,
                        ..state
                    };
                    (state_prime, None)
                }
            }
        },
        VDeploymentReconcileStep::ScaleReplicaSet(rs, diff) => {
            if diff == 0 {

                let error_state = VDeploymentReconcileState {
                    reconcile_step: VDeploymentReconcileStep::Error,
                    ..state
                };
                (error_state, None)
            }
            let req = KubeAPIRequest::UpdateRequest(UpdateRequest {
                api_resource: VReplicaSet::api_resource(),
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
            let (new_vrs, old_vrs) = filter_old_and_new_vrs(state.vrs_pod_map.keys().cloned().collect(), vd);
            if new_vrs.is_Some() && new_vrs.spec.replicas != vd.spec.replicas {
                let state_prime = VDeploymentReconcileState {
                    reconcile_step: VDeploymentReconcileStep::ScaleReplicaSet(new_vrs.get_Some_0(), vd.spec.replicas - new_vrs.spec.replicas),
                    ..state
                };
            } else if old_vrs.len() > 0 {
                let state_prime = VDeploymentReconcileState {
                    reconcile_step: VDeploymentReconcileStep::ScaleReplicaSet(old_vrs[0], -old_vrs[0].spec.replicas),
                    ..state
                };
            } else {
                let state_prime = VDeploymentReconcileState {
                    reconcile_step: VDeploymentReconcileStep::Done,
                    ..state
                };
            }
            (state_prime, Some(Request::KubeAPIRequest(req)))
        },
    }
}

#[verifier(external_body)]
fn objects_to_vrs_list(objs: Vec<DynamicObject>) -> (vrs_list_or_none: Option<Vec<VReplicaSet>>)
    ensures
        vrs_list.is_Some() ==> vrs_list.get_Some_0()@.map_values(|vrs: VReplicaSet| vrs@) == model_reconciler::objects_to_vrs_list(objs@),
{
    let mut vrs_list: Vec<VReplicaSet> = Vec::new();
    for obj in objs.iter() {
        let vrs_or_error = VReplicaSet::unmarshal(obj.clone());
        if vrs_or_error.is_OK() {
            vrs_list.push(vrs_or_error.unwrap());
        }
        else {
            return None;
        }
    }
    Some(vrs_list)
}

// what's the correct way of encoding owner reference?
#[verifier(external_body)]
fn filter_vrs_list(vrs_list: Vec<VReplicaSet>, vd: &VDeployment) -> (filtered_vrs_list: Vec<VReplicaSet>)
    requires vd@.well_formed(),
    ensures filtered_vrs_list@ == model_reconciler::filter_vrs_list(vrs_list@.map_values(|vrs: VReplicaSet| vrs@), vd@),
{
    let mut filtered_vrs_list = Vec::new();
    for vrs in vrs_list.iter() {
        // double check
        if vrs.metadata().owner_references_contains(vd.controller_owner_ref()) 
        && !vrs.metadata().has_deletion_timestamp() {
            filtered_vrs_list.push(vrs.clone());
        }
    }
    filtered_vrs_list
}

fn filter_old_and_new_vrs(vrs_list: Vec<VReplicaSet>, vd: &VDeployment) -> (Option<VReplicaSet>, Vec<VReplicaSet>)
    requires vd@.well_formed(),
{
    let mut new_vrs = None;
    let mut old_vrs_list = Vec::new();
    let pod_template_hash = vd.metadata().resource_version().unwrap();
    let vrs_template_match = |vrs: VReplicaSet| {
        vrs.spec.template == PodTemplateSpecView{
            "phd-template-hash": pod_template_hash,
            ..vd.spec.template
        }
    };
    for vrs in vrs_list.iter() {
        if vrs_template_match(vrs) {
            new_vrs = Some(vrs);
        } else if vrs.spec.replicas > 0 {
            old_vrs_list.push(vrs);
        }
    }
    (new_vrs, old_vrs_list)
}

// TODO
// proof lemma_filter_old_and_new_vrs_match_model();

fn make_replica_set(vd: &VDeployment) -> (vrs: VReplicaSet) {
    let pod_template_hash = vd.metadata().resource_version().unwrap();
    let template = PodTemplateSpec{
        metadata: Some(ObjectMeta {
            labels: Some(
                "pod-template-hash": pod_template_hash,
                ..vd.spec().template().metadata().labels(),
            ),
            ..vd.spec().template().metadata()
        }),
        spec: Some(vd.spec().template().spec()),
        ..PodTemplateSpec::default()
    };
    let spec = VReplicaSetSpec {
        replicas: Some(vd.spec().replicas()),
        selector: LabelSelector {
            match_labels: Some(
                "pod-template-hash": pod_template_hash,
                ..vd.spec().selector().match_labels().unwrap(),
            ),
        }
        template: Some(template),
        ..VReplicaSetSpec::default()
    };
    let metadata = ObjectMeta {
        name: Some(vd.metadata().name() + '-' + pod_template_hash),
        namespace: vd.metadata().namespace(),
        owner_references: Some(make_owner_references(vd)),
        ..vd.metadata()
    };
    VReplicaSet {
        metadata: metadata,
        spec: spec,
        ..VReplicaSet::default()
    }
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