#![allow(unused_imports)]

use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::exec::{
    prelude::*,
    pod_template_spec::PodTemplateSpec,
    label_selector::LabelSelector,
};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vreplicaset_controller::trusted::{exec_types::*, spec_types::*};
use crate::vdeployment_controller::model::reconciler as model_reconciler;
use crate::vdeployment_controller::trusted::{exec_types::*, step::*};
use crate::vstd_ext::option_lib::*;
use vstd::{prelude::*, seq_lib::*};
use crate::vstd_ext::seq_lib::*;

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

#[verifier(external_body)]
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
            return (state_prime, Some(Request::KRequest(req)))
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
            let vrs_list = filter_vrs_list(vrs_list_or_none.unwrap(), vd);
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStep::RollReplicas,
                vrs_list: vrs_list,
                ..state
            };
            return (state_prime, None)
        },
        VDeploymentReconcileStep::RollReplicas => {
            // TODO: support different policy (order of scaling of new and old vrs)
            //       and maxSurge and maxUnavailable
            match filter_old_and_new_vrs(state.vrs_list.clone(), vd) {
                (None, _) => {
                    // create the new vrs
                    let new_vrs = make_replica_set(vd);
                    let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: VReplicaSet::api_resource(),
                        namespace: namespace,
                        obj: new_vrs.marshal(),
                    });
                    let state_prime = VDeploymentReconcileState {
                        reconcile_step: VDeploymentReconcileStep::RollReplicas,
                        ..state
                    };
                    return (state_prime, Some(Request::KRequest(req)))
                },
                (Some(mut new_vrs), old_vrs_list) => {
                    // update existing new vrs
                    // TODO: is it valid for replicas on both sides to be None?
                    if new_vrs.spec().replicas().unwrap() != vd.spec().replicas().unwrap() {
                        let mut new_spec = new_vrs.spec();
                        new_spec.set_replicas(vd.spec().replicas().unwrap());
                        new_vrs.set_spec(new_spec);
                        let req = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: VReplicaSet::api_resource(),
                            namespace: namespace,
                            name: new_vrs.metadata().name().unwrap(),
                            obj: new_vrs.marshal()
                        });
                        let state_prime = VDeploymentReconcileState {
                            reconcile_step: VDeploymentReconcileStep::RollReplicas,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req)))
                    }
                    else if old_vrs_list.len() > 0 {
                        // scale down old vrs to zero
                        let mut old_vrs = old_vrs_list[0].clone();
                        let mut new_spec = old_vrs.spec();
                        new_spec.set_replicas(0);
                        old_vrs.set_spec(new_spec);
                        let req = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
                            api_resource: VReplicaSet::api_resource(),
                            namespace: namespace,
                            // is it possible to have name as None?
                            name: old_vrs.metadata().name().unwrap(),
                            obj: old_vrs.marshal()

                        });
                        let state_prime = VDeploymentReconcileState {
                            reconcile_step: VDeploymentReconcileStep::RollReplicas,
                            ..state
                        };
                        return (state_prime, Some(Request::KRequest(req)))
                    }
                    else {
                        // all good
                        let state_prime = VDeploymentReconcileState {
                            reconcile_step: VDeploymentReconcileStep::Done,
                            ..state
                        };
                        return (state_prime, None)
                    }
                }
            }
        },
        _ => {
            return (state, None)
        }
    }
}

pub fn error_state(state: VDeploymentReconcileState) -> (state_prime: VDeploymentReconcileState)
    ensures state_prime@ == model_reconciler::error_state(state@),
{
    VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStep::Error,
        ..state
    }
}

fn objects_to_vrs_list(objs: Vec<DynamicObject>) -> (vrs_list_or_none: Option<Vec<VReplicaSet>>)
ensures
    option_vec_view(vrs_list_or_none) == model_reconciler::objects_to_vrs_list(objs@.map_values(|obj: DynamicObject| obj@)),
{
    let mut vrs_list: Vec<VReplicaSet> = Vec::new();
    let mut idx = 0;

    proof {
        let model_result = model_reconciler::objects_to_vrs_list(objs@.map_values(|obj: DynamicObject| obj@));
        if model_result.is_some() {
            assert_seqs_equal!(
                vrs_list@.map_values(|vrs: VReplicaSet| vrs@),
                model_result.unwrap().take(0)
            );
        }
    }

    while idx < objs.len()
    invariant
        idx <= objs.len(),
        ({
            let model_result = model_reconciler::objects_to_vrs_list(objs@.map_values(|obj: DynamicObject| obj@));
            &&& (model_result.is_some() ==>
                    vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == model_result.unwrap().take(idx as int))
            &&& forall|i: int| 0 <= i < idx ==> VReplicaSetView::unmarshal(#[trigger] objs@[i]@).is_ok()
        }),
    {
        match VReplicaSet::unmarshal(objs[idx].clone()) {
            Ok(vrs) => {
                vrs_list.push(vrs);
                proof {
                    // Show that the vrs Vec and the model_result are equal up to index idx + 1.
                    let model_result = model_reconciler::objects_to_vrs_list(objs@.map_values(|obj: DynamicObject| obj@));
                    if (model_result.is_some()) {
                        assert(model_result.unwrap().take((idx + 1) as int)
                            == model_result.unwrap().take(idx as int) + seq![model_result.unwrap()[idx as int]]);
                        assert_seqs_equal!(
                            vrs_list@.map_values(|vrs: VReplicaSet| vrs@),
                            model_result.unwrap().take((idx + 1) as int)
                        );
                    }
                }
            },
            Err(_) => {
                proof {
                    // Show that if a vrs was unable to be serialized, the model would return None.
                    let model_input = objs@.map_values(|obj: DynamicObject| obj@);
                    let model_result = model_reconciler::objects_to_vrs_list(model_input);
                    assert(
                        model_input
                            .filter(|obj: DynamicObjectView| VReplicaSetView::unmarshal(obj).is_err())
                            .contains(model_input[idx as int])
                    );
                    assert(model_result == None::<Seq<VReplicaSetView>>);
                }
                return None;
            }
        }
        idx += 1;
    }

    proof {
        let model_input = objs@.map_values(|obj: DynamicObject| obj@);
        let model_result = model_reconciler::objects_to_vrs_list(model_input);

        // Prove, by contradiction, that the model_result can't be None.
        let filter_result = model_input.filter(|obj: DynamicObjectView| VReplicaSetView::unmarshal(obj).is_err());
        assert(filter_result.len() == 0) by {
            if filter_result.len() != 0 {
                seq_filter_contains_implies_seq_contains(
                    model_input,
                    |obj: DynamicObjectView| VReplicaSetView::unmarshal(obj).is_err(),
                    filter_result[0]
                );
            }
        };
        assert(model_result.is_some());
        assert(model_result.unwrap().take(objs.len() as int) == model_result.unwrap());
    }

    Some(vrs_list)
}

// what's the correct way of encoding owner reference?
fn filter_vrs_list(vrs_list: Vec<VReplicaSet>, vd: &VDeployment) -> (filtered_vrs_list: Vec<VReplicaSet>)
requires
    vd@.well_formed(),
    forall |vrs: VReplicaSet| vrs_list@.map_values(|vrs: VReplicaSet| vrs@).contains(vrs@) ==> vrs@.well_formed(),
ensures filtered_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == model_reconciler::filter_vrs_list(vrs_list@.map_values(|vrs: VReplicaSet| vrs@), vd@),
{
    let mut filtered_vrs_list: Vec<VReplicaSet> = Vec::new();
    let mut idx = 0;
    while idx < vrs_list.len() {
        let vrs = &vrs_list[idx];
        if vrs.metadata().owner_references_contains(vd.controller_owner_ref()) 
        && !vrs.metadata().has_deletion_timestamp() {
            filtered_vrs_list.push(vrs.clone());
        }
        idx += 1;
    }
    filtered_vrs_list
}

fn filter_old_and_new_vrs(vrs_list: Vec<VReplicaSet>, vd: &VDeployment) -> (Option<VReplicaSet>, Vec<VReplicaSet>)
requires
    vd@.well_formed(),
    forall |vrs: VReplicaSet| vrs_list@.map_values(|vrs: VReplicaSet| vrs@).contains(vrs@) ==> vrs@.well_formed(),
// TODO: how to write postcondition here as named tuple is not supported
{
    let mut new_vrs = None;
    let mut old_vrs_list = Vec::new();
    let mut idx = 0;
    let pod_template_hash = vd.metadata().resource_version().unwrap();
    while idx < vrs_list.len() {
        let vrs = &vrs_list[idx];
        if vrs.spec().template().unwrap().eq(&template_with_hash(vd)) {
            new_vrs = Some(vrs.clone());
        } else if vrs.spec().replicas().is_none() || vrs.spec().replicas().unwrap() > 0 {
            old_vrs_list.push(vrs.clone());
        }
    }
    (new_vrs, old_vrs_list)
}

// TODO
// proof lemma_filter_old_and_new_vrs_match_model();
fn make_replica_set(vd: &VDeployment) -> (vrs: VReplicaSet)
    requires vd@.well_formed(),
    ensures vrs@ == model_reconciler::make_replica_set(vd@),
{
    let pod_template_hash = vd.metadata().resource_version().unwrap();
    let template = template_with_hash(vd);
    let mut labels = vd.spec().template().unwrap().metadata().unwrap().labels().unwrap();
    labels.insert("pod_template_hash".to_string(), pod_template_hash.clone());
    let mut spec = VReplicaSetSpec::default();
    spec.set_replicas(vd.spec().replicas().unwrap());
    let mut label_selector = LabelSelector::default();
    label_selector.set_match_labels(labels);
    spec.set_selector(label_selector);
    let template = template_with_hash(vd);
    spec.set_template(template);
    let mut metadata = vd.metadata();
    // concatenation of (String, String) not yet supported in Verus
    metadata.set_name(vd.metadata().name().unwrap().concat("-").concat(pod_template_hash.as_str()));
    metadata.set_namespace(vd.metadata().namespace().unwrap());
    metadata.set_owner_references(make_owner_references(vd));
    let mut vrs = VReplicaSet::default();
    vrs.set_metadata(metadata);
    vrs.set_spec(spec);
    vrs
}

pub fn template_with_hash(vd: &VDeployment) -> (pod_template_spec: PodTemplateSpec)
    requires vd@.well_formed(),
    ensures pod_template_spec@ == model_reconciler::template_with_hash(vd@),
{
    let pod_template_hash = vd.metadata().resource_version().unwrap();
    let mut labels = vd.spec().template().unwrap().metadata().unwrap().labels().unwrap();
    labels.insert("pod_template_hash".to_string(), pod_template_hash);
    let mut template_meta = ObjectMeta::default();
    template_meta.set_labels(labels);
    let mut pod_template_spec = PodTemplateSpec::default();
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
        assert(owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@) =~= model_reconciler::make_owner_references(vd@));
    }
    owner_references
}

} // verus!