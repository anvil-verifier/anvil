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
use crate::vstd_ext::{seq_lib::*, string_map::*, string_view::*};
use deps_hack::tracing::{error, info};

verus! {

pub struct VDeploymentReconcileState {
    pub reconcile_step: VDeploymentReconcileStep,
    pub new_vrs: Option<VReplicaSet>,
    pub old_vrs_list: Vec<VReplicaSet>,
}

impl View for VDeploymentReconcileState {
    type V = model_reconciler::VDeploymentReconcileState;

    open spec fn view(&self) -> model_reconciler::VDeploymentReconcileState {
        model_reconciler::VDeploymentReconcileState {
            reconcile_step: self.reconcile_step@,
            new_vrs: option_view(self.new_vrs),
            old_vrs_list: self.old_vrs_list@.map_values(|vrs: VReplicaSet| vrs@),
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
        new_vrs: None,
        old_vrs_list: Vec::new(),
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
// 2. User manages deployments, dc updates vrs_list by rollout or rollback. There should be a user-monkey step just like pod-monkey
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
            let old_vrs_list = Vec::<VReplicaSet>::new();
            // why this assertion is required
            assert(old_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == Seq::<VReplicaSetView>::empty());
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStep::AfterListVRS,
                new_vrs: None,
                old_vrs_list: old_vrs_list,
            };
            return (state_prime, Some(Request::KRequest(req)))
        },
        VDeploymentReconcileStep::AfterListVRS => {
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                && resp_o.as_ref().unwrap().as_k_response_ref().is_list_response()
                && resp_o.as_ref().unwrap().as_k_response_ref().as_list_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            let objs = extract_some_k_list_resp!(resp_o).unwrap();
            let vrs_list_or_none = objects_to_vrs_list(objs);
            if vrs_list_or_none.is_none() {
                return (error_state(state), None);
            }
            let (new_vrs_list, old_vrs_list) = filter_old_and_new_vrs(filter_vrs_list(vrs_list_or_none.clone().unwrap(), vd), vd);
            // no .last().cloned() in verus because "The verifier does not yet support the following Rust feature: overloaded deref"
            let state = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStep::Error,
                new_vrs: None,
                old_vrs_list: old_vrs_list.clone(),
            };
            if new_vrs_list.len() == 0 {
                // no new vrs, create one
                return create_new_vrs(state, vd);
            }
            // verus doesn't have .pop() equivalent, and .last().cloned() is not supported either
            let new_vrs = new_vrs_list[new_vrs_list.len() - 1].clone();
            let state = VDeploymentReconcileState {
                new_vrs: Some(new_vrs.clone()),
                ..state
            };
            if !match_replicas(&new_vrs, &vd) {
                // scale new vrs to desired replicas
                return scale_new_vrs(state, &vd);
            }
            if old_vrs_list.len() > 0 {
                if !state.old_vrs_list[state.old_vrs_list.len() - 1].well_formed() {
                    return (error_state(state), None);
                }
                // scale old vrs to zero
                return scale_down_old_vrs(state, &vd);
            }
            // all good
            return (done_state(state), None);
        },
        VDeploymentReconcileStep::AfterCreateNewVRS => {
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                && resp_o.as_ref().unwrap().as_k_response_ref().is_create_response()
                && resp_o.as_ref().unwrap().as_k_response_ref().as_create_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            if state.new_vrs.is_none() {
                return (error_state(state), None);
            }
            let new_vrs = state.new_vrs.clone().unwrap();
            if !new_vrs.well_formed() {
                return (error_state(state), None);
            }
            if !match_replicas(&new_vrs, &vd) {
                return scale_new_vrs(state, &vd);
            }
            if state.old_vrs_list.len() > 0 {
                if !state.old_vrs_list[state.old_vrs_list.len() - 1].well_formed() {
                    return (error_state(state), None);
                }
                return scale_down_old_vrs(state, &vd);
            } else {
                return (done_state(state), None)
            }
        }
        VDeploymentReconcileStep::AfterScaleNewVRS => {
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
                && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            if state.old_vrs_list.len() > 0 {
                if !state.old_vrs_list[state.old_vrs_list.len() - 1].well_formed() {
                    return (error_state(state), None);
                }
                return scale_down_old_vrs(state, &vd);
            } else {
                return (done_state(state), None)
            }
        },
        VDeploymentReconcileStep::AfterScaleDownOldVRS => {
            if !(resp_o.is_some() && resp_o.as_ref().unwrap().is_k_response()
                && resp_o.as_ref().unwrap().as_k_response_ref().is_update_response()
                && resp_o.as_ref().unwrap().as_k_response_ref().as_update_response_ref().res.is_ok()) {
                return (error_state(state), None);
            }
            if state.old_vrs_list.len() > 0 {
                if !state.old_vrs_list[state.old_vrs_list.len() - 1].well_formed() {
                    return (error_state(state), None);
                }
                return scale_down_old_vrs(state, &vd);
            } else {
                return (done_state(state), None)
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

pub fn done_state(state: VDeploymentReconcileState) -> (state_prime: VDeploymentReconcileState)
    ensures state_prime@ == model_reconciler::done_state(state@),
{
    VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStep::Done,
        ..state
    }
}

// wrapper functions to avoid duplication

// create new vrs
#[verifier(external_body)]
pub fn create_new_vrs(state: VDeploymentReconcileState, vd: &VDeployment) -> (res: (VDeploymentReconcileState, Option<Request<VoidEReq>>))
requires
    vd@.well_formed(),
    state.new_vrs@.is_None(),
ensures
    res.0@ == model_reconciler::create_new_vrs(state@, vd@).0,
    res.1@.is_Some() && model_reconciler::create_new_vrs(state@, vd@).1.is_Some(),
    option_view(res.1@) == model_reconciler::create_new_vrs(state@, vd@).1,
{
    let new_vrs = make_replica_set(vd);
    let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
        api_resource: VReplicaSet::api_resource(),
        namespace: vd.metadata().namespace().unwrap(),
        obj: new_vrs.clone().marshal(),
    });
    let state_prime = VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStep::AfterCreateNewVRS,
        new_vrs: Some(new_vrs),
        ..state
    };
    return (state_prime, Some(Request::KRequest(req)))
}

// scale new vrs to desired replicas
#[verifier(external_body)]
pub fn scale_new_vrs(state: VDeploymentReconcileState, vd: &VDeployment) -> (res: (VDeploymentReconcileState, Option<Request<VoidEReq>>))
requires
    state.new_vrs@.is_Some(),
    state.new_vrs.unwrap()@.well_formed(),
ensures
    res.0@ == model_reconciler::scale_new_vrs(state@, vd@).0,
    res.1@.is_Some() && model_reconciler::scale_new_vrs(state@, vd@).1.is_Some(),
    option_view(res.1@) == model_reconciler::scale_new_vrs(state@, vd@).1,
{
    let mut new_vrs = state.new_vrs.unwrap();
    let mut new_spec = new_vrs.spec();
    new_spec.set_replicas(vd.spec().replicas().unwrap_or(1));
    new_vrs.set_spec(new_spec);
    let req = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
        api_resource: VReplicaSet::api_resource(),
        namespace: vd.metadata().namespace().unwrap(),
        name: new_vrs.metadata().name().unwrap(),
        obj: new_vrs.clone().marshal()
    });
    let state_prime = VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStep::AfterScaleNewVRS,
        new_vrs: Some(new_vrs),
        ..state
    };
    return (state_prime, Some(Request::KRequest(req)))
}

// scale down old vrs to 0 replicas 
#[verifier(external_body)]
pub fn scale_down_old_vrs(state: VDeploymentReconcileState, vd: &VDeployment) -> (res: (VDeploymentReconcileState, Option<Request<VoidEReq>>))
requires
    vd@.well_formed(),
    state@.old_vrs_list.len() > 0,
ensures
    res.0@ == model_reconciler::scale_down_old_vrs(state@, vd@).0,
    res.1@.is_Some() && model_reconciler::scale_down_old_vrs(state@, vd@).1.is_Some(),
    option_view(res.1@) == model_reconciler::scale_down_old_vrs(state@, vd@).1,
{
    let mut old_vrs_list = state.old_vrs_list;
    let mut old_vrs = old_vrs_list[old_vrs_list.len() - 1].clone();
    old_vrs_list.pop();
    let mut new_spec = old_vrs.spec();
    new_spec.set_replicas(0);
    old_vrs.set_spec(new_spec);
    let req = KubeAPIRequest::UpdateRequest(KubeUpdateRequest {
        api_resource: VReplicaSet::api_resource(),
        namespace: vd.metadata().namespace().unwrap(),
        name: old_vrs.metadata().name().unwrap(),
        obj: old_vrs.clone().marshal()
    });
    let state_prime = VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStep::AfterScaleDownOldVRS,
        old_vrs_list: old_vrs_list,
        ..state
    };
    return (state_prime, Some(Request::KRequest(req)))
}

fn match_replicas(vrs: &VReplicaSet, vd: &VDeployment) -> (res: bool)
requires
    vd@.well_formed(),
    vrs@.well_formed(),
ensures res == model_reconciler::match_replicas(vrs@, vd@),
{
    vrs.spec().replicas().unwrap_or(1) == vd.spec().replicas().unwrap_or(1)
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

fn filter_vrs_list(vrs_list: Vec<VReplicaSet>, vd: &VDeployment) -> (filtered_vrs_list: Vec<VReplicaSet>)
requires
    vd@.well_formed(),
ensures
    filtered_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == model_reconciler::filter_vrs_list(vrs_list@.map_values(|vrs: VReplicaSet| vrs@), vd@),
    forall |i: int| 0 <= i < filtered_vrs_list.len() ==> #[trigger] filtered_vrs_list[i]@.well_formed(),
{
    let mut filtered_vrs_list: Vec<VReplicaSet> = Vec::new();
    let mut idx = 0;

    proof {
        assert(
            filtered_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) ==
            model_reconciler::filter_vrs_list(vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(0), vd@)
        );
    }

    while idx < vrs_list.len()
    invariant
        idx <= vrs_list.len(),
        filtered_vrs_list@.map_values(|vrs: VReplicaSet| vrs@)
            == model_reconciler::filter_vrs_list(vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx as int), vd@),
        forall |i: int| 0 <= i < filtered_vrs_list.len() ==> #[trigger] filtered_vrs_list[i]@.well_formed(),
    {
        let vrs = &vrs_list[idx];
        if vrs.metadata().owner_references_contains(vd.controller_owner_ref()) 
        && !vrs.metadata().has_deletion_timestamp()
        && vrs.well_formed() {
            filtered_vrs_list.push(vrs.clone());
        }

        proof {
            let spec_filter = |vrs: VReplicaSetView|
                vrs.metadata.owner_references_contains(vd@.controller_owner_ref())
                && vrs.metadata.deletion_timestamp.is_none()
                && vrs.well_formed();
            let pre_filtered_vrs_list = if spec_filter(vrs@) {
                filtered_vrs_list@.map_values(|vrs: VReplicaSet| vrs@).drop_last()
            } else {
                filtered_vrs_list@.map_values(|vrs: VReplicaSet| vrs@)
            };
            assert(pre_filtered_vrs_list == vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx as int).filter(spec_filter));
            push_filter_and_filter_push(vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx as int), spec_filter, vrs@);
            assert(vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx as int).push(vrs@)
                   == vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx + 1 as int));
            assert(spec_filter(vrs@) ==> filtered_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == pre_filtered_vrs_list.push(vrs@));
        }

        idx += 1;
    }
    assert(vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(vrs_list.len() as int));
    filtered_vrs_list
}

fn filter_old_and_new_vrs(vrs_list: Vec<VReplicaSet>, vd: &VDeployment) -> (res: (Vec<VReplicaSet>, Vec<VReplicaSet>))
requires
    vd@.well_formed(),
    // vrs.well_formed() is required because we need to update the old vrs -> old_vrs.metadata.well_formed()
    // and new/old vrs has replicas -> vrs.state_validation()
    forall |i: int| 0 <= i < vrs_list.len() ==> #[trigger] vrs_list[i]@.well_formed()
ensures
    res.0@.map_values(|vrs: VReplicaSet| vrs@) == model_reconciler::filter_old_and_new_vrs(vrs_list@.map_values(|vrs: VReplicaSet| vrs@), vd@).0,
    res.1@.map_values(|vrs: VReplicaSet| vrs@) == model_reconciler::filter_old_and_new_vrs(vrs_list@.map_values(|vrs: VReplicaSet| vrs@), vd@).1,
    forall |i: int| 0 <= i < res.0.len() ==> (#[trigger] res.0[i])@.well_formed(),
    forall |i: int| 0 <= i < res.1.len() ==> (#[trigger] res.1[i])@.well_formed(),
{
    let mut new_vrs_list = Vec::new();
    let mut old_vrs_list = Vec::new();
    let mut idx = 0;

    proof {
        assert(
            new_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) ==
            model_reconciler::filter_old_and_new_vrs(vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(0), vd@).0
        );
        assert(
            old_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) ==
            model_reconciler::filter_old_and_new_vrs(vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(0), vd@).1
        );
        assert(forall |i: int| 0 <= i < new_vrs_list.len() ==> (#[trigger] new_vrs_list[i])@.well_formed());
        assert(forall |i: int| 0 <= i < old_vrs_list.len() ==> (#[trigger] old_vrs_list[i])@.well_formed());
    }

    while idx < vrs_list.len()
    invariant
        vd@.well_formed(),
        // again here, we can't put idx in invariants as "not proven before loop starts"
        ({
            let vrs_list_view = vrs_list@.map_values(|vrs: VReplicaSet| vrs@);
            forall |i: int| 0 <= i < vrs_list.len() ==> #[trigger] vrs_list_view[i].well_formed()
        }),
        idx <= vrs_list.len(),
        new_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == model_reconciler::filter_old_and_new_vrs(vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx as int), vd@).0,
        old_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == model_reconciler::filter_old_and_new_vrs(vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx as int), vd@).1,
        forall |i: int| 0 <= i < new_vrs_list.len() ==> (#[trigger] new_vrs_list[i])@.well_formed(),
        forall |i: int| 0 <= i < old_vrs_list.len() ==> (#[trigger] old_vrs_list[i])@.well_formed(),
    {
        let vrs = &vrs_list[idx];
        assert(vrs@.well_formed());

        // when comparing template, we should remove the pod_template_hash label from vrs
        if match_template_without_hash(vd, vrs) {
            new_vrs_list.push(vrs.clone());
        } else if vrs.spec().replicas().is_none() || vrs.spec().replicas().unwrap() > 0 {
            old_vrs_list.push(vrs.clone());
        }

        proof { // so we have it again, any ways to avoid this?
            assert(vrs_list@.map_values(|vrs: VReplicaSet| vrs@)[idx as int].well_formed());
            let new_spec_filter = |vrs: VReplicaSetView|
                model_reconciler::match_template_without_hash(vd@, vrs);
            let old_spec_filter = |vrs: VReplicaSetView|
                !new_spec_filter(vrs)
                && (vrs.spec.replicas.is_None() || vrs.spec.replicas.unwrap() > 0);
            let pre_new_vrs_list = if new_spec_filter(vrs_list@.map_values(|vrs: VReplicaSet| vrs@)[idx as int]) {
                new_vrs_list@.map_values(|vrs: VReplicaSet| vrs@).drop_last()
            } else {
                new_vrs_list@.map_values(|vrs: VReplicaSet| vrs@)
            };
            let pre_old_vrs_list = if old_spec_filter(vrs_list@.map_values(|vrs: VReplicaSet| vrs@)[idx as int]) {
                old_vrs_list@.map_values(|vrs: VReplicaSet| vrs@).drop_last()
            } else {
                old_vrs_list@.map_values(|vrs: VReplicaSet| vrs@)
            };
            assert(pre_new_vrs_list == vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx as int).filter(new_spec_filter));
            assert(pre_old_vrs_list == vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx as int).filter(old_spec_filter));
            push_filter_and_filter_push(vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx as int), new_spec_filter, vrs_list@.map_values(|vrs: VReplicaSet| vrs@)[idx as int]);
            push_filter_and_filter_push(vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx as int), old_spec_filter, vrs_list@.map_values(|vrs: VReplicaSet| vrs@)[idx as int]);
            assert(vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx as int).push(vrs_list@.map_values(|vrs: VReplicaSet| vrs@)[idx as int])
                   == vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(idx + 1 as int));
            assert(new_spec_filter(vrs@) ==> new_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == pre_new_vrs_list.push(vrs@));
            assert(old_spec_filter(vrs@) ==> old_vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == pre_old_vrs_list.push(vrs@));
        }

        idx += 1;
    }
    assert(vrs_list@.map_values(|vrs: VReplicaSet| vrs@) == vrs_list@.map_values(|vrs: VReplicaSet| vrs@).take(vrs_list.len() as int));
    (new_vrs_list, old_vrs_list)
}

// TODO
// proof lemma_filter_old_and_new_vrs_match_model();
fn make_replica_set(vd: &VDeployment) -> (vrs: VReplicaSet)
requires
    vd@.well_formed(),
ensures
    vrs@ == model_reconciler::make_replica_set(vd@),
{
    let pod_template_hash = vd.metadata().resource_version().unwrap();
    let mut vrs = VReplicaSet::default();
    vrs.set_metadata({
        let mut metadata = ObjectMeta::default();
        // concatenation of (String, String) not yet supported in Verus
        metadata.set_name(vd.metadata().name().unwrap().concat("-").concat(pod_template_hash.as_str()));
        metadata.set_namespace(vd.metadata().namespace().unwrap());
        if vd.metadata().labels().is_some() {
            metadata.set_labels(vd.metadata().labels().unwrap().clone());
        }
        metadata.add_label("pod-template-hash".to_string(), pod_template_hash.clone());
        metadata.set_owner_references(make_owner_references(vd));
        metadata
    });
    let mut spec = VReplicaSetSpec::default();
    if vd.spec().replicas().is_some() {
        spec.set_replicas(vd.spec().replicas().unwrap());
    }
    let mut labels = vd.spec().template().unwrap().metadata().unwrap().labels().unwrap().clone();
    labels.insert("pod-template-hash".to_string(), pod_template_hash.clone());
    let mut label_selector = LabelSelector::default();
    label_selector.set_match_labels(labels);
    spec.set_selector(label_selector);
    let template = template_with_hash(vd, pod_template_hash.clone());
    spec.set_template(template);
    vrs.set_spec(spec);
    proof {
        assert(template@ == model_reconciler::template_with_hash(vd@, pod_template_hash@));
        let model_labels = model_reconciler::make_replica_set(vd@).spec.selector.match_labels.unwrap();
        assert(labels@ == model_labels) by {
            assert(labels@ == vd@.spec.template.unwrap().metadata.unwrap().labels.unwrap().insert("pod-template-hash"@, pod_template_hash@));
            assert(pod_template_hash@ == int_to_string_view(vd@.metadata.resource_version.unwrap()));
            assert(model_labels == labels@);
        }
        assert(vrs@.spec.selector.match_labels == model_reconciler::make_replica_set(vd@).spec.selector.match_labels);
    }
    vrs
}

pub fn template_with_hash(vd: &VDeployment, hash: String) -> (pod_template_spec: PodTemplateSpec)
requires
    vd@.well_formed(),
ensures
    pod_template_spec@ == #[trigger] model_reconciler::template_with_hash(vd@, hash@),
{
    let mut labels = vd.spec().template().unwrap().metadata().unwrap().labels().unwrap().clone();
    let mut template_meta = ObjectMeta::default();
    template_meta.set_labels(labels);
    template_meta.add_label("pod-template-hash".to_string(), hash);
    let mut pod_template_spec = PodTemplateSpec::default();
    pod_template_spec.set_metadata(template_meta);
    pod_template_spec.set_spec(vd.spec().template().unwrap().spec().unwrap().clone());
    assert(pod_template_spec@.metadata.unwrap().labels == model_reconciler::template_with_hash(vd@, hash@).metadata.unwrap().labels);
    pod_template_spec
}

pub fn match_template_without_hash(vd: &VDeployment, vrs: &VReplicaSet) -> (res: bool)
requires
    vd@.well_formed(),
    vrs@.well_formed(),
ensures res == model_reconciler::match_template_without_hash(vd@, vrs@),
{
    let mut vrs_template = vrs.spec().template().unwrap().clone();
    let mut labels = vrs_template.metadata().unwrap().labels().unwrap();
    labels.remove(&"pod-template-hash".to_string());
    let mut template_meta = vrs_template.metadata().unwrap().clone();
    template_meta.set_labels(labels);
    vrs_template.set_metadata(template_meta);
    vd.spec().template().unwrap().eq(&vrs_template)
}

pub fn make_owner_references(vd: &VDeployment) -> (owner_references: Vec<OwnerReference>)
requires
    vd@.well_formed(),
ensures
    owner_references@.map_values(|or: OwnerReference| or@) ==  model_reconciler::make_owner_references(vd@),
{
    let mut owner_references = Vec::new();
    owner_references.push(vd.controller_owner_ref());
    proof {
        assert(owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@) =~= model_reconciler::make_owner_references(vd@));
    }
    owner_references
}

} // verus!