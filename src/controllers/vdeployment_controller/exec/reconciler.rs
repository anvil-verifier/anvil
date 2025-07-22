#![allow(unused_imports)]

use crate::kubernetes_api_objects::exec::{
    label_selector::LabelSelector, pod_template_spec::PodTemplateSpec, prelude::*,
};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vdeployment_controller::model::reconciler as model_reconciler;
use crate::vdeployment_controller::trusted::util as model_util;
use crate::vdeployment_controller::trusted::{exec_types::*, step::*};
use crate::vreplicaset_controller::trusted::{exec_types::*, spec_types::*};
use crate::vstd_ext::option_lib::*;
use crate::vstd_ext::{seq_lib::*, string_map::*, string_view::*};
use deps_hack::tracing::{error, info};
use vstd::{prelude::*, seq_lib::*, set::*, map::*};
// for assert(objs.deep_view() == extract_some_k_list_resp_view!(resp_o.deep_view()).unwrap());
use crate::reconciler::spec::io::*;

verus! {

pub struct VDeploymentReconcileState {
    pub reconcile_step: VDeploymentReconcileStep,
    pub new_vrs: Option<VReplicaSet>,
    pub old_vrs_list: Vec<VReplicaSet>,
    pub old_vrs_index: usize,
}

impl View for VDeploymentReconcileState {
    type V = model_reconciler::VDeploymentReconcileState;

    open spec fn view(&self) -> model_reconciler::VDeploymentReconcileState {
        model_reconciler::VDeploymentReconcileState {
            reconcile_step: self.reconcile_step@,
            new_vrs: self.new_vrs.deep_view(),
            old_vrs_list: self.old_vrs_list.deep_view(),
            old_vrs_index: self.old_vrs_index@ as nat,
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
    let old_vrs_list = Vec::<VReplicaSet>::new();
    assert(old_vrs_list.deep_view() == model_reconciler::reconcile_init_state().old_vrs_list);
    VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStep::Init,
        new_vrs: None,
        old_vrs_list: old_vrs_list,
        old_vrs_index: 0,
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

// Features to be supported:
// 1. rolling is supported, recreate is not. It waits for all old pods to stop running before adding new vrs.
// 2. maxSurge and maxUnavailable are not supported.
// 3. clean up old vrs is not supported. It's defined by "d.Spec.RevisionHistoryLimit" to keep that many replicas,
//    which also requires the support for revisions inside annotations to sort old rs and status of vd (will not clean up if vd is paused, etc.)
// 4. rollback is not supported.
// *. When having multiple new vrs, k8s deterministically chooses the oldest one.
//    We may not need to support this if we can prove this doesn't happen for our controller.
 // mask this proof before there's a solution to flakiness
 // see https://github.com/verus-lang/verus/issues/1756
pub fn reconcile_core(vd: &VDeployment, resp_o: Option<Response<VoidEResp>>, state: VDeploymentReconcileState) -> (res: (VDeploymentReconcileState, Option<Request<VoidEReq>>))
    requires
        vd@.well_formed(),
    ensures
        res.0@ == model_reconciler::reconcile_core(vd@, resp_o.deep_view(), state@).0,
        res.1.deep_view() == model_reconciler::reconcile_core(vd@, resp_o.deep_view(), state@).1,
{
    let namespace = vd.metadata().namespace().unwrap();
    match state.reconcile_step {
        VDeploymentReconcileStep::Init => {
            let req = KubeAPIRequest::ListRequest(KubeListRequest {
                api_resource: VReplicaSet::api_resource(),
                namespace: namespace,
            });
            let old_vrs_list = Vec::<VReplicaSet>::new();
            assert(old_vrs_list.deep_view() == Seq::<VReplicaSetView>::empty());
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStep::AfterListVRS,
                new_vrs: None,
                old_vrs_list: old_vrs_list,
                old_vrs_index: 0,
            };
            return (state_prime, Some(Request::KRequest(req)))
        },
        VDeploymentReconcileStep::AfterListVRS => {
            if !(is_some_k_list_resp!(resp_o) && extract_some_k_list_resp_as_ref!(resp_o).is_ok()) {
                return (error_state(state), None);
            }
            let objs = extract_some_k_list_resp!(resp_o).unwrap();
            assert(objs.deep_view() == extract_some_k_list_resp_view!(resp_o.deep_view()).unwrap());
            let vrs_list_or_none = objects_to_vrs_list(objs);
            if vrs_list_or_none.is_none() {
                return (error_state(state), None);
            }
            let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, filter_vrs_list(vd, vrs_list_or_none.clone().unwrap()));
            // no .last().cloned() in verus because "The verifier does not yet support the following Rust feature: overloaded deref"
            let state_prime = VDeploymentReconcileState{
                reconcile_step: VDeploymentReconcileStep::AfterEnsureNewVRS,
                new_vrs: new_vrs.clone(),
                old_vrs_index: old_vrs_list.len(),
                old_vrs_list: old_vrs_list
            };
            if new_vrs.is_none() {
                // no new vrs, create one
                return create_new_vrs(&state_prime, vd);
            }
            if !match_replicas(&vd, &new_vrs.unwrap()) {
                // scale new vrs to desired replicas
                return scale_new_vrs(&state_prime, &vd);
            }
            return (state_prime, None);
        },
        VDeploymentReconcileStep::AfterCreateNewVRS => {
            if !(is_some_k_create_resp!(resp_o) && extract_some_k_create_resp_as_ref!(resp_o).is_ok()) {
                return (error_state(state), None);
            }
            let obj = extract_some_k_create_resp!(resp_o).unwrap();
            if VReplicaSet::unmarshal(obj).is_err() {
                return (error_state(state), None);
            }
            let new_vrs = VReplicaSet::unmarshal(obj).unwrap();
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStep::AfterEnsureNewVRS,
                new_vrs: Some(new_vrs),
                ..state
            };
            return (state_prime, None);
        }
        VDeploymentReconcileStep::AfterScaleNewVRS => {
            if !(is_some_k_get_then_update_resp!(resp_o) && extract_some_k_get_then_update_resp_as_ref!(resp_o).is_ok()) {
                return (error_state(state), None);
            }
            let state_prime = VDeploymentReconcileState {
                reconcile_step: VDeploymentReconcileStep::AfterEnsureNewVRS,
                ..state
            };
            return (state_prime, None);
        },
        VDeploymentReconcileStep::AfterEnsureNewVRS => {
            if state.old_vrs_index == 0 {
                return (done_state(state), None)
            }
            if state.old_vrs_index > state.old_vrs_list.len() {
                return (error_state(state), None);
            }
            if !valid_owned_object(&state.old_vrs_list[state.old_vrs_index - 1], vd) {
                return (error_state(state), None);
            }
            return scale_down_old_vrs(&state, &vd);
        },
        VDeploymentReconcileStep::AfterScaleDownOldVRS => {
            if !(is_some_k_get_then_update_resp!(resp_o) && extract_some_k_get_then_update_resp_as_ref!(resp_o).is_ok()) {
                return (error_state(state), None);
            }
            if state.old_vrs_index == 0 {
                return (done_state(state), None)
            }
            if state.old_vrs_index > state.old_vrs_list.len() {
                return (error_state(state), None);
            }
            if !valid_owned_object(&state.old_vrs_list[state.old_vrs_index - 1], vd) {
                return (error_state(state), None);
            }
            return scale_down_old_vrs(&state, &vd);
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
pub fn create_new_vrs(state: &VDeploymentReconcileState, vd: &VDeployment) -> (res: (VDeploymentReconcileState, Option<Request<VoidEReq>>))
requires
    vd@.well_formed(),
    state@.new_vrs is None,
ensures
    res.1@ is Some && model_reconciler::create_new_vrs(state@, vd@).1 is Some,
    (res.0@, res.1.deep_view()) == model_reconciler::create_new_vrs(state@, vd@),
{
    let new_vrs = make_replica_set(vd);
    let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
        api_resource: VReplicaSet::api_resource(),
        namespace: vd.metadata().namespace().unwrap(),
        obj: new_vrs.clone().marshal(),
    });
    let state_prime = VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStep::AfterCreateNewVRS,
        ..(*state)
    };
    return (state_prime, Some(Request::KRequest(req)))
}

// scale new vrs to desired replicas
pub fn scale_new_vrs(state: &VDeploymentReconcileState, vd: &VDeployment) -> (res: (VDeploymentReconcileState, Option<Request<VoidEReq>>))
requires
    vd@.well_formed(),
    state@.new_vrs is Some,
    model_util::valid_owned_object(state@.new_vrs->0, vd@),
ensures
    res.1@ is Some && model_reconciler::scale_new_vrs(state@, vd@).1 is Some,
    (res.0@, res.1.deep_view()) == model_reconciler::scale_new_vrs(state@, vd@),
{
    let mut new_vrs = state.new_vrs.clone().unwrap();
    let mut new_spec = new_vrs.spec();
    new_spec.set_replicas(vd.spec().replicas().unwrap_or(1));
    new_vrs.set_spec(new_spec);
    let req = KubeAPIRequest::GetThenUpdateRequest(KubeGetThenUpdateRequest {
        api_resource: VReplicaSet::api_resource(),
        namespace: vd.metadata().namespace().unwrap(),
        name: new_vrs.metadata().name().unwrap(),
        owner_ref: vd.controller_owner_ref(),
        obj: new_vrs.clone().marshal()
    });
    let state_prime = VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStep::AfterScaleNewVRS,
        new_vrs: Some(new_vrs),
        old_vrs_list: state.old_vrs_list.clone(),
        old_vrs_index: state.old_vrs_index
    };
    return (state_prime, Some(Request::KRequest(req)))
}

// scale down old vrs to 0 replicas
pub fn scale_down_old_vrs(state: &VDeploymentReconcileState, vd: &VDeployment) -> (res: (VDeploymentReconcileState, Option<Request<VoidEReq>>))
requires
    vd@.well_formed(),
    0 < state.old_vrs_index <= state.old_vrs_list@.len(),
    model_util::valid_owned_object(state.old_vrs_list[state.old_vrs_index - 1]@, vd@),
ensures
    (res.0@, res.1.deep_view()) == model_reconciler::scale_down_old_vrs(state@, vd@),
{
    let old_vrs_index = state.old_vrs_index - 1;
    let mut old_vrs = state.old_vrs_list[old_vrs_index].clone();
    let mut new_spec = old_vrs.spec();
    new_spec.set_replicas(0);
    old_vrs.set_spec(new_spec);
    let req = KubeAPIRequest::GetThenUpdateRequest(KubeGetThenUpdateRequest {
        api_resource: VReplicaSet::api_resource(),
        namespace: vd.metadata().namespace().unwrap(),
        name: old_vrs.metadata().name().unwrap(),
        owner_ref: vd.controller_owner_ref(),
        obj: old_vrs.clone().marshal()
    });
    let state_prime = VDeploymentReconcileState {
        reconcile_step: VDeploymentReconcileStep::AfterScaleDownOldVRS,
        old_vrs_index: old_vrs_index,
        old_vrs_list: state.old_vrs_list.clone(),
        new_vrs: state.new_vrs.clone()
    };
    return (state_prime, Some(Request::KRequest(req)))
}

fn match_replicas(vd: &VDeployment, vrs: &VReplicaSet) -> (res: bool)
requires
    vd@.well_formed(),
    model_util::valid_owned_object(vrs@, vd@),
ensures res == model_util::match_replicas(vd@, vrs@),
{
    vrs.spec().replicas().unwrap_or(1) == vd.spec().replicas().unwrap_or(1)
}

fn objects_to_vrs_list(objs: Vec<DynamicObject>) -> (vrs_list_or_none: Option<Vec<VReplicaSet>>)
ensures
    vrs_list_or_none@.deep_view() == model_util::objects_to_vrs_list(objs.deep_view()),
{
    let mut vrs_list: Vec<VReplicaSet> = Vec::new();
    let mut idx = 0;

    proof {
        let model_result = model_util::objects_to_vrs_list(objs.deep_view());
        if model_result.is_some() {
            assert_seqs_equal!(
                vrs_list.deep_view(),
                model_result.unwrap().take(0)
            );
        }
    }

    for idx in 0..objs.len()
    invariant
        idx <= objs.len(),
        ({
            let model_result = model_util::objects_to_vrs_list(objs.deep_view());
            &&& (model_result.is_some() ==>
                vrs_list.deep_view() == model_result.unwrap().take(idx as int))
            &&& forall|i: int| 0 <= i < idx ==> VReplicaSetView::unmarshal(#[trigger] objs@[i]@).is_ok()
        }),
    {
        match VReplicaSet::unmarshal(objs[idx].clone()) {
            Ok(vrs) => {
                vrs_list.push(vrs);
                proof {
                    // Show that the vrs Vec and the model_result are equal up to index idx + 1.
                    let model_result = model_util::objects_to_vrs_list(objs.deep_view());
                    if (model_result.is_some()) {
                        assert(model_result.unwrap().take((idx + 1) as int)
                            == model_result.unwrap().take(idx as int) + seq![model_result.unwrap()[idx as int]]);
                        assert_seqs_equal!(
                            vrs_list.deep_view(),
                            model_result.unwrap().take((idx + 1) as int)
                        );
                    }
                }
            },
            Err(_) => {
                proof {
                    // Show that if a vrs was unable to be serialized, the model would return None.
                    let model_input = objs.deep_view();
                    let model_result = model_util::objects_to_vrs_list(model_input);
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
    }

    proof {
        let model_input = objs.deep_view();
        let model_result = model_util::objects_to_vrs_list(model_input);

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

fn valid_owned_object(vrs: &VReplicaSet, vd: &VDeployment) -> (res: bool)
requires
    vd@.well_formed(),
ensures
    res == model_util::valid_owned_object(vrs@, vd@),
{
    vrs.metadata().name().is_some()
    && !vrs.metadata().has_deletion_timestamp()
    && vrs.metadata().namespace_eq(&vd.metadata())
    && vrs.metadata().owner_references_contains(&vd.controller_owner_ref())
    && vrs.state_validation()
}

fn filter_vrs_list(vd: &VDeployment, vrs_list: Vec<VReplicaSet>) -> (filtered_vrs_list: Vec<VReplicaSet>)
requires
    vd@.well_formed(),
ensures
    filtered_vrs_list.deep_view() == vrs_list.deep_view().filter(|vrs: VReplicaSetView| model_util::valid_owned_object(vrs, vd@)),
    forall |i: int| 0 <= i < filtered_vrs_list.len() ==> #[trigger] model_util::valid_owned_object(filtered_vrs_list[i]@, vd@),
{
    let mut filtered_vrs_list: Vec<VReplicaSet> = Vec::new();
    let mut idx = 0;

    proof {
        assert(filtered_vrs_list.deep_view() == vrs_list.deep_view().take(0).filter(|vrs: VReplicaSetView| model_util::valid_owned_object(vrs, vd@)));
    }

    for idx in 0..vrs_list.len()
    invariant
        vd@.well_formed(),
        idx <= vrs_list.len(),
        filtered_vrs_list.deep_view() == vrs_list.deep_view().take(idx as int).filter(|vrs: VReplicaSetView| model_util::valid_owned_object(vrs, vd@)),
        forall |i: int| 0 <= i < filtered_vrs_list.len() ==> #[trigger] model_util::valid_owned_object(filtered_vrs_list[i]@, vd@),
    {
        let vrs = &vrs_list[idx];
        if valid_owned_object(vrs, vd) {
            filtered_vrs_list.push(vrs.clone());
        }

        proof {
            let filter = |vrs: VReplicaSetView| model_util::valid_owned_object(vrs, vd@);
            let pre_filtered_vrs_list = if filter(vrs@) {
                filtered_vrs_list.deep_view().drop_last()
            } else {
                filtered_vrs_list.deep_view()
            };
            assert(pre_filtered_vrs_list == vrs_list.deep_view().take(idx as int).filter(filter));
            push_filter_and_filter_push(vrs_list.deep_view().take(idx as int), filter, vrs@);
            assert(vrs_list.deep_view().take(idx as int).push(vrs@)
                   == vrs_list.deep_view().take(idx + 1 as int));
            assert(filter(vrs@) ==> filtered_vrs_list.deep_view() == pre_filtered_vrs_list.push(vrs@));
        }
    }
    assert(vrs_list.deep_view() == vrs_list.deep_view().take(vrs_list.len() as int));
    filtered_vrs_list
}

fn filter_old_and_new_vrs(vd: &VDeployment, vrs_list: Vec<VReplicaSet>) -> (res: (Option<VReplicaSet>, Vec<VReplicaSet>))
requires
    vd@.well_formed(),
    // vrs.well_formed() is required because we need to update the old vrs -> old_vrs.metadata.well_formed_for_namespaced()
    // and new/old vrs has replicas -> vrs.state_validation()
    forall |i: int| 0 <= i < vrs_list.len() ==> #[trigger] model_util::valid_owned_object(vrs_list[i]@, vd@)
ensures
    (res.0.deep_view(), res.1.deep_view()) == model_util::filter_old_and_new_vrs(vd@, vrs_list.deep_view()),
    res.0.is_some() ==> model_util::valid_owned_object(res.0.unwrap()@, vd@),
    forall |i: int| 0 <= i < res.1.len() ==> #[trigger] model_util::valid_owned_object(res.1[i]@, vd@),
{
    let mut new_vrs_list = Vec::<VReplicaSet>::new();
    let mut old_vrs_list = Vec::<VReplicaSet>::new();
    let mut idx = 0;
    assert(new_vrs_list.deep_view() == vrs_list.deep_view().take(0).filter(|vrs: VReplicaSetView| model_util::match_template_without_hash(vd@, vrs)));
    for idx in 0..vrs_list.len()
    invariant
        new_vrs_list.deep_view() == vrs_list.deep_view().take(idx as int).filter(|vrs: VReplicaSetView| model_util::match_template_without_hash(vd@, vrs)),
        forall |i: int| 0 <= i < new_vrs_list.len() ==> #[trigger] model_util::valid_owned_object(new_vrs_list[i]@, vd@),
        forall |i: int| 0 <= i < vrs_list.len() ==> #[trigger] model_util::valid_owned_object(vrs_list[i]@, vd@),
        vd@.well_formed(),
        idx <= vrs_list.len(),
    {
        assert(model_util::valid_owned_object(vrs_list[idx as int]@, vd@));
        if match_template_without_hash(vd, &vrs_list[idx]) {
            new_vrs_list.push(vrs_list[idx].clone());
        }
        proof {
            let spec_filter = |vrs: VReplicaSetView| model_util::match_template_without_hash(vd@, vrs);
            let pre_filtered_vrs_list = if spec_filter(vrs_list[idx as int]@) {
                new_vrs_list.deep_view().drop_last()
            } else {
                new_vrs_list.deep_view()
            };
            assert(pre_filtered_vrs_list == vrs_list.deep_view().take(idx as int).filter(spec_filter));
            push_filter_and_filter_push(vrs_list.deep_view().take(idx as int), spec_filter, vrs_list[idx as int]@);
            assert(vrs_list.deep_view().take(idx as int).push(vrs_list[idx as int]@)
                   == vrs_list.deep_view().take(idx + 1 as int));
            assert(spec_filter(vrs_list[idx as int]@ ) ==> new_vrs_list.deep_view() == pre_filtered_vrs_list.push(vrs_list[idx as int]@));
        }
    }
    assert(new_vrs_list.deep_view() == vrs_list.deep_view().filter(|vrs: VReplicaSetView| model_util::match_template_without_hash(vd@, vrs))) by {
        // this is stupid
        assert(vrs_list.deep_view().take(vrs_list.len() as int) == vrs_list.deep_view());
    }
    let new_vrs = if new_vrs_list.len() == 0 {
        None
    } else {
        assert(model_util::valid_owned_object(new_vrs_list[0]@, vd@));
        Some(new_vrs_list[0].clone())
    };
    assert(new_vrs.deep_view() == model_util::filter_old_and_new_vrs(vd@, vrs_list.deep_view()).0);
    assert(old_vrs_list.deep_view() == vrs_list.deep_view().take(idx as int).filter(|vrs: VReplicaSetView| {
                &&& (new_vrs.is_none() || vrs.metadata.uid != new_vrs.deep_view().unwrap().metadata.uid)
                &&& (vrs.spec.replicas.is_none() || vrs.spec.replicas.unwrap() > 0)
            }));
    for idx in 0..vrs_list.len()
    invariant
        old_vrs_list.deep_view() == vrs_list.deep_view()
            .take(idx as int).filter(|vrs: VReplicaSetView| {
                &&& (new_vrs.is_none() || vrs.metadata.uid != new_vrs.deep_view().unwrap().metadata.uid)
                &&& (vrs.spec.replicas.is_none() || vrs.spec.replicas.unwrap() > 0)
            }),
        forall |i: int| 0 <= i < old_vrs_list.len() ==> #[trigger] model_util::valid_owned_object(old_vrs_list[i]@, vd@),
        forall |i: int| 0 <= i < vrs_list.len() ==> #[trigger] model_util::valid_owned_object(vrs_list[i]@, vd@),
        vd@.well_formed(),
        idx <= vrs_list.len(),
    {
        assert(model_util::valid_owned_object(vrs_list[idx as int]@, vd@));
        let vrs = &vrs_list[idx];
        if (new_vrs.is_none() || !vrs.metadata().uid_eq(&new_vrs.as_ref().unwrap().metadata()))
            && (vrs.spec().replicas().is_none() || vrs.spec().replicas().unwrap() > 0) {
            old_vrs_list.push(vrs.clone());
        }
        proof {
            let spec_filter = |vrs: VReplicaSetView| {
                &&& (new_vrs.is_none() || vrs.metadata.uid != new_vrs.deep_view().unwrap().metadata.uid)
                &&& (vrs.spec.replicas.is_none() || vrs.spec.replicas.unwrap() > 0)
            };
            let pre_filtered_vrs_list = if spec_filter(vrs@) {
                old_vrs_list.deep_view().drop_last()
            } else {
                old_vrs_list.deep_view()
            };
            assert(pre_filtered_vrs_list == vrs_list.deep_view().take(idx as int).filter(spec_filter));
            push_filter_and_filter_push(vrs_list.deep_view().take(idx as int), spec_filter, vrs@);
            assert(vrs_list.deep_view().take(idx as int).push(vrs@)
                   == vrs_list.deep_view().take(idx + 1 as int));
            assert(spec_filter(vrs@) ==> old_vrs_list.deep_view() == pre_filtered_vrs_list.push(vrs@));
        }
    }
    assert(old_vrs_list.deep_view() == model_util::filter_old_and_new_vrs(vd@, vrs_list.deep_view()).1);
    return (new_vrs, old_vrs_list);
}

// TODO
// proof lemma_model_util::filter_old_and_new_vrs_match_model();
fn make_replica_set(vd: &VDeployment) -> (vrs: VReplicaSet)
requires
    vd@.well_formed(),
ensures
    vrs@ == model_reconciler::make_replica_set(vd@),
    model_util::valid_owned_object(vrs@, vd@),
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
    let mut labels = vd.spec().template().metadata().unwrap().labels().unwrap().clone();
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
            assert(labels@ == vd@.spec.template.metadata.unwrap().labels.unwrap().insert("pod-template-hash"@, pod_template_hash@));
            assert(pod_template_hash@ == int_to_string_view(vd@.metadata.resource_version.unwrap()));
            assert(model_labels == labels@);
        }
        assert(labels@.len() > 0) by {
            assert(labels@.dom().contains("pod-template-hash"@));
            let old_labels = vd@.spec.template.metadata.unwrap().labels.unwrap();
            assert(old_labels.dom().len() >= 0);
            assert(labels@ == old_labels.insert("pod-template-hash"@, pod_template_hash@));
            axiom_map_insert_domain(old_labels, "pod-template-hash"@, pod_template_hash@);
            assert(labels@.dom() == old_labels.dom().insert("pod-template-hash"@));
            axiom_set_insert_len(old_labels.dom(), "pod-template-hash"@);
        }
        assert(vrs@.spec.selector.match_labels->0 == labels@);
        assert(vrs@.spec.selector.match_labels->0.len() > 0);
        assert(vrs@.spec.selector.match_labels == model_reconciler::make_replica_set(vd@).spec.selector.match_labels);
        assert(vrs@.metadata.owner_references.unwrap() == model_reconciler::make_owner_references(vd@));
        assert(vrs@.metadata.owner_references_contains(vd@.controller_owner_ref())) by {
            assert(vrs@.metadata.owner_references.unwrap()[0] == vd@.controller_owner_ref());
        }
    }
    vrs
}

pub fn template_with_hash(vd: &VDeployment, hash: String) -> (pod_template_spec: PodTemplateSpec)
requires
    vd@.well_formed(),
ensures
    pod_template_spec@ == #[trigger] model_reconciler::template_with_hash(vd@, hash@),
{
    let mut labels = vd.spec().template().metadata().unwrap().labels().unwrap().clone();
    let mut template_meta = ObjectMeta::default();
    template_meta.set_labels(labels);
    template_meta.add_label("pod-template-hash".to_string(), hash);
    let mut pod_template_spec = PodTemplateSpec::default();
    pod_template_spec.set_metadata(template_meta);
    pod_template_spec.set_spec(vd.spec().template().spec().unwrap().clone());
    assert(pod_template_spec@.metadata.unwrap().labels == model_reconciler::template_with_hash(vd@, hash@).metadata.unwrap().labels);
    pod_template_spec
}

pub fn match_template_without_hash(vd: &VDeployment, vrs: &VReplicaSet) -> (res: bool)
requires
    vd@.well_formed(),
    model_util::valid_owned_object(vrs@, vd@),
ensures res == model_util::match_template_without_hash(vd@, vrs@),
{
    let mut vrs_template = vrs.spec().template().unwrap().clone();
    let mut labels = vrs_template.metadata().unwrap().labels().unwrap();
    labels.remove(&"pod-template-hash".to_string());
    let mut template_meta = vrs_template.metadata().unwrap().clone();
    template_meta.set_labels(labels);
    vrs_template.set_metadata(template_meta);
    vd.spec().template().eq(&vrs_template)
}

pub fn make_owner_references(vd: &VDeployment) -> (owner_references: Vec<OwnerReference>)
requires
    vd@.well_formed(),
ensures
    owner_references@.map_values(|or: OwnerReference| or@) == model_reconciler::make_owner_references(vd@),
{
    let mut owner_references = Vec::new();
    owner_references.push(vd.controller_owner_ref());
    proof {
        assert(owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@) =~= model_reconciler::make_owner_references(vd@));
    }
    owner_references
}

} // verus!
