use crate::kubernetes_api_objects::error::APIError;
use crate::kubernetes_api_objects::exec::{prelude::*, volume::*};
use crate::kubernetes_api_objects::spec::{prelude::*, volume::*};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::model::reconciler::pod_has_ord;
use crate::vstatefulset_controller::trusted::exec_types::VStatefulSet;
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::vstatefulset_controller::trusted::reconciler::get_ordinal;
use crate::vstatefulset_controller::trusted::reconciler::sort_pods_by_ord;
use crate::vstatefulset_controller::trusted::step::VStatefulSetReconcileStep;
use crate::vstatefulset_controller::trusted::step::VStatefulSetReconcileStepView;
use crate::vstd_ext::string_view::StringView;
use crate::vstd_ext::{seq_lib::*, string_map::StringMap, vec_lib::*};
use crate::{
    vstatefulset_controller::model::reconciler as model_reconciler,
    vstatefulset_controller::trusted::reconciler as trusted_reconciler,
    vstatefulset_controller::trusted::step::*, vstd_ext::string_view::usize_to_string,
};
use vstd::{prelude::*, seq_lib::*};

verus! {

pub struct VStatefulSetReconcileState {
    pub reconcile_step: VStatefulSetReconcileStep,
    pub needed: Vec<Option<Pod>>,
    pub needed_index: usize,
    pub condemned: Vec<Pod>,
    pub condemned_index: usize,
    pub pvcs: Vec<PersistentVolumeClaim>,
    pub pvc_index: usize,
}

impl View for VStatefulSetReconcileState {
    type V = model_reconciler::VStatefulSetReconcileState;

    open spec fn view(&self) -> Self::V {
        model_reconciler::VStatefulSetReconcileState {
            reconcile_step: self.reconcile_step@,
            needed: self.needed.deep_view(),
            needed_index: self.needed_index as nat,
            condemned: self.condemned.deep_view(),
            condemned_index: self.condemned_index as nat,
            pvcs: self.pvcs.deep_view(),
            pvc_index: self.pvc_index as nat,
        }
    }
}

pub struct VStatefulSetReconciler {}

impl Reconciler for VStatefulSetReconciler {
    type S = VStatefulSetReconcileState;
    type K = VStatefulSet;
    type EReq = VoidEReq;
    type EResp = VoidEResp;
    type M = model_reconciler::VStatefulSetReconciler;

    fn reconcile_init_state() -> Self::S {
        reconcile_init_state()
    }

    fn reconcile_core(cr: &Self::K, resp_o: Option<Response<Self::EResp>>, state: Self::S) -> (Self::S, Option<Request<Self::EReq>>)
    {
        reconcile_core(cr, resp_o, state)   
    }

    fn reconcile_done(state: &Self::S) -> bool
    {
        reconcile_done(state)
    }

    fn reconcile_error(state: &Self::S) -> bool
    {        
        reconcile_error(state)
    }

}

pub fn reconcile_init_state() -> (state: VStatefulSetReconcileState)
    ensures state@ == model_reconciler::reconcile_init_state()
{
    let init_state = VStatefulSetReconcileState {
        reconcile_step: VStatefulSetReconcileStep::Init,
        needed: Vec::new(),
        needed_index: 0,
        condemned: Vec::new(),
        condemned_index: 0,
        pvcs: Vec::new(),
        pvc_index: 0
    };
    proof {
        let model_init_state = model_reconciler::reconcile_init_state();
        assert(init_state.needed.deep_view() == model_init_state.needed);
        assert(init_state.condemned.deep_view() == model_init_state.condemned);
        assert(init_state.pvcs.deep_view() == model_init_state.pvcs);
    }
    init_state
}

pub fn reconcile_done(state: &VStatefulSetReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_done(state@)
{
    match state.reconcile_step {
        VStatefulSetReconcileStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &VStatefulSetReconcileState) -> (res: bool)
    ensures res == model_reconciler::reconcile_error(state@)
{
    match state.reconcile_step {
        VStatefulSetReconcileStep::Error => true,
        _ => false
    }
}

pub fn reconcile_core(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::reconcile_core(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{

    match state.reconcile_step {
        VStatefulSetReconcileStep::Init => { handle_init(vsts, resp_o, state) },
        VStatefulSetReconcileStep::AfterListPod => { handle_after_list_pod(vsts, resp_o, state) },
        VStatefulSetReconcileStep::GetPVC => { handle_get_pvc(vsts, resp_o, state) },
        VStatefulSetReconcileStep::AfterGetPVC => { handle_after_get_pvc(vsts, resp_o, state) },
        VStatefulSetReconcileStep::CreatePVC => { handle_create_pvc(vsts, resp_o, state) },
        VStatefulSetReconcileStep::AfterCreatePVC => { handle_after_create_pvc(vsts, resp_o, state)
        },
        VStatefulSetReconcileStep::SkipPVC => { handle_skip_pvc(vsts, resp_o, state) },
        VStatefulSetReconcileStep::CreateNeeded => { handle_create_needed(vsts, resp_o, state) },
        VStatefulSetReconcileStep::AfterCreateNeeded => {
            handle_after_create_needed(vsts, resp_o, state)
        },
        VStatefulSetReconcileStep::UpdateNeeded => { handle_update_needed(vsts, resp_o, state) },
        VStatefulSetReconcileStep::AfterUpdateNeeded => {
            handle_after_update_needed(vsts, resp_o, state)
        },
        VStatefulSetReconcileStep::DeleteCondemned => { handle_delete_condemned(vsts, resp_o, state)
        },
        VStatefulSetReconcileStep::AfterDeleteCondemned => {
            handle_after_delete_condemned(vsts, resp_o, state)
        },
        // At this point, we should have desired number of replicas running (tho with old versions).
        // The next step DeleteOutdated deletes the old replica with largest ordinal, and the next
        // reconcile will do the remaining jobs to start a new one (and delete the next old one).
        VStatefulSetReconcileStep::DeleteOutdated => { handle_delete_outdated(vsts, resp_o, state)
        },
        VStatefulSetReconcileStep::AfterDeleteOutdated => {
            handle_after_delete_outdated(vsts, resp_o, state)
        },
        _ => { (state, None) },
    }
}

pub fn handle_init(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_init(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if vsts.metadata().has_deletion_timestamp() {
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStep::Done,
            ..state
        };
        (state_prime, None)
    } else {
        let req = KubeAPIRequest::ListRequest(
            KubeListRequest {
                api_resource: Pod::api_resource(),
                namespace: vsts.metadata().namespace().unwrap(),
            },
        );
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStep::AfterListPod,
            ..state
        };
        (state_prime, Some(Request::KRequest(req)))
    }
}

pub fn handle_after_list_pod(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_after_list_pod(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if is_some_k_list_resp!(resp_o) {
        let extracted = extract_some_k_list_resp!(resp_o);
        if extracted.is_err() {
            return (error_state(state), None)
        }
        let objs = extracted.unwrap();
        let pods_or_none = objects_to_pods(objs);
        if pods_or_none.is_none() {
            (error_state(state), None)
        } else {
            let pods = pods_or_none.unwrap();
            let filtered_pods = filter_pods(pods, vsts);
            let replicas = vsts.spec().replicas().unwrap_or(1);
            if replicas >= 0 {
                let (needed, condemned) = partition_pods(
                    vsts.metadata().name().unwrap(),
                    replicas as usize,
                    filtered_pods,
                );
                let needed_index = 0;
                let condemned_index = 0;
                let pvc_index = 0;
                let pvcs = make_pvcs(vsts, 0);

                let state_without_step = VStatefulSetReconcileState {
                    needed: needed.clone(),
                    condemned: condemned.clone(),
                    pvcs: pvcs.clone(),
                    needed_index: needed_index,
                    condemned_index: condemned_index,
                    pvc_index: pvc_index,
                    ..state
                };

                if needed_index < needed.len() {
                    // There are more pods to create/update
                    if pvcs.len() > 0 {
                        // There is at least one pvc for the next pod to handle
                        (
                            VStatefulSetReconcileState {
                                reconcile_step: VStatefulSetReconcileStep::GetPVC,
                                ..state_without_step
                            },
                            None,
                        )
                    } else {
                        // There is no pvc to handle, so handle the next pod directly
                        if needed[needed_index].is_none() {
                            // Create the pod
                            (
                                VStatefulSetReconcileState {
                                    reconcile_step: VStatefulSetReconcileStep::CreateNeeded,
                                    ..state_without_step
                                },
                                None,
                            )
                        } else {
                            // Update the pod
                            (
                                VStatefulSetReconcileState {
                                    reconcile_step: VStatefulSetReconcileStep::UpdateNeeded,
                                    ..state_without_step
                                },
                                None,
                            )
                        }
                    }
                } else {
                    if condemned_index < condemned.len() {
                        (
                            VStatefulSetReconcileState {
                                reconcile_step: VStatefulSetReconcileStep::DeleteCondemned,
                                pvc_index: pvcs.len(), // reset the index when entering DeleteCondemned state
                                ..state_without_step
                            },
                            None,
                        )
                    } else {
                        (
                            VStatefulSetReconcileState {
                                reconcile_step: VStatefulSetReconcileStep::DeleteOutdated,
                                pvc_index: pvcs.len(),
                                ..state_without_step
                            },
                            None,
                        )
                    }
                }
            } else {
                (error_state(state), None)
            }
        }
    } else {
        (error_state(state), None)
    }
}

pub fn handle_get_pvc(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_get_pvc(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if state.pvc_index < state.pvcs.len() {
        // TODO: what to do about this?
        if state.pvcs[state.pvc_index].metadata().name().is_none() {
            return (error_state(state), None);
        }

        let req = KubeAPIRequest::GetRequest(
            KubeGetRequest {
                api_resource: PersistentVolumeClaim::api_resource(),
                name: state.pvcs[state.pvc_index].metadata().name().unwrap(),
                namespace: vsts.metadata().namespace().unwrap(),
            },
        );
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStep::AfterGetPVC,
            ..state
        };
        (state_prime, Some(Request::KRequest(req)))
    } else {
        (error_state(state), None)
    }
}

pub fn handle_after_get_pvc(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_after_get_pvc(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if is_some_k_get_resp!(resp_o) {
        assert(is_some_k_get_resp_view(resp_o.deep_view()));
        let result = extract_some_k_get_resp!(resp_o);
        if result.is_ok() {
            let state_prime = VStatefulSetReconcileState {
                reconcile_step: VStatefulSetReconcileStep::SkipPVC,
                ..state
            };
            (state_prime, None)
        } else {
            let not_found = matches!(result.unwrap_err(), APIError::ObjectNotFound);
            if not_found {
                let state_prime = VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStep::CreatePVC,
                    ..state
                };
                (state_prime, None)
            } else {
                (error_state(state), None)
            }
        }
    } else {
        (error_state(state), None)
    }
}

pub fn handle_create_pvc(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_create_pvc(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if state.pvc_index < state.pvcs.len() {
        let req = KubeAPIRequest::CreateRequest(
            KubeCreateRequest {
                api_resource: PersistentVolumeClaim::api_resource(),
                namespace: vsts.metadata().namespace().unwrap(),
                obj: state.pvcs[state.pvc_index].clone().marshal(),
            },
        );
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStep::AfterCreatePVC,
            pvc_index: state.pvc_index + 1,
            ..state
        };
        (state_prime, Some(Request::KRequest(req)))
    } else {
        (error_state(state), None)
    }
}

pub fn handle_after_create_pvc(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_after_create_pvc(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if is_some_k_create_resp!(resp_o) {
        let result = extract_some_k_create_resp!(resp_o);
        if result.is_ok() || (result.is_err()
            && matches!(result.unwrap_err(), APIError::ObjectAlreadyExists)) {
            handle_after_create_or_skip_pvc_helper(vsts, state)
        } else {
            (error_state(state), None)
        }
    } else {
        (error_state(state), None)
    }
}

pub fn handle_skip_pvc(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_skip_pvc(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if state.pvc_index < state.pvcs.len() {
        let state_prime = VStatefulSetReconcileState {
            pvc_index: state.pvc_index + 1,
            ..state
        };
        handle_after_create_or_skip_pvc_helper(vsts, state_prime)
    } else {
        (error_state(state), None)
    }
}

pub fn handle_create_needed(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_create_needed(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if state.needed_index < state.needed.len() {
        let req = KubeAPIRequest::CreateRequest(
            KubeCreateRequest {
                api_resource: Pod::api_resource(),
                namespace: vsts.metadata().namespace().unwrap(),
                obj: make_pod(&vsts, state.needed_index).marshal(),
            },
        );

        let new_needed_index = state.needed_index + 1;

        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStep::AfterCreateNeeded,
            needed_index: new_needed_index,
            ..state
        };
        (state_prime, Some(Request::KRequest(req)))
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub fn handle_after_create_needed(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_after_create_needed(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if is_some_k_create_resp!(resp_o) {
        let result = extract_some_k_create_resp!(resp_o);
        if result.is_ok() || (result.is_err()
            && matches!(result.unwrap_err(), APIError::ObjectAlreadyExists)) {
            handle_after_create_or_after_update_needed_helper(vsts.clone(), state)
        } else {
            (error_state(state), None)
        }
    } else {
        (error_state(state), None)
    }
}

pub fn handle_update_needed(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_update_needed(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if state.needed_index < state.needed.len() && state.needed[state.needed_index].is_some() {
        let old_pod = state.needed[state.needed_index].clone().unwrap();

        if old_pod.metadata().name().is_none() {
            return (error_state(state), None)
        }

        let ordinal = state.needed_index;
        let new_pod = update_storage(vsts, update_identity(old_pod, ordinal), ordinal);

        let req = KubeAPIRequest::GetThenUpdateRequest(
            KubeGetThenUpdateRequest {
                api_resource: Pod::api_resource(),
                name: new_pod.metadata().name().unwrap(),
                namespace: vsts.metadata().namespace().unwrap(),
                owner_ref: vsts.controller_owner_ref(),
                obj: new_pod.marshal(),
            },
        );

        let new_needed_index = state.needed_index + 1;

        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStep::AfterUpdateNeeded,
            needed_index: new_needed_index,
            ..state
        };
        (state_prime, Some(Request::KRequest(req)))
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub fn handle_after_update_needed(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_after_update_needed(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if is_some_k_get_then_update_resp!(resp_o) {
        let result = extract_some_k_get_then_update_resp!(resp_o);
        if result.is_ok() {
            handle_after_create_or_after_update_needed_helper(vsts.clone(), state)
        } else {
            (error_state(state), None)
        }
    } else {
        (error_state(state), None)
    }
}

pub fn handle_delete_condemned(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_delete_condemned(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if state.condemned_index < state.condemned.len() {
        let condemned_pod = &state.condemned[state.condemned_index];
        if condemned_pod.metadata().name().is_none() {
            return (error_state(state), None);
        }
        let req = KubeAPIRequest::GetThenDeleteRequest(
            KubeGetThenDeleteRequest {
                api_resource: Pod::api_resource(),
                name: condemned_pod.metadata().name().unwrap(),
                namespace: vsts.metadata().namespace().unwrap(),
                owner_ref: vsts.controller_owner_ref(),
            },
        );

        let new_condemned_index = state.condemned_index + 1;

        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStep::AfterDeleteCondemned,
            condemned_index: new_condemned_index,
            ..state
        };

        (state_prime, Some(Request::KRequest(req)))
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub fn handle_after_delete_condemned(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_after_delete_condemned(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if is_some_k_get_then_delete_resp!(resp_o) {
        let result = extract_some_k_get_then_delete_resp!(resp_o);
        if result.is_ok() || (result.is_err()
            && matches!(result.unwrap_err(), APIError::ObjectNotFound)) {
            if state.condemned_index < state.condemned.len() {
                (
                    VStatefulSetReconcileState {
                        reconcile_step: VStatefulSetReconcileStep::DeleteCondemned,
                        ..state
                    },
                    None,
                )
            } else {
                (delete_outdated_state(state), None)
            }
        } else {
            (error_state(state), None)
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub fn handle_delete_outdated(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_delete_outdated(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    if let Some(pod) = get_largest_unmatched_pods(&vsts, &state.needed) {

        if pod.metadata().name().is_none() {
            return (error_state(state), None)
        }

        let req = KubeAPIRequest::GetThenDeleteRequest(KubeGetThenDeleteRequest {
            api_resource: Pod::api_resource(),
            name: pod.metadata().name().unwrap(),
            namespace: vsts.metadata().namespace().unwrap(),
            owner_ref: vsts.controller_owner_ref(),
        });
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStep::AfterDeleteOutdated,
            ..state
        };
        (state_prime, Some(Request::KRequest(req)))
    } else {
        (done_state(state), None)
    }
}

pub fn handle_after_delete_outdated(
    vsts: &VStatefulSet,
    resp_o: Option<Response<VoidEResp>>,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_after_delete_outdated(
            vsts@,
            resp_o.deep_view(),
            state@,
        ),
{
    let res = is_some_k_get_then_delete_resp!(resp_o);
    proof {
        assert(res == is_some_k_get_then_delete_resp_view(resp_o.deep_view()));
    }
    if is_some_k_get_then_delete_resp!(resp_o) {
        let result = extract_some_k_get_then_delete_resp!(resp_o);
        if result.is_ok() || (result.is_err()
            && matches!(result.unwrap_err(), APIError::ObjectNotFound)) {
            (done_state(state), None)
        } else {
            (error_state(state), None)
        }
    } else {
        // This should be unreachable
        (error_state(state), None)
    }
}

pub fn handle_after_create_or_skip_pvc_helper(
    vsts: &VStatefulSet,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view()) == model_reconciler::handle_after_create_or_skip_pvc_helper(
            vsts@,
            state@,
        ),
{
    if state.pvc_index < state.pvcs.len() {
        let state_prime = VStatefulSetReconcileState {
            reconcile_step: VStatefulSetReconcileStep::GetPVC,
            ..state
        };
        (state_prime, None)
    } else {
        // Move to next pod
        if state.needed_index < state.needed.len() {
            if state.needed[state.needed_index].is_none() {
                let state_prime = VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStep::CreateNeeded,
                    ..state
                };
                (state_prime, None)
            } else {
                let state_prime = VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStep::UpdateNeeded,
                    ..state
                };
                (state_prime, None)
            }
        } else {
            (error_state(state), None)
        }
    }
}

pub fn handle_after_create_or_after_update_needed_helper(
    vsts: VStatefulSet,
    state: VStatefulSetReconcileState,
) -> (res: (VStatefulSetReconcileState, Option<Request<VoidEReq>>))
    requires
        vsts@.well_formed(),
    ensures
        (res.0@, res.1.deep_view())
            == model_reconciler::handle_after_create_or_after_update_needed_helper(vsts@, state@),
{
    if state.needed_index < state.needed.len() {
        // There are more pods to create/update
        let new_pvcs = make_pvcs(&vsts, state.needed_index);
        let new_pvc_index = 0;
        if new_pvcs.len() > 0 {
            // There is at least one pvc for the next pod to handle
            (
                VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStep::GetPVC,
                    pvcs: new_pvcs,
                    pvc_index: new_pvc_index,
                    ..state
                },
                None,
            )
        } else {
            if state.needed[state.needed_index].is_none() {
                // Create the pod
                (
                    VStatefulSetReconcileState {
                        reconcile_step: VStatefulSetReconcileStep::CreateNeeded,
                        ..state
                    },
                    None,
                )
            } else {
                (
                    VStatefulSetReconcileState {
                        reconcile_step: VStatefulSetReconcileStep::UpdateNeeded,
                        ..state
                    },
                    None,
                )
            }
        }
    } else {
        if state.condemned_index < state.condemned.len() {
            (
                VStatefulSetReconcileState {
                    reconcile_step: VStatefulSetReconcileStep::DeleteCondemned,
                    ..state
                },
                None,
            )
        } else {
            (delete_outdated_state(state), None)
        }
    }
}

pub fn delete_outdated_state(state: VStatefulSetReconcileState) -> (result:
    VStatefulSetReconcileState)
    ensures
        result@ == model_reconciler::delete_outdated_state(state@),
{
    VStatefulSetReconcileState {
        reconcile_step: VStatefulSetReconcileStep::DeleteOutdated,
        ..state
    }
}

pub fn done_state(state: VStatefulSetReconcileState) -> (result: VStatefulSetReconcileState)
    ensures
        result@ == model_reconciler::done_state(state@),
{
    VStatefulSetReconcileState { reconcile_step: VStatefulSetReconcileStep::Done, ..state }
}

pub fn error_state(state: VStatefulSetReconcileState) -> (result: VStatefulSetReconcileState)
    ensures
        result@ == model_reconciler::error_state(state@),
{
    VStatefulSetReconcileState { reconcile_step: VStatefulSetReconcileStep::Error, ..state }
}

pub fn make_pod(vsts: &VStatefulSet, ordinal: usize) -> (pod: Pod)
    requires
        vsts@.well_formed(),
    ensures
        pod@ == model_reconciler::make_pod(vsts@, ordinal as nat),
{
    let mut pod = Pod::default();
    pod.set_metadata(
        {
            let mut metadata = ObjectMeta::default();
            let template_meta = vsts.spec().template().metadata().unwrap();
            metadata.set_name(pod_name(vsts.metadata().name().unwrap(), ordinal));
            if template_meta.labels().is_some() {
                metadata.set_labels(template_meta.labels().unwrap());
            }
            if template_meta.annotations().is_some() {
                metadata.set_annotations(template_meta.annotations().unwrap());
            }
            if template_meta.finalizers().is_some() {
                metadata.set_finalizers(template_meta.finalizers().unwrap());
            }
            metadata.set_owner_references(make_owner_references(vsts));
            metadata
        },
    );

    pod.set_spec(vsts.spec().template().spec().unwrap());
    update_storage(vsts, init_identity(vsts, pod, ordinal), ordinal)
}

// TODO: finish implementing this
#[verifier(external_body)]
pub fn update_storage(vsts: &VStatefulSet, mut pod: Pod, ordinal: usize) -> (result: Pod)
    requires
        vsts@.well_formed(),
    ensures
        result@ == model_reconciler::update_storage(vsts@, pod@, ordinal as nat),
{
    let pvcs = make_pvcs(vsts, ordinal as usize);
    let current_volumes = if pod.spec().unwrap().volumes().is_some() {
        pod.spec().unwrap().volumes().unwrap()
    } else {
        Vec::new()
    };

    let (mut new_volumes, templates) = if vsts.spec().volume_claim_templates().is_some() {
        let templates = vsts.spec().volume_claim_templates().unwrap();
        let mut new_volumes: Vec<Volume> = Vec::new();
        let len = templates.len();
        for i in 0..len
            invariant
                vsts@.well_formed(),
                new_volumes.deep_view() == new_volumes_spec.take(i)
        {
            proof {
                // this satisfies a trigger in the vsts's state_validation saying that all volume_claim_templates are valid
                assert(vsts@.spec.volume_claim_templates->0[i as int].state_validation());
            }
            let mut vol = Volume::default();
            vol.set_name(templates[i].metadata().name().unwrap());
            let mut pvc = PersistentVolumeClaimVolumeSource::default();
            pvc.set_claim_name(pvcs[i].metadata().name().unwrap());
            pvc.set_read_only(false);
            vol.set_persistent_volume_claim_source(pvc);
            new_volumes.push(vol);
        }
        (new_volumes, templates)
    } else {
        (Vec::new(), Vec::new())
    };

    let mut filtered_current_volumes = Vec::new();
    for i in 0..current_volumes.len() {
        let vol = &current_volumes[i];
        if templates.iter().all(|template: &PersistentVolumeClaim| vol.name() != template.metadata().name().unwrap()) {
            filtered_current_volumes.push(vol.clone());
        }
    }

    let mut old_spec = pod.spec().unwrap();
    new_volumes.extend(filtered_current_volumes);
    old_spec.set_volumes(new_volumes);
    pod.set_spec(old_spec);
    pod
}

pub fn init_identity(vsts: &VStatefulSet, pod: Pod, ordinal: usize) -> (result: Pod)
    requires
        vsts@.well_formed(),
        pod@.metadata.name is Some,
        pod@.spec is Some
    ensures
        result@ == model_reconciler::init_identity(vsts@, pod@, ordinal as nat),
{
    
    let mut updated_pod = update_identity(pod, ordinal);
    let mut pod_spec = updated_pod.spec().unwrap();

    pod_spec.set_hostname(updated_pod.metadata().name().unwrap());
    pod_spec.set_subdomain(vsts.spec().service_name());

    updated_pod.set_spec(pod_spec);

    updated_pod
}

// TODO: implement this
pub fn update_identity(pod: Pod, ordinal: usize) -> (result: Pod)
    requires
        pod@.metadata.name is Some,
    ensures
        result@ == model_reconciler::update_identity(pod@, ordinal as nat),
{

    let mut result = pod.clone();
    let mut meta = pod.metadata();
    let mut labels = meta.labels().unwrap_or(StringMap::empty());
    labels.insert("statefulset.kubernetes.io/pod-name".to_string(), meta.name().unwrap());
    labels.insert("apps.kubernetes.io/pod-index".to_string(), usize_to_string(ordinal));
    meta.set_labels(labels);
    result.set_metadata(meta);
    result
}

pub fn make_pvc(vsts: &VStatefulSet, ordinal: usize, i: usize) -> (pvc: PersistentVolumeClaim)
    requires
        vsts@.well_formed() && vsts@.spec.volume_claim_templates is Some && i
            < vsts@.spec.volume_claim_templates->0.len(),
    ensures
        pvc@ == model_reconciler::make_pvc(vsts@, ordinal as nat, i as int),
{
    proof {
        // this satisfies a trigger in the vsts's state_validation saying that all volume_claim_templates are valid
        assert(vsts@.spec.volume_claim_templates->0[i as int].state_validation());
    }

    let pvc_template = vsts.spec().volume_claim_templates().unwrap()[i].clone();
    let mut pvc = PersistentVolumeClaim::default();
    pvc.set_metadata(
        {
            let mut metadata = ObjectMeta::default();

            metadata.set_namespace(vsts.metadata().namespace().unwrap());

            let pvc_labels = pvc_template.metadata().labels();
            let vsts_labels = vsts.spec().selector().match_labels();
            let labels = if pvc_labels.is_some() {
                if vsts_labels.is_some() {
                    let mut pvc_map = pvc_labels.unwrap();
                    pvc_map.extend(vsts_labels.unwrap());
                    Some(pvc_map)
                } else {
                    pvc_labels
                }
            } else {
                vsts_labels
            };
            if labels.is_some() {
                metadata.set_labels(labels.unwrap());
            }
            metadata.set_name(
                pvc_name(
                    pvc_template.metadata().name().unwrap(),
                    vsts.metadata().name().unwrap(),
                    ordinal,
                ),
            );

            metadata
        },
    );
    pvc.set_spec(pvc_template.spec().unwrap());
    pvc
}

pub fn make_pvcs(vsts: &VStatefulSet, ordinal: usize) -> (pvcs: Vec<PersistentVolumeClaim>)
    requires
        vsts@.well_formed(),
    ensures
        pvcs.deep_view() == model_reconciler::make_pvcs(vsts@, ordinal as nat),
{
    if vsts.spec().volume_claim_templates().is_some() {
        let mut result: Vec<PersistentVolumeClaim> = Vec::new();
        let len = vsts.spec().volume_claim_templates().unwrap().len();

        assert(len == vsts@.spec.volume_claim_templates->0.len());

        for idx in 0..len
            invariant
                result.deep_view() == model_reconciler::make_pvcs(vsts@, ordinal as nat).take(
                    idx as int,
                ),
                vsts@.well_formed(),
                vsts@.spec.volume_claim_templates is Some,
                len == vsts@.spec.volume_claim_templates->0.len(),
            decreases len - idx,
        {
            result.push(make_pvc(&vsts, ordinal, idx));
            proof {
                let prev = result.deep_view().drop_last();
                let model_pvcs = model_reconciler::make_pvcs(vsts@, ordinal as nat);
                // assert(prev == model_pvcs.take(idx as int));
                // assert(result.deep_view().last() == model_pvcs[idx as int]);
                assert(model_pvcs.take(idx + 1) == model_pvcs.take(idx as int).push(
                    model_pvcs[idx as int],
                ));
            }
        }
        result
    } else {
        Vec::new()
    }
}

pub fn get_pod_with_ord(parent_name: String, pods: &Vec<Pod>, ord: usize) -> (result: Option<Pod>)
    requires
        pods.deep_view().all(|pod: PodView| pod.metadata.name is Some),
    ensures
        result.deep_view() == model_reconciler::get_pod_with_ord(
            parent_name@,
            pods.deep_view(),
            ord as nat,
        ),
{
    let mut filtered: Vec<Pod> = Vec::new();

    proof {
        let model_filtered = pods.deep_view().take(0).filter(
            model_reconciler::pod_has_ord(parent_name@, ord as nat),
        );
        assert(filtered.deep_view() == model_filtered);
    }

    for idx in 0..pods.len()
        invariant
            idx <= pods.len(),
            filtered.deep_view() == pods.deep_view().take(idx as int).filter(
                model_reconciler::pod_has_ord(parent_name@, ord as nat),
            ),
            pods.deep_view().all(|pod: PodView| pod.metadata.name is Some),
    {
        let pod = &pods[idx];
        proof {
            assert(pod@.metadata.name is Some) by {
                assert((|pod: PodView| pod.metadata.name is Some)(pods.deep_view()[idx as int]));
            }
        }
        if get_ordinal(&parent_name, &pod.metadata().name().unwrap()).is_some() && get_ordinal(&parent_name, &pod.metadata().name().unwrap()).unwrap()
            == ord {
            filtered.push(pod.clone());
        }
        proof {
            let old_filtered = if model_reconciler::pod_has_ord(parent_name@, ord as nat)(pod@) {
                filtered.deep_view().drop_last()
            } else {
                filtered.deep_view()
            };
            assert(old_filtered == pods.deep_view().take(idx as int).filter(
                model_reconciler::pod_has_ord(parent_name@, ord as nat),
            ));
            lemma_filter_push(
                pods.deep_view().take(idx as int),
                model_reconciler::pod_has_ord(parent_name@, ord as nat),
                pod@,
            );
            assert(pods.deep_view().take(idx as int).push(pod@) == pods.deep_view().take(idx + 1));
            assert(filtered.deep_view() == pods.deep_view().take(idx + 1).filter(
                model_reconciler::pod_has_ord(parent_name@, ord as nat),
            ));
        }
    }

    proof {
        assert(pods.deep_view().take(pods.len() as int) == pods.deep_view());
    }

    assert(filtered.deep_view() == pods.deep_view().filter(
        model_reconciler::pod_has_ord(parent_name@, ord as nat),
    ));

    if filtered.len() > 0 {
        Some(filtered[0].clone())
    } else {
        None
    }
}

pub fn partition_pods(parent_name: String, replicas: usize, pods: Vec<Pod>) -> (result: (
    Vec<Option<Pod>>,
    Vec<Pod>,
))
    requires
        pods.deep_view().all(|pod: PodView| pod.metadata.name is Some),
    ensures
        result.0.deep_view() == model_reconciler::partition_pods(
            parent_name@,
            replicas as nat,
            pods.deep_view(),
        ).0,
        result.1.deep_view() == model_reconciler::partition_pods(
            parent_name@,
            replicas as nat,
            pods.deep_view(),
        ).1,
{
    // needed includes all the pods that should be created or updated
    // creation/update will start with the beginning of needed where ordinal == 0
    let mut needed: Vec<Option<Pod>> = Vec::new();

    proof {
        assert_seqs_equal!(
                needed.deep_view(),
                model_reconciler::partition_pods(parent_name@, replicas as nat, pods.deep_view()).0.take(0)
            );
    }
    let mut i = 0;
    while i < replicas
        invariant
            i <= replicas,
            needed.deep_view() == model_reconciler::partition_pods(
                parent_name@,
                replicas as nat,
                pods.deep_view(),
            ).0.take(i as int),
            pods.deep_view().all(|pod: PodView| pod.metadata.name is Some),
        decreases replicas - i,
    {
        let pod_or_none = get_pod_with_ord(parent_name.clone(), &pods, i);
        needed.push(pod_or_none);

        proof {
            let needed_model: Seq<Option<PodView>> = Seq::new(
                replicas as nat,
                |ord: int|
                    model_reconciler::get_pod_with_ord(parent_name@, pods.deep_view(), ord as nat),
            );
            let needed_old = needed.deep_view().drop_last();
            let pod = pod_or_none.deep_view();

            assert(needed.deep_view() == needed_old.push(pod));

            assert(needed_old == needed_model.take(i as int));
            assert(needed_model[i as int] == model_reconciler::get_pod_with_ord(
                parent_name@,
                pods.deep_view(),
                i as nat,
            ));
            assert(pod_or_none.deep_view() == model_reconciler::get_pod_with_ord(
                parent_name@,
                pods.deep_view(),
                i as nat,
            ));
            assert(needed_model[i as int] == pod_or_none.deep_view());
        }

        i += 1;
    }

    let mut condemned: Vec<Pod> = Vec::new();

    proof {
        assert_seqs_equal!(
                condemned.deep_view(),
                pods.deep_view().take(0).filter(|pod: PodView| model_reconciler::get_ordinal(parent_name@, pod.metadata.name->0) is Some && model_reconciler::get_ordinal(parent_name@, pod.metadata.name->0)->0 >= replicas)
            );
    }

    for i in 0..pods.len()
        invariant
            condemned.deep_view() == pods.deep_view().take(i as int).filter(
                |pod: PodView|
                    model_reconciler::get_ordinal(parent_name@, pod.metadata.name->0) is Some
                        && model_reconciler::get_ordinal(parent_name@, pod.metadata.name->0)->0 >= replicas,
            ),
            pods.deep_view().all(|pod: PodView| pod.metadata.name is Some),
    {
        let pod = &pods[i];
        proof {
            assert(pod@.metadata.name is Some) by {
                assert((|pod: PodView| pod.metadata.name is Some)(pods.deep_view()[i as int]));
            }
        }
        let ordinal = get_ordinal(&parent_name, &pod.metadata().name().unwrap());
        if ordinal.is_some() && ordinal.unwrap() >= replicas {
            condemned.push(pod.clone());
        }
        proof {
            let spec_filter = |pod: PodView|
                model_reconciler::get_ordinal(parent_name@, pod.metadata.name->0) is Some
                    && model_reconciler::get_ordinal(parent_name@, pod.metadata.name->0)->0 >= replicas;
            let old_filtered = if spec_filter(pod@) {
                condemned.deep_view().drop_last()
            } else {
                condemned.deep_view()
            };
            assert(old_filtered == pods.deep_view().take(i as int).filter(spec_filter));
            lemma_filter_push(pods.deep_view().take(i as int), spec_filter, pod@);
            assert(pods.deep_view().take(i as int).push(pod@) == pods.deep_view().take(i + 1));
        }
    }

    proof {
        assert(pods.deep_view().take(pods.len() as int) == pods.deep_view());
    }

    sort_pods_by_ord(&parent_name, &mut condemned);

    (needed, condemned)
}

// copied verbatim from vreplicaset_controller::objects_to_pods
// should we refactor to only have one version of this?
fn objects_to_pods(objs: Vec<DynamicObject>) -> (pods_or_none: Option<Vec<Pod>>)
    ensures
        pods_or_none.deep_view() == model_reconciler::objects_to_pods(objs.deep_view()),
{
    let mut pods = Vec::new();
    let mut idx = 0;

    proof {
        let model_result = model_reconciler::objects_to_pods(objs.deep_view());
        if model_result.is_some() {
            assert_seqs_equal!(
                    pods.deep_view(),
                    model_result.unwrap().take(0)
                );
        }
    }

    for idx in 0..objs.len()
        invariant
            idx <= objs.len(),
            ({
                let model_result = model_reconciler::objects_to_pods(objs.deep_view());
                &&& (model_result.is_some() ==> pods.deep_view() == model_result.unwrap().take(
                    idx as int,
                ))
                &&& forall|i: int| 0 <= i < idx ==> PodView::unmarshal(#[trigger] objs@[i]@).is_ok()
            }),
    {
        let pod_or_error = Pod::unmarshal(objs[idx].clone());
        if pod_or_error.is_ok() {
            pods.push(pod_or_error.unwrap());
            proof {
                // Show that the pods Vec and the model_result are equal up to index idx + 1.
                let model_result = model_reconciler::objects_to_pods(objs.deep_view());
                if (model_result.is_some()) {
                    assert(model_result.unwrap().take((idx + 1) as int)
                        == model_result.unwrap().take(idx as int) + seq![
                        model_result.unwrap()[idx as int],
                    ]);
                    assert_seqs_equal!(
                            pods.deep_view(),
                            model_result.unwrap().take((idx + 1) as int)
                        );
                }
            }
        } else {
            proof {
                // Show that if a pod was unable to be serialized, the model would return None.
                let model_input = objs.deep_view();
                let model_result = model_reconciler::objects_to_pods(model_input);
                assert(model_input.filter(
                    |o: DynamicObjectView| PodView::unmarshal(o).is_err(),
                ).contains(model_input[idx as int]));
                assert(model_result == None::<Seq<PodView>>);
            }
            return None;
        }
    }

    proof {
        let model_input = objs.deep_view();
        let model_result = model_reconciler::objects_to_pods(model_input);

        // Prove, by contradiction, that the model_result can't be None.
        let filter_result = model_input.filter(
            |o: DynamicObjectView| PodView::unmarshal(o).is_err(),
        );
        assert(filter_result.len() == 0) by {
            if filter_result.len() != 0 {
                seq_filter_contains_implies_seq_contains(
                    model_input,
                    |o: DynamicObjectView| PodView::unmarshal(o).is_err(),
                    filter_result[0],
                );
            }
        };
        assert(model_result.is_some());

        assert(model_result.unwrap().take(objs.len() as int) == model_result.unwrap());
    }

    Some(pods)
}

pub fn make_owner_references(vsts: &VStatefulSet) -> (references: Vec<OwnerReference>)
    requires
        vsts@.well_formed(),
    ensures
        references.deep_view() =~= model_reconciler::make_owner_references(vsts@),
{
    vec![vsts.controller_owner_ref()]
}

// spec returns filter function instead of filtered_pods for easier proof
pub fn filter_pods(pods: Vec<Pod>, vsts: &VStatefulSet) -> (filtered: Vec<Pod>)
    requires
        vsts@.well_formed(),
    ensures
        filtered.deep_view() =~= pods.deep_view().filter(model_reconciler::pod_filter(vsts@)),
{
    let mut filtered_pods = Vec::new();

    proof {
        assert_seqs_equal!(filtered_pods.deep_view(),pods.deep_view().filter(model_reconciler::pod_filter(vsts@)).take(0));
    }

    let mut idx = 0;
    for idx in 0..pods.len()
        invariant
            idx <= pods.len(),
            filtered_pods.deep_view() == pods.deep_view().take(idx as int).filter(model_reconciler::pod_filter(vsts@)),
            vsts@.well_formed(),
    {
        let pod = &pods[idx];
        if pod.metadata().owner_references_contains(&vsts.controller_owner_ref())
            && vsts.spec().selector().matches(pod.metadata().labels().unwrap_or(StringMap::empty()))
            && vsts.metadata().name().is_some()
            && pod.metadata().name().is_some()
            && trusted_reconciler::get_ordinal(&vsts.metadata().name().unwrap(), &pod.metadata().name().unwrap()).is_some() {
            filtered_pods.push(pod.clone());
        }
        // prove the invariant

        proof {
            let spec_filter = |pod: PodView|
                pod.metadata.owner_references_contains(vsts@.controller_owner_ref())
                && vsts@.spec.selector.matches(
                    pod.metadata.labels.unwrap_or(Map::<Seq<char>, Seq<char>>::empty()),
                )
                && vsts@.metadata.name is Some
                && pod.metadata.name is Some
                && model_reconciler::get_ordinal(
                    vsts@.metadata.name->0,
                    pod.metadata.name->0,
                ) is Some;

            let old_filtered = if spec_filter(pod@) {
                filtered_pods.deep_view().drop_last()
            } else {
                filtered_pods.deep_view()
            };

            assert(old_filtered == pods.deep_view().take(idx as int).filter(spec_filter));
            lemma_filter_push(pods.deep_view().take(idx as int), spec_filter, pod@);
            assert(pods.deep_view().take(idx as int).push(pod@) == pods.deep_view().take(
                (idx + 1) as int,
            ));
        }

    }
    assert(pods.deep_view() == pods.deep_view().take(pods.len() as int));
    filtered_pods
}

pub fn pod_name(parent_name: String, ordinal: usize) -> (result: String)
    ensures
        result@ == model_reconciler::pod_name(parent_name@, ordinal as nat),
{
    // we don't have executable CustomResource kind, hardcoded as a temporary solution
    let prefix = "vstatefulset".to_string().concat("-"); // "vstatefulset-" fails proof
    prefix.concat(pod_name_without_vsts_prefix(parent_name, ordinal).as_str())
}

pub fn pod_name_without_vsts_prefix(parent_name: String, ordinal: usize) -> (result: String)
    ensures
        result@ == model_reconciler::pod_name_without_vsts_prefix(parent_name@, ordinal as nat),
{
    parent_name.concat("-").concat(usize_to_string(ordinal).as_str())
}

pub fn pvc_name(pvc_template_name: String, vsts_name: String, ordinal: usize) -> (result: String)
    ensures
        result@ == model_reconciler::pvc_name(pvc_template_name@, vsts_name@, ordinal as nat),
{
    let prefix = "vstatefulset".to_string().concat("-");
    prefix.concat(pvc_template_name.as_str()).concat("-").concat(pod_name_without_vsts_prefix(vsts_name, ordinal).as_str())
}

pub fn pod_spec_matches(vsts: &VStatefulSet, pod: Pod) -> (res: bool) 
    requires vsts@.well_formed()
    ensures res == model_reconciler::pod_spec_matches(vsts@, pod@)
{
    if let Some(mut spec) = pod.spec() {
        let mut vsts_spec = vsts.spec().template().spec().unwrap();
        spec.unset_volumes();
        spec.unset_hostname();
        spec.unset_subdomain();
        vsts_spec.unset_volumes();
        vsts_spec.unset_hostname();
        vsts_spec.unset_subdomain();
        return spec.eq_spec(&vsts_spec);
    } else {
        return false;
    }
}

pub fn get_largest_unmatched_pods(
    vsts: &VStatefulSet,
    pods: &Vec<Option<Pod>>,
) -> (result: Option<Pod>)
    requires
        vsts@.well_formed(),
    ensures
        result.deep_view() == model_reconciler::get_largest_unmatched_pods(
            vsts@,
            pods.deep_view(),
        ),
{
    let mut filtered_pods = Vec::<Option<Pod>>::new();

    proof {
        assert_seqs_equal!(filtered_pods.deep_view(), pods.deep_view().take(0).filter(model_reconciler::outdated_pod_filter(vsts@)));
    }

    let mut ord: usize = 0;

    while ord < pods.len() 
        invariant 
            ord <= pods.len(),
            filtered_pods.deep_view() == pods.deep_view().take(ord as int).filter(model_reconciler::outdated_pod_filter(vsts@)),
            vsts@.well_formed(),
        decreases pods.len() - ord,
    {
        let pod_or_none = &pods[ord];
        if pod_or_none.is_some() && !pod_spec_matches(vsts, pod_or_none.clone().unwrap()) {
            proof {
                assert(model_reconciler::outdated_pod_filter(vsts@)(pod_or_none.deep_view()));
            }
            filtered_pods.push(pod_or_none.clone());
        }
        proof {
            let old_filtered = if model_reconciler::outdated_pod_filter(vsts@)(pod_or_none.deep_view()) {
                filtered_pods.deep_view().drop_last()
            } else {
                filtered_pods.deep_view()
            };
            assert(old_filtered == pods.deep_view().take(ord as int).filter(model_reconciler::outdated_pod_filter(vsts@)));
            lemma_filter_push(pods.deep_view().take(ord as int), model_reconciler::outdated_pod_filter(vsts@), pod_or_none.deep_view());
            assert(pods.deep_view().take(ord as int).push(pods.deep_view()[ord as int]) == pods.deep_view().take(
                (ord + 1) as int,
            ));
        }
        ord += 1;
    }

    proof {
        assert(pods.deep_view() == pods.deep_view().take(pods.len() as int));
        assert(filtered_pods.deep_view() == pods.deep_view().filter(model_reconciler::outdated_pod_filter(vsts@)));
    }

    if filtered_pods.len() > 0 {
        filtered_pods[filtered_pods.len() - 1].clone()
    } else {
        None
    }
}

} // verus!
