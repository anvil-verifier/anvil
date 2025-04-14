use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::vdeployment_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::*;
use vstd::prelude::*;


verus! {

    pub struct VDeploymentReconciler {}
    
    pub struct VDeploymentReconcileState {
        pub reconcile_step: VDeploymentRecStepView,
        pub filtered_pods: Option<Seq<PodView>>,
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
            reconcile_step: VDeploymentRecStepView::Init,
            filtered_pods: None,
        }
    }
    
    pub open spec fn reconcile_done(state: VDeploymentReconcileState) -> bool {
        match state.reconcile_step {
            VDeploymentRecStepView::Done => true,
            _ => false,
        }
    }
    
    pub open spec fn reconcile_error(state: VDeploymentReconcileState) -> bool {
        match state.reconcile_step {
            VDeploymentRecStepView::Error => true,
            _ => false,
        }
    }
    
    pub open spec fn reconcile_core(v_replica_set: VDeploymentView, resp_o: Option<ResponseView<VoidERespView>>, state: VDeploymentReconcileState) -> (VDeploymentReconcileState, Option<RequestView<VoidEReqView>>) {
    }
    
    pub open spec fn error_state(state: VDeploymentReconcileState) -> (state_prime: VDeploymentReconcileState)
    {
        VDeploymentReconcileState {
            reconcile_step: VDeploymentRecStepView::Error,
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