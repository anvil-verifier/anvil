use crate::vstatefulset_controller::{
    trusted::{spec_types::*, step::*},
    model::{reconciler::VStatefulSetReconcileState, install::*}
};
use crate::kubernetes_cluster::spec::controller::types::*;
use crate::kubernetes_api_objects::spec::resource::*;
use vstd::prelude::*;

verus! {

pub open spec fn lift_step(step: VStatefulSetReconcileStepView) -> spec_fn(ReconcileLocalState) -> bool {
    |rls: ReconcileLocalState| {
        let vsts_local_state = VStatefulSetReconcileState::unmarshal(rls)->Ok_0;
        &&& vsts_local_state.reconcile_step == step
    }
}

}