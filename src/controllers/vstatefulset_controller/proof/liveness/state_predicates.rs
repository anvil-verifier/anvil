// state-encoding predicates dedicated for liveness proofs in resource_match.rs

use crate::kubernetes_api_objects::spec::{resource::*, prelude::*};
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*};
use crate::vstatefulset_controller::trusted::{spec_types::*, step::*};
use crate::vstatefulset_controller::model::{reconciler::*, install::*};
use crate::vstatefulset_controller::proof::predicate::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub open spec fn at_vsts_step(vsts_key: ObjectRef, controller_id: int, step_pred: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let triggering_cr = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts_key].triggering_cr).unwrap();
        let local_state = s.ongoing_reconciles(controller_id)[vsts_key].local_state;
        &&& s.ongoing_reconciles(controller_id).contains_key(vsts_key)
        &&& VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts_key].triggering_cr).is_ok()
        &&& VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts_key].local_state).is_ok()
        &&& step_pred(local_state)
    }
}

pub open spec fn no_pending_req_in_cluster(vsts_key: ObjectRef, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Cluster::no_pending_req_msg(controller_id, s, vsts_key)
    }
}

}