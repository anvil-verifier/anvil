use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::trusted::step::VReplicaSetRecStepView;
use crate::vreplicaset_controller::proof::predicate::*;
use vstd::prelude::*;

verus! {

pub open spec fn vrs_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vrs| current_state_matches(vrs))
}

pub open spec fn vrs_eventually_stable_reconciliation_per_cr(vrs: VReplicaSetView) -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation_per_cr(vrs, |vrs| current_state_matches(vrs))
}

pub open spec fn current_state_matches(vrs: VReplicaSetView) -> StatePred<ClusterState> {
    |s: ClusterState|
        matching_pods(vrs, s.resources()).len() == vrs.spec.replicas.unwrap_or(1)
}

pub open spec fn matching_pods(vrs: VReplicaSetView, resources: StoredState) -> Set<DynamicObjectView> {
    resources.values().filter(|obj: DynamicObjectView| owned_selector_match_is(vrs, obj))
}

pub open spec fn owned_selector_match_is(vrs: VReplicaSetView, obj: DynamicObjectView) -> bool {
    &&& obj.kind == PodView::kind()
    &&& obj.metadata.namespace is Some
    &&& obj.metadata.namespace == vrs.metadata.namespace
    &&& obj.metadata.owner_references_contains(vrs.controller_owner_ref())
    &&& vrs.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
    &&& obj.metadata.deletion_timestamp is None
}

pub open spec fn inductive_current_state_matches(vrs: VReplicaSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& current_state_matches(vrs)(s)
        &&& s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) ==> {
            &&& {
                ||| at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Init)(s)
                ||| at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterListPods)(s)
                ||| at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Done)(s)
                ||| at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::Error)(s)
            }
            &&& if at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterListPods)(s) {
                let req_msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
                &&& s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg is Some
                &&& req_msg_is_list_pods_req(vrs, req_msg)
                &&& forall |msg| {
                    &&& #[trigger] s.in_flight().contains(msg)
                    &&& msg.src is APIServer
                    &&& resp_msg_matches_req_msg(msg, req_msg)
                } ==> resp_msg_is_ok_list_resp_containing_matching_pods(s, vrs, msg)
            } else {
                s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg is None
            }
        }
    }
}

}
