use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::{
    trusted::spec_types::*, model::reconciler::*,
    proof::predicate::*,
};
use crate::vreplicaset_controller::trusted::step::VReplicaSetRecStepView;
use vstd::prelude::*;

verus! {

pub open spec fn vrs_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    tla_forall(|vrs| vrs_eventually_stable_reconciliation_per_cr(vrs))
}

pub open spec fn vrs_eventually_stable_reconciliation_per_cr(vrs: VReplicaSetView) -> TempPred<ClusterState> {
    always(lift_state(desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches(vrs))))
}

pub open spec fn current_state_matches(vrs: VReplicaSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()])->Ok_0;
        &&& s.resources().contains_key(vrs.object_ref())
        &&& matching_pods(vrs, s.resources()).len() == vrs.spec.replicas.unwrap_or(1)
        &&& VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()]) is Ok
        &&& etcd_vrs.status is Some
        &&& etcd_vrs.status->0.replicas == etcd_vrs.spec.replicas.unwrap_or(1)
    }
}

pub open spec fn desired_state_is(vrs: VReplicaSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // same as Cluster::desired_state_is, but allow replicas: None == replicas: Some(1)
        let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()])->Ok_0;
        &&& vrs.metadata.namespace is Some
        &&& s.resources().contains_key(vrs.object_ref())
        &&& s.resources()[vrs.object_ref()].metadata.uid == vrs.metadata.uid
        &&& s.resources()[vrs.object_ref()].metadata.deletion_timestamp is None
        &&& VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()]) is Ok
        &&& etcd_vrs.spec.with_replicas(etcd_vrs.spec.replicas.unwrap_or(1))
            == vrs.spec.with_replicas(vrs.spec.replicas.unwrap_or(1))
        // required by get_then_update
        &&& vrs.metadata.owner_references is Some
        &&& s.resources()[vrs.object_ref()].metadata.owner_references is Some
        &&& vrs.metadata.owner_references->0.filter(controller_owner_filter())
            == s.resources()[vrs.object_ref()].metadata.owner_references->0.filter(controller_owner_filter())
        &&& s.resources()[vrs.object_ref()].metadata.owner_references->0.filter(controller_owner_filter()).len() == 1
    }
}

pub open spec fn matching_pods(vrs: VReplicaSetView, resources: StoredState) -> Set<DynamicObjectView> {
    resources.values().filter(|obj: DynamicObjectView| owned_selector_match_is(vrs, obj))
}

pub open spec fn owned_selector_match_is(vrs: VReplicaSetView, obj: DynamicObjectView) -> bool {
    &&& obj.kind == PodView::kind()
    &&& obj.metadata.name is Some
    &&& has_vrs_prefix(obj.metadata.name->0)
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
