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

pub open spec fn req_msg_is_list_vrs_req(
    vsts_key: ObjectRef, controller_id: int, msg: Message, s: ClusterState
) -> bool {
    let req = req_msg.content->APIRequest_0;
    &&& req_msg.src == HostId::Controller(controller_id, vsts_key)
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& req is ListRequest
    &&& req->ListRequest_0 == ListRequest {
        kind: Kind::PodKind,
        namespace: vsts_key.namespace,
    }
}

pub open spec fn pending_list_req_in_flight(
    vsts_key: ObjectRef, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts_key].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts_key, req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_vrs_req(vsts_key, controller_id, req_msg, s)
    }
}

pub open spec fn req_msg_is_pending_list_req_in_flight(
    vsts_key: ObjectRef, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts_key, req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_vrs_req(vsts_key, controller_id, req_msg, s)
    }
}

pub open spec fn exists_pending_list_resp_in_flight_and_match_req(
    vsts_key: ObjectRef, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts_key].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts_key, req_msg)
        &&& req_msg_is_list_vrs_req(vsts_key, controller_id, req_msg, s)
        // predicate on resp_msg
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            // &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vsts_key, controller_id, resp_msg, s)
        }
    }
}

}