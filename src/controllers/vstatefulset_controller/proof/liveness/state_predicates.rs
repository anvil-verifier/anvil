// state-encoding predicates dedicated for liveness proofs in resource_match.rs

use crate::kubernetes_api_objects::spec::{resource::*, prelude::*};
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::vstatefulset_controller::trusted::{spec_types::*, step::*};
use crate::vstatefulset_controller::model::{reconciler::*, install::*};
use crate::vstatefulset_controller::proof::predicate::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub open spec fn at_vsts_step(vsts: VStatefulSetView, controller_id: int, step_pred: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let triggering_cr = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr).unwrap();
        let local_state = s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state;
        &&& s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())
        &&& VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr).is_ok()
        &&& VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).is_ok()
        &&& step_pred(local_state)
        // alternative: make it an invariant
        &&& triggering_cr.metadata.deletion_timestamp is None
    }
}

pub open spec fn no_pending_req_in_cluster(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Cluster::no_pending_req_msg(controller_id, s, vsts.object_ref())
    }
}

pub open spec fn req_msg_is_list_pod_req(
    vsts_key: ObjectRef, controller_id: int, req_msg: Message, s: ClusterState
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
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg, s)
    }
}

pub open spec fn req_msg_is_pending_list_req_in_flight(
    vsts: VStatefulSetView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg, s)
    }
}

pub open spec fn exists_pending_list_resp_in_flight_and_match_req(
    vsts: VStatefulSetView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg, s)
        // predicate on resp_msg
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            &&& resp_msg_is_ok_list_resp_of_pods(vsts, resp_msg, s)
        }
    }
}

pub open spec fn resp_msg_is_pending_list_resp_in_flight_and_match_req(
    vsts: VStatefulSetView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let req_msg = s.ongoing_reconciles(controller_id)[vsts.object_ref()].pending_req_msg->0;
        // predicate on req_msg, it's not in_flight
        &&& Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg)
        &&& req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg, s)
        // predicate on resp_msg
        &&& #[trigger] s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& resp_msg_is_ok_list_resp_of_pods(vsts, resp_msg, s)
    }
}

// because we have controller_owner_ref which requires uid, key alone is not enough
pub open spec fn resp_msg_is_ok_list_resp_of_pods(
    vsts: VStatefulSetView, resp_msg: Message, s: ClusterState
) -> bool {
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let pod_list = objects_to_pods(resp_objs)->0;
    let managed_pod_list = filter_pods(pod_list, vsts);
    &&& resp_msg.content.is_list_response()
    &&& resp_msg.content.get_list_response().res is Ok
    &&& resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates()
    // &&& managed_pod_list.map_values(|pod: PodView| pod.object_ref()).to_set()
    //     == filter_obj_keys_managed_by_vsts(vsts, s)
    &&& forall |obj: DynamicObjectView| #[trigger] resp_objs.contains(obj) ==> {
        let key = obj.object_ref();
        let etcd_obj = s.resources()[key];
        &&& obj.kind == Kind::PodKind
        &&& obj.metadata.name is Some
        &&& obj.metadata.namespace is Some
        &&& obj.metadata.owner_references is Some
        &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()]
        &&& s.resources().contains_key(key)
        &&& weakly_eq(etcd_obj, obj)
    }
    &&& objects_to_pods(resp_objs) is Some
}

}