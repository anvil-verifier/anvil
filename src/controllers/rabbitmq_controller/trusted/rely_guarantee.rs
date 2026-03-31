use crate::kubernetes_api_objects::spec::{persistent_volume_claim::*, prelude::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::rabbitmq_controller::{
    trusted::{spec_types::*, step::*},
};
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub open spec fn rmq_rely_conditions(cluster: Cluster, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] rmq_rely(other_id)(s)
    }
}

// stronger rely: other controllers do not send request to RMQ subresources
pub open spec fn rmq_rely(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(other_id)
        } ==> {
            match (msg.content->APIRequest_0) {
                APIRequest::CreateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                APIRequest::UpdateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                APIRequest::GetThenUpdateRequest(req) => !is_rmq_managed_kind(req.key().kind),
                APIRequest::DeleteRequest(req) => !is_rmq_managed_kind(req.key().kind),
                APIRequest::GetThenDeleteRequest(req) => !is_rmq_managed_kind(req.key().kind),
                APIRequest::UpdateStatusRequest(req) => !is_rmq_managed_kind(req.key().kind),
                APIRequest::GetThenUpdateStatusRequest(req) => !is_rmq_managed_kind(req.key().kind),
                // Get/List requests do not interfere
                _ => true,
            }
        }
    }
}

// Helper to check if a kind is managed by the RMQ controller
pub open spec fn is_rmq_managed_kind(kind: Kind) -> bool {
    // err: `fn` calls are not allowed in patterns
    let vsts_kind = VStatefulSetView::kind();
    match kind {
        Kind::ServiceKind => true,
        Kind::SecretKind => true,
        Kind::ConfigMapKind => true,
        Kind::ServiceAccountKind => true,
        Kind::RoleKind => true,
        Kind::RoleBindingKind => true,
        vsts_kind => true,
        _ => false,
    }
}

// RMQ only creates objects of rmq-managed kind with rabbitmq prefix in the name,
// owned by exactly one RabbitmqCluster.
pub open spec fn rmq_guarantee_create_req(req: CreateRequest) -> bool {
    &&& is_rmq_managed_kind(req.obj.kind)
    &&& req.obj.metadata.name is Some
    &&& req.obj.metadata.owner_references is Some
    &&& exists |rabbitmq: RabbitmqClusterView|
        req.obj.metadata.owner_references->0 == seq![#[trigger] rabbitmq.controller_owner_ref()]
}

// RMQ only updates objects of rmq-managed kind with rabbitmq prefix in the name,
// owned by exactly one RabbitmqCluster.
pub open spec fn rmq_guarantee_update_req(req: UpdateRequest) -> bool {
    &&& is_rmq_managed_kind(req.obj.kind)
    &&& req.obj.metadata.owner_references is Some
    &&& exists |rabbitmq: RabbitmqClusterView|
        req.obj.metadata.owner_references->0 == seq![#[trigger] rabbitmq.controller_owner_ref()]
}

pub open spec fn rmq_guarantee(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::GetRequest(_) => true,
            APIRequest::CreateRequest(req) => rmq_guarantee_create_req(req),
            APIRequest::UpdateRequest(req) => rmq_guarantee_update_req(req),
            _ => false, // rmq doesn't send other requests
        }
    }
}

}
