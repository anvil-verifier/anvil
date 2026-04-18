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
                APIRequest::CreateRequest(req) => rmq_rely_create_req(req),
                APIRequest::UpdateRequest(req) => rmq_rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) => rmq_rely_get_then_update_req(req)(s),
                APIRequest::DeleteRequest(req) => rmq_rely_delete_req(req)(s),
                APIRequest::GetThenDeleteRequest(req) => rmq_rely_get_then_delete_req(req)(s),
                APIRequest::UpdateStatusRequest(req) => rmq_rely_update_status_req(req)(s),
                APIRequest::GetThenUpdateStatusRequest(req) => rmq_rely_get_then_update_status_req(req)(s),
                // Get/List requests do not interfere
                _ => true,
            }
        }
    }
}

// Helper to check if a kind is managed by the RMQ controller
pub open spec fn is_rmq_managed_kind(kind: Kind) -> bool {
    ||| kind == Kind::ServiceKind
    ||| kind == Kind::SecretKind
    ||| kind == Kind::ConfigMapKind
    ||| kind == Kind::ServiceAccountKind
    ||| kind == Kind::RoleKind
    ||| kind == Kind::RoleBindingKind
    ||| kind == VStatefulSetView::kind()
}

pub open spec fn has_rmq_name_prefix(name: StringView) -> bool {
    exists |suffix| name == RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + suffix
}

pub open spec fn rmq_rely_create_req(req: CreateRequest) -> bool {
    is_rmq_managed_kind(req.obj.kind) ==> {
        &&& req.obj.metadata.name is Some ==> !has_rmq_name_prefix(req.obj.metadata.name->0)
        &&& req.obj.metadata.name is None && req.obj.metadata.generate_name is Some ==> !has_rmq_name_prefix(req.obj.metadata.generate_name->0)
    }
}

pub open spec fn rmq_rely_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key()];
        &&& is_rmq_managed_kind(req.obj.kind) && has_rmq_name_prefix(req.name) && s.resources().contains_key(req.key()) ==> { // if req could interfere
            req.obj.metadata.resource_version is Some
            && etcd_obj.metadata.resource_version is Some
            && etcd_obj.metadata.resource_version == req.obj.metadata.resource_version // if req could succeed
                ==> !exists |rmq: RabbitmqClusterView| #[trigger] etcd_obj.metadata.owner_references_contains(rmq.controller_owner_ref()) // then it should not touch objects owned by rmq
        }
    }
}

pub open spec fn rmq_rely_get_then_update_req(req: GetThenUpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& is_rmq_managed_kind(req.obj.kind) && has_rmq_name_prefix(req.name) && s.resources().contains_key(req.key()) // if req could interfere
            ==> req.owner_ref.controller == Some(true) // if req could succeed
                ==> req.owner_ref.kind != RabbitmqClusterView::kind() // then it should not touch objects owned by rmq
    }
}

pub open spec fn rmq_rely_update_status_req(req: UpdateStatusRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key()];
        &&& is_rmq_managed_kind(req.obj.kind) && has_rmq_name_prefix(req.name) && s.resources().contains_key(req.key()) ==> {
            req.obj.metadata.resource_version is Some
            && etcd_obj.metadata.resource_version is Some
            && etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
                ==> !exists |rmq: RabbitmqClusterView| #[trigger] etcd_obj.metadata.owner_references_contains(rmq.controller_owner_ref())
        }
    }
}

pub open spec fn rmq_rely_get_then_update_status_req(req: GetThenUpdateStatusRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& is_rmq_managed_kind(req.obj.kind) && has_rmq_name_prefix(req.name) && s.resources().contains_key(req.key()) // if req could interfere
            ==> req.owner_ref.controller == Some(true) // if req could succeed
                ==> req.owner_ref.kind != RabbitmqClusterView::kind() // then it should not touch objects owned by rmq
    }
}

pub open spec fn rmq_rely_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key()];
        &&& is_rmq_managed_kind(req.key().kind) && has_rmq_name_prefix(req.key.name) && s.resources().contains_key(req.key()) // if req could interfere
            ==> req.preconditions is Some
            && req.preconditions->0.resource_version is Some
            && etcd_obj.metadata.resource_version is Some
            && etcd_obj.metadata.resource_version == req.preconditions->0.resource_version // if req could succeed
                ==> !exists |rmq: RabbitmqClusterView| #[trigger] etcd_obj.metadata.owner_references_contains(rmq.controller_owner_ref()) // then it should not touch objects owned by rmq
    }
}

pub open spec fn rmq_rely_get_then_delete_req(req: GetThenDeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& is_rmq_managed_kind(req.key().kind) && has_rmq_name_prefix(req.key.name) && s.resources().contains_key(req.key()) // if req could interfere
            ==> req.owner_ref.controller == Some(true) // if req could succeed
                ==> req.owner_ref.kind != RabbitmqClusterView::kind() // then it should not touch objects owned by rmq
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
