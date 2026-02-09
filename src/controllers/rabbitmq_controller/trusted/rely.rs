use crate::kubernetes_api_objects::spec::{prelude::*, persistent_volume_claim::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::kubernetes_cluster::spec::api_server::{state_machine::*, types::InstalledTypes};
use crate::rabbitmq_controller::{
    trusted::spec_types::*,
    model::reconciler::*,
    proof::predicate::*
};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub open spec fn rmq_rely_conditions(cluster: Cluster, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] rmq_rely(other_id, cluster.installed_types)(s)
    }
}

pub open spec fn rmq_rely(other_id: int, installed_types: InstalledTypes) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(other_id)
        } ==> {
            match (msg.content->APIRequest_0) {
                APIRequest::CreateRequest(req) => rely_create_req(req),
                APIRequest::UpdateRequest(req) => rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) => rely_get_then_update_req(req),
                APIRequest::DeleteRequest(req) => rely_delete_req(req)(s),
                APIRequest::GetThenDeleteRequest(req) => rely_get_then_delete_req(req),
                // Get/List requests do not interfere
                _ => true,
            }
        }
    }
}

// Helper to check if a kind is managed by the RMQ controller
pub open spec fn is_rmq_managed_kind(kind: Kind) -> bool {
    match kind {
        Kind::ServiceKind => true,
        Kind::SecretKind => true,
        Kind::ConfigMapKind => true,
        Kind::ServiceAccountKind => true,
        Kind::RoleKind => true,
        Kind::RoleBindingKind => true,
        Kind::StatefulSetKind => true,
        _ => false,
    }
}

// Other controllers don't create objects owned by a RabbitmqCluster
// and should not create objects with "rabbitmq-" prefix
pub open spec fn rely_create_req(req: CreateRequest) -> bool {
    is_rmq_managed_kind(req.obj.kind) ==> {
        // Prevents 1): where other controllers create objects owned by RMQ
        &&& !exists |rmq: RabbitmqClusterView| #[trigger] req.obj.metadata.owner_references_contains(rmq.controller_owner_ref())
        // Prevents 2): where other controllers create objects with name collision potential
        &&& !{
            if req.obj.metadata.name is Some {
                has_rabbitmq_prefix(req.obj.metadata.name->0)
            } else {
                &&& req.obj.metadata.generate_name is Some
                &&& has_rabbitmq_prefix(req.obj.metadata.generate_name->0)
            }
        }
    }
}

// Other controllers don't update objects owned by a RabbitmqCluster
pub open spec fn rely_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        is_rmq_managed_kind(req.obj.kind) ==> {
            // Prevents 1): where other controllers update objects already owned by a RabbitmqCluster
            &&& !{
                let etcd_obj = s.resources()[req.key()];
                &&& exists |rmq: RabbitmqClusterView|
                    #[trigger] etcd_obj.metadata.owner_references_contains(rmq.controller_owner_ref())
            }
            // Prevents 2): where other controllers update objects so they become owned by a RabbitmqCluster
            &&& !exists |rmq: RabbitmqClusterView| #[trigger] req.obj.metadata.owner_references_contains(rmq.controller_owner_ref())
        }
    }
}

// Other controllers don't update objects owned by a RabbitmqCluster
pub open spec fn rely_get_then_update_req(req: GetThenUpdateRequest) -> bool {
    is_rmq_managed_kind(req.obj.kind) ==> {
        // Prevents 1): where other controllers update objects owned by a RabbitmqCluster
        &&& req.owner_ref.kind != RabbitmqClusterView::kind()
        // Prevents 2): where other controllers update objects so they become owned by a RabbitmqCluster
        &&& !exists |rmq: RabbitmqClusterView| #[trigger] req.obj.metadata.owner_references_contains(rmq.controller_owner_ref())
    }
}

// Other controllers don't delete objects owned by a RabbitmqCluster
pub open spec fn rely_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        is_rmq_managed_kind(req.key.kind) ==> {
            // that object does not belong to any RabbitmqCluster
            !{
                let etcd_obj = s.resources()[req.key];
                &&& exists |rmq: RabbitmqClusterView|
                    #[trigger] etcd_obj.metadata.owner_references_contains(rmq.controller_owner_ref())
            }
        }
    }
}

// Other controllers don't conditionally delete objects owned by a RabbitmqCluster
pub open spec fn rely_get_then_delete_req(req: GetThenDeleteRequest) -> bool {
    is_rmq_managed_kind(req.key.kind) ==> {
        req.owner_ref.kind != RabbitmqClusterView::kind()
    }
}

}
