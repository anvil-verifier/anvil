use crate::kubernetes_api_objects::spec::{persistent_volume_claim::*, prelude::*};
use crate::kubernetes_cluster::spec::api_server::{state_machine::*, types::InstalledTypes};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::rabbitmq_controller::{
    model::reconciler::*, proof::predicate::*, trusted::spec_types::*,
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
                APIRequest::GetThenUpdateRequest(req) => rely_get_then_update_req(req)(s),
                APIRequest::DeleteRequest(req) => rely_delete_req(req)(s),
                APIRequest::GetThenDeleteRequest(req) => rely_get_then_delete_req(req)(s),
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

// should not create objects with "rabbitmq-" prefix
pub open spec fn rely_create_req(req: CreateRequest) -> bool {
    is_rmq_managed_kind(req.obj.kind) ==> {
        !{
            if req.obj.metadata.name is Some {
                has_rabbitmq_prefix(req.obj.metadata.name->0)
            } else {
                &&& req.obj.metadata.generate_name is Some
                &&& has_rabbitmq_prefix(req.obj.metadata.generate_name->0)
            }
        }
    }
}

// Other controllers don't update objects with rabbitmq prefix
pub open spec fn rely_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        is_rmq_managed_kind(req.obj.kind) ==> {
            !{
                let etcd_obj = s.resources()[req.key()];
                has_rabbitmq_prefix(etcd_obj.metadata.name->0)
            }
        }
    }
}

pub open spec fn rely_get_then_update_req(req: GetThenUpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        is_rmq_managed_kind(req.obj.kind) ==> {
            !{
                let etcd_obj = s.resources()[req.key()];
                has_rabbitmq_prefix(etcd_obj.metadata.name->0)
            }
        }
    }
}

pub open spec fn rely_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        is_rmq_managed_kind(req.key.kind) ==> {
            !{
                let etcd_obj = s.resources()[req.key];
                has_rabbitmq_prefix(etcd_obj.metadata.name->0)
            }
        }
    }
}

pub open spec fn rely_get_then_delete_req(req: GetThenDeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        is_rmq_managed_kind(req.key.kind) ==> {
            !{
                let etcd_obj = s.resources()[req.key];
                has_rabbitmq_prefix(etcd_obj.metadata.name->0)
            }
        }
    }
}

}
