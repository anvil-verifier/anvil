use crate::kubernetes_api_objects::spec::{persistent_volume_claim::*, prelude::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::rabbitmq_controller::{
    model::{install::rabbitmq_controller_model, reconciler::*, resource::*},
    proof::predicate::*,
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

pub open spec fn rmq_rely(other_id: int) -> StatePred<ClusterState> {
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
                APIRequest::UpdateStatusRequest(req) => rely_update_status_req(req)(s),
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

// should not create objects with "rabbitmq-" prefix
pub open spec fn rely_create_req(req: CreateRequest) -> bool {
    is_rmq_managed_kind(req.obj.kind) ==> {
        if req.obj.metadata.name is Some {
            !has_rabbitmq_prefix(req.obj.metadata.name->0)
        } else {
            !(req.obj.metadata.generate_name is Some && has_rabbitmq_prefix(req.obj.metadata.generate_name->0))
        }
    }
}

// Other controllers don't update objects with rabbitmq prefix
pub open spec fn rely_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        is_rmq_managed_kind(req.obj.kind) ==> !has_rabbitmq_prefix(req.key().name)
    }
}

pub open spec fn rely_get_then_update_req(req: GetThenUpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        is_rmq_managed_kind(req.obj.kind) ==> !has_rabbitmq_prefix(req.key().name)
    }
}

pub open spec fn rely_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        is_rmq_managed_kind(req.key.kind) ==> !has_rabbitmq_prefix(req.key().name)
    }
}

pub open spec fn rely_get_then_delete_req(req: GetThenDeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        is_rmq_managed_kind(req.key.kind) ==> !has_rabbitmq_prefix(req.key().name)
    }
}

pub open spec fn rely_update_status_req(req: UpdateStatusRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        is_rmq_managed_kind(req.obj.kind) ==> !has_rabbitmq_prefix(req.key().name)
    }
}

// RMQ only creates objects of rmq-managed kind with rabbitmq prefix in the name,
// owned by exactly one RabbitmqCluster.
pub open spec fn rmq_guarantee_create_req(req: CreateRequest) -> bool {
    &&& is_rmq_managed_kind(req.obj.kind)
    &&& req.obj.metadata.name is Some
    &&& has_rabbitmq_prefix(req.obj.metadata.name->0)
    &&& req.obj.metadata.owner_references is Some
    &&& exists |rabbitmq: RabbitmqClusterView|
        req.obj.metadata.owner_references->0 == seq![#[trigger] rabbitmq.controller_owner_ref()]
}

// RMQ only updates objects of rmq-managed kind with rabbitmq prefix in the name,
// owned by exactly one RabbitmqCluster.
pub open spec fn rmq_guarantee_update_req(req: UpdateRequest) -> bool {
    &&& is_rmq_managed_kind(req.obj.kind)
    &&& has_rabbitmq_prefix(req.key().name)
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

pub proof fn guarantee_condition_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(always(lift_state(rmq_guarantee(controller_id))))
{
}

// internal rely-guarantee
pub open spec fn no_interfering_request_between_rmq(controller_id: int, sub_resource: SubResource, other_rmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src == HostId::Controller(controller_id, other_rmq.object_ref())
        } ==> match msg.content->APIRequest_0 {
            APIRequest::GetRequest(_) => true,
            APIRequest::CreateRequest(_) | APIRequest::UpdateRequest(_)=> {
                let key = if msg.content.is_create_request() {
                    msg.content.get_create_request().key()
                } else {
                    msg.content.get_update_request().key()
                };
                &&& rmq_requests_carry_rmq_key(key, sub_resource, other_rmq)
            }
            _ => false
        }
    }
}

pub open spec fn rmq_requests_carry_rmq_key(req_key: ObjectRef, sub_resource: SubResource, other_rmq: RabbitmqClusterView) -> bool {
    match sub_resource {
        SubResource::HeadlessService => req_key == make_headless_service_key(other_rmq),
        SubResource::Service => req_key == make_main_service_key(other_rmq),
        SubResource::ErlangCookieSecret => req_key == make_erlang_secret_key(other_rmq),
        SubResource::DefaultUserSecret => req_key == make_default_user_secret_key(other_rmq),
        SubResource::PluginsConfigMap => req_key == make_plugins_config_map_key(other_rmq),
        SubResource::ServerConfigMap => req_key == make_server_config_map_key(other_rmq),
        SubResource::ServiceAccount => req_key == make_service_account_key(other_rmq),
        SubResource::Role => req_key == make_role_key(other_rmq),
        SubResource::RoleBinding => req_key == make_role_binding_key(other_rmq),
        SubResource::VStatefulSetView => req_key == make_stateful_set_key(other_rmq),
        _ => false,
    }
}


}
