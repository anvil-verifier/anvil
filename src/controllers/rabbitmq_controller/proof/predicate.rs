// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, prelude::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep, ReconcileLocalState},
    message::*,
};
use crate::rabbitmq_controller::model::{reconciler::*, resource::*};
use crate::rabbitmq_controller::proof::{resource::*, helper_invariants::*};
use crate::rabbitmq_controller::trusted::{
    spec_types::*, step::*, liveness_theorem::*,
};
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub open spec fn at_rabbitmq_step(key: ObjectRef, controller_id: int, step: RabbitmqReconcileStep) -> StatePred<ClusterState>
    recommends
        key.kind is CustomResourceKind
{
    |s: ClusterState| {
        let local_state = s.ongoing_reconciles(controller_id)[key].local_state;
        let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
        &&& s.ongoing_reconciles(controller_id).contains_key(key)
        &&& unmarshalled_state.reconcile_step == step
    }
}

pub open spec fn at_rabbitmq_step_with_rabbitmq(rabbitmq: RabbitmqClusterView, controller_id: int, step: RabbitmqReconcileStep) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = rabbitmq.object_ref();
        let triggering_cr = RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
        let local_state = s.ongoing_reconciles(controller_id)[key].local_state;
        let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
        &&& s.ongoing_reconciles(controller_id).contains_key(key)
        &&& RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).is_ok()
        &&& RabbitmqReconcileState::unmarshal(local_state).is_ok()
        &&& triggering_cr.object_ref() == rabbitmq.object_ref()
        &&& triggering_cr.spec() == rabbitmq.spec()
        &&& triggering_cr.metadata().uid == rabbitmq.metadata().uid
        &&& unmarshalled_state.reconcile_step == step
    }
}

pub open spec fn no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq: RabbitmqClusterView, controller_id: int, step: RabbitmqReconcileStep) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::no_pending_req_msg(controller_id, s, rabbitmq.object_ref())
    }
}

pub open spec fn at_step_closure(step: RabbitmqReconcileStep) -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
        let state = RabbitmqReconcileState::unmarshal(s).unwrap();
        state.reconcile_step == step
    }
}

pub open spec fn after_get_k_request_step(sub_resource: SubResource) -> RabbitmqReconcileStep {
    RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource)
}

pub open spec fn after_create_k_request_step(sub_resource: SubResource) -> RabbitmqReconcileStep {
    RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource)
}

pub open spec fn after_update_k_request_step(sub_resource: SubResource) -> RabbitmqReconcileStep {
    RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource)
}

pub open spec fn next_resource_after(sub_resource: SubResource) -> RabbitmqReconcileStep {
    match sub_resource {
        SubResource::HeadlessService => after_get_k_request_step(SubResource::Service),
        SubResource::Service => after_get_k_request_step(SubResource::ErlangCookieSecret),
        SubResource::ErlangCookieSecret => after_get_k_request_step(SubResource::DefaultUserSecret),
        SubResource::DefaultUserSecret => after_get_k_request_step(SubResource::PluginsConfigMap),
        SubResource::PluginsConfigMap => after_get_k_request_step(SubResource::ServerConfigMap),
        SubResource::ServerConfigMap => after_get_k_request_step(SubResource::ServiceAccount),
        SubResource::ServiceAccount => after_get_k_request_step(SubResource::Role),
        SubResource::Role => after_get_k_request_step(SubResource::RoleBinding),
        SubResource::RoleBinding => after_get_k_request_step(SubResource::VStatefulSetView),
        _ => RabbitmqReconcileStep::Done,
    }
}

pub open spec fn pending_req_in_flight_at_after_get_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let request = msg.content->APIRequest_0;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& msg.dst == HostId::APIServer
        &&& msg.content is APIRequest
        &&& request is GetRequest
        &&& request->GetRequest_0 == get_request(sub_resource, rabbitmq)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_get_k_request_step(sub_resource);
        let request = req_msg.content->APIRequest_0;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content is APIRequest
        &&& request is GetRequest
        &&& request->GetRequest_0 == get_request(sub_resource, rabbitmq)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, controller_id, req_msg)(s)
    }
}

pub open spec fn at_after_get_resource_step_and_exists_not_found_resp_in_flight(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let request = msg.content->APIRequest_0;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& msg.dst == HostId::APIServer
        &&& msg.content is APIRequest
        &&& request is GetRequest
        &&& request->GetRequest_0 == get_request(sub_resource, rabbitmq)
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_response().res is Err
            &&& resp_msg.content.get_get_response().res->Err_0 is ObjectNotFound
        }
    }
}

pub open spec fn at_after_get_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let request = msg.content->APIRequest_0;
        let key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& msg.dst == HostId::APIServer
        &&& msg.content is APIRequest
        &&& request is GetRequest
        &&& request->GetRequest_0 == get_request(sub_resource, rabbitmq)
        &&& s.resources().contains_key(key)
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_response().res is Ok
            &&& resp_msg.content.get_get_response().res->Ok_0 == s.resources()[key]
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let request = msg.content->APIRequest_0;
        let key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& msg.dst == HostId::APIServer
        &&& msg.content is APIRequest
        &&& request is GetRequest
        &&& request->GetRequest_0 == get_request(sub_resource, rabbitmq)
        &&& s.resources().contains_key(key)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_get_response().res is Ok
        &&& resp_msg.content.get_get_response().res->Ok_0 == s.resources()[key]
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_after_get_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let request = msg.content->APIRequest_0;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& msg.dst == HostId::APIServer
        &&& msg.content is APIRequest
        &&& request is GetRequest
        &&& request->GetRequest_0 == get_request(sub_resource, rabbitmq)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
    }
}

pub open spec fn req_obj_matches_sub_resource_requirements(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, obj: DynamicObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
        &&& match sub_resource {
            SubResource::HeadlessService => {
                &&& ServiceView::unmarshal(obj) is Ok
                &&& ServiceView::unmarshal(obj)->Ok_0.state_validation()
                &&& ServiceView::unmarshal(obj)->Ok_0.spec is Some
                &&& ServiceView::unmarshal(obj)->Ok_0.spec->0.without_cluster_ip() == make_headless_service(rabbitmq).spec->0.without_cluster_ip()
                &&& obj.metadata.labels == make_headless_service(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_headless_service(rabbitmq).metadata.annotations
            },
            SubResource::Service => {
                &&& ServiceView::unmarshal(obj) is Ok
                &&& ServiceView::unmarshal(obj)->Ok_0.state_validation()
                &&& ServiceView::unmarshal(obj)->Ok_0.spec is Some
                &&& ServiceView::unmarshal(obj)->Ok_0.spec->0.without_cluster_ip() == make_main_service(rabbitmq).spec->0.without_cluster_ip()
                &&& obj.metadata.labels == make_main_service(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_main_service(rabbitmq).metadata.annotations
            },
            SubResource::ErlangCookieSecret => {
                &&& SecretView::unmarshal(obj) is Ok
                &&& SecretView::unmarshal(obj)->Ok_0.state_validation()
                &&& SecretView::unmarshal(obj)->Ok_0.data == make_erlang_secret(rabbitmq).data
                &&& obj.metadata.labels == make_erlang_secret(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_erlang_secret(rabbitmq).metadata.annotations
            },
            SubResource::DefaultUserSecret => {
                &&& SecretView::unmarshal(obj) is Ok
                &&& SecretView::unmarshal(obj)->Ok_0.state_validation()
                &&& SecretView::unmarshal(obj)->Ok_0.data == make_default_user_secret(rabbitmq).data
                &&& obj.metadata.labels == make_default_user_secret(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_default_user_secret(rabbitmq).metadata.annotations
            },
            SubResource::PluginsConfigMap => {
                &&& ConfigMapView::unmarshal(obj) is Ok
                &&& ConfigMapView::unmarshal(obj)->Ok_0.state_validation()
                &&& ConfigMapView::unmarshal(obj)->Ok_0.data == make_plugins_config_map(rabbitmq).data
                &&& obj.metadata.labels == make_plugins_config_map(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_plugins_config_map(rabbitmq).metadata.annotations
            },
            SubResource::ServerConfigMap => {
                &&& ConfigMapView::unmarshal(obj) is Ok
                &&& ConfigMapView::unmarshal(obj)->Ok_0.state_validation()
                &&& ConfigMapView::unmarshal(obj)->Ok_0.data == make_server_config_map(rabbitmq).data
                &&& obj.metadata.labels == make_server_config_map(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_server_config_map(rabbitmq).metadata.annotations
            },
            SubResource::ServiceAccount => {
                &&& ServiceAccountView::unmarshal(obj) is Ok
                &&& ServiceAccountView::unmarshal(obj)->Ok_0.state_validation()
                &&& ServiceAccountView::unmarshal(obj)->Ok_0.automount_service_account_token == make_service_account(rabbitmq).automount_service_account_token
                &&& ServiceAccountView::unmarshal(obj)->Ok_0.metadata.labels == make_service_account(rabbitmq).metadata.labels
                &&& ServiceAccountView::unmarshal(obj)->Ok_0.metadata.annotations == make_service_account(rabbitmq).metadata.annotations
            },
            SubResource::Role => {
                &&& RoleView::unmarshal(obj) is Ok
                &&& RoleView::unmarshal(obj)->Ok_0.state_validation()
                &&& RoleView::unmarshal(obj)->Ok_0.policy_rules == make_role(rabbitmq).policy_rules
                &&& obj.metadata.labels == make_role(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_role(rabbitmq).metadata.annotations
            },
            SubResource::RoleBinding => {
                &&& RoleBindingView::unmarshal(obj) is Ok
                &&& RoleBindingView::unmarshal(obj)->Ok_0.state_validation()
                &&& RoleBindingView::unmarshal(obj)->Ok_0.role_ref == make_role_binding(rabbitmq).role_ref
                &&& RoleBindingView::unmarshal(obj)->Ok_0.subjects == make_role_binding(rabbitmq).subjects
                &&& obj.metadata.labels == make_role_binding(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_role_binding(rabbitmq).metadata.annotations
            },
            SubResource::VStatefulSetView => {
                let cm_key = make_server_config_map_key(rabbitmq);
                let cm_obj = s.resources()[cm_key];
                let made_sts = make_stateful_set(rabbitmq, int_to_string_view(cm_obj.metadata.resource_version->0));
                let req_obj_spec = VStatefulSetView::unmarshal(obj)->Ok_0.spec;
                &&& VStatefulSetView::unmarshal(obj) is Ok
                &&& VStatefulSetView::unmarshal(obj)->Ok_0.state_validation()
                &&& obj.metadata.labels == made_sts.metadata.labels
                &&& obj.metadata.annotations == made_sts.metadata.annotations
                &&& req_obj_spec.replicas == Some(rabbitmq.spec.replicas)
                &&& req_obj_spec.template == made_sts.spec.template
                &&& req_obj_spec.persistent_volume_claim_retention_policy == rabbitmq.spec.persistent_volume_claim_retention_policy
            },
        }
    }
}

pub open spec fn pending_req_in_flight_at_after_create_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let req = msg.content.get_create_request();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
        &&& req_obj_matches_sub_resource_requirements(sub_resource, rabbitmq, msg.content.get_create_request().obj)(s)
        // sanity check
        &&& !s.resources().contains_key(req.key())
        &&& req.obj.metadata.name is Some
        &&& req.obj.metadata.generate_name is None
        &&& req.obj.metadata.namespace is Some
        &&& req.namespace == req.obj.metadata.namespace->0
        &&& req.obj.metadata.deletion_timestamp is None
        &&& req.obj.metadata.finalizers is None
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_create_k_request_step(sub_resource);
        let req = req_msg.content.get_create_request();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(req_msg)
        &&& req_obj_matches_sub_resource_requirements(sub_resource, rabbitmq, req_msg.content.get_create_request().obj)(s)
        // sanity check
        &&& !s.resources().contains_key(req.key())
        &&& req.obj.metadata.name is Some
        &&& req.obj.metadata.generate_name is None
        &&& req.obj.metadata.namespace is Some
        &&& req.namespace == req.obj.metadata.namespace->0
        &&& req.obj.metadata.deletion_timestamp is None
        &&& req.obj.metadata.finalizers is None
    }
}

pub open spec fn at_after_create_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let request = msg.content->APIRequest_0;
        let key = get_request(sub_resource, rabbitmq).key;
        let local_state = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state;
        let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_create_request_msg(key)(msg)
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_create_response().res is Ok
            &&& state_after_create(sub_resource, rabbitmq, resp_msg.content.get_create_response().res->Ok_0, unmarshalled_state) is Ok
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let request = msg.content->APIRequest_0;
        let key = get_request(sub_resource, rabbitmq).key;
        let local_state = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state;
        let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_create_request_msg(key)(msg)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_create_response().res is Ok
        &&& state_after_create(sub_resource, rabbitmq, resp_msg.content.get_create_response().res->Ok_0, unmarshalled_state) is Ok
    }
}

pub open spec fn pending_req_in_flight_at_after_update_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let req = msg.content.get_update_request();
        let resource_key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_update_request_msg(resource_key)(msg)
        &&& s.resources().contains_key(resource_key)
        &&& msg.content.get_update_request().obj.metadata.resource_version is Some
        &&& msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
        &&& req_obj_matches_sub_resource_requirements(sub_resource, rabbitmq, msg.content.get_update_request().obj)(s)
        // sanity check
        &&& req.obj.metadata.name is Some
        &&& req.name == req.obj.metadata.name->0
        &&& req.obj.metadata.namespace is Some
        &&& req.namespace == req.obj.metadata.namespace->0
        &&& req.obj.metadata.uid is Some
        &&& req.obj.metadata.deletion_timestamp is None
        &&& req.obj.metadata.finalizers is None
        &&& s.resources()[resource_key].metadata.uid->0 == req.obj.metadata.uid->0
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_update_k_request_step(sub_resource);
        let resource_key = get_request(sub_resource, rabbitmq).key;
        let req = req_msg.content.get_update_request();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(req_msg)
        &&& s.resources().contains_key(resource_key)
        &&& req_msg.content.get_update_request().obj.metadata.resource_version is Some
        &&& req_msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
        &&& req_obj_matches_sub_resource_requirements(sub_resource, rabbitmq, req_msg.content.get_update_request().obj)(s)
        // sanity check
        &&& req.obj.metadata.name is Some
        &&& req.name == req.obj.metadata.name->0
        &&& req.obj.metadata.namespace is Some
        &&& req.namespace == req.obj.metadata.namespace->0
        &&& req.obj.metadata.uid is Some
        &&& req.obj.metadata.deletion_timestamp is None
        &&& req.obj.metadata.finalizers is None
        &&& s.resources()[resource_key].metadata.uid->0 == req.obj.metadata.uid->0
    }
}

pub open spec fn at_after_update_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let request = msg.content->APIRequest_0;
        let key = get_request(sub_resource, rabbitmq).key;
        let local_state = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state;
        let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_update_request_msg(key)(msg)
        &&& exists |resp_msg: Message| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_update_response().res is Ok
            &&& state_after_update(sub_resource, rabbitmq, resp_msg.content.get_update_response().res->Ok_0, unmarshalled_state) is Ok
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        let request = msg.content->APIRequest_0;
        let key = get_request(sub_resource, rabbitmq).key;
        let local_state = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state;
        let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_update_request_msg(key)(msg)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_update_response().res is Ok
        &&& state_after_update(sub_resource, rabbitmq, resp_msg.content.get_update_response().res->Ok_0, unmarshalled_state) is Ok
    }
}

pub open spec fn cluster_invariants_since_reconciliation(cluster: Cluster, controller_id: int, rmq: RabbitmqClusterView, sub_resource: SubResource) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::etcd_objects_have_unique_uids()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::cr_objects_in_schedule_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)(s)
        &&& Cluster::ongoing_reconciles_is_finite(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rmq.object_ref())(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::no_pending_request_to_api_server_from_non_controllers()(s)
        &&& Cluster::desired_state_is(rmq)(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, rmq.object_ref())(s)
        // &&& every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rmq)(s)
        &&& no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rmq)(s)
        &&& no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rmq)(s)
        &&& object_in_etcd_satisfies_unchangeable(sub_resource, rmq)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rmq)(s)
        &&& cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rmq)(s)
        &&& resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rmq)(s)
        &&& sts_in_etcd_with_rmq_key_match_rmq_selector_and_owner(rmq)(s)
    }
}

}
