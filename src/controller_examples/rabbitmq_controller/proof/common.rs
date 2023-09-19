// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::proof::controller_runtime::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::{reconciler::*, types::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub type RMQStep = Step<RMQMessage>;

pub type RMQCluster = Cluster<RabbitmqClusterView, EmptyAPI, RabbitmqReconciler>;

pub type RMQMessage = Message<EmptyTypeView, EmptyTypeView>;

pub open spec fn cluster_spec() -> TempPred<RMQCluster> {
    RMQCluster::sm_spec()
}

pub open spec fn at_rabbitmq_step(key: ObjectRef, step: RabbitmqReconcileStep) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: RMQCluster| {
        &&& s.ongoing_reconciles().contains_key(key)
        &&& s.ongoing_reconciles()[key].local_state.reconcile_step == step
    }
}

pub open spec fn at_step_closure(step: RabbitmqReconcileStep) -> FnSpec(RabbitmqReconcileState) -> bool {
    |s: RabbitmqReconcileState| s.reconcile_step == step
}

pub open spec fn at_rabbitmq_step_with_rabbitmq(rabbitmq: RabbitmqClusterView, step: RabbitmqReconcileStep) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& s.ongoing_reconciles().contains_key(rabbitmq.object_ref())
        &&& s.ongoing_reconciles()[rabbitmq.object_ref()].triggering_cr.object_ref() == rabbitmq.object_ref()
        &&& s.ongoing_reconciles()[rabbitmq.object_ref()].triggering_cr.spec() == rabbitmq.spec()
        &&& s.ongoing_reconciles()[rabbitmq.object_ref()].triggering_cr.metadata().uid == rabbitmq.metadata().uid
        &&& s.ongoing_reconciles()[rabbitmq.object_ref()].local_state.reconcile_step == step
    }
}

pub open spec fn no_pending_req_at_rabbitmq_step_with_rabbitmq(rabbitmq: RabbitmqClusterView, step: RabbitmqReconcileStep) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::no_pending_req_msg_or_external_api_input(s, rabbitmq.object_ref())
    }
}

pub open spec fn pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(
    step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& s.in_flight().contains(s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
        &&& is_correct_pending_request_msg_at_rabbitmq_step(step, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq)
    }
}

pub open spec fn pending_req_with_object_in_flight_at_rabbitmq_step_with_rabbitmq(
    step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, object: DynamicObjectView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& s.in_flight().contains(s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
        &&& is_correct_pending_request_msg_with_object_at_rabbitmq_step(step, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq, object)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(
    step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg_is(s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& is_correct_pending_request_msg_at_rabbitmq_step(step, req_msg, rabbitmq)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_with_object_at_rabbitmq_step_with_rabbitmq(
    step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage, object: DynamicObjectView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg_is(s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& is_correct_pending_request_msg_with_object_at_rabbitmq_step(step, req_msg, rabbitmq, object)
    }
}

pub open spec fn exists_resp_in_flight_at_rabbitmq_step_with_rabbitmq(
    step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& is_correct_pending_request_msg_at_rabbitmq_step(step, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(
    step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, resp_msg: RMQMessage
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& is_correct_pending_request_msg_at_rabbitmq_step(step, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
    }
}

pub open spec fn is_correct_pending_request_msg_at_rabbitmq_step(
    step: RabbitmqReconcileStep, msg: RMQMessage, rabbitmq: RabbitmqClusterView
) -> bool {
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_APIRequest()
    &&& is_correct_pending_request_at_rabbitmq_step(step, msg.content.get_APIRequest_0(), rabbitmq)
}

pub open spec fn is_correct_pending_request_at_rabbitmq_step(
    step: RabbitmqReconcileStep, request: APIRequest, rabbitmq: RabbitmqClusterView
) -> bool {
    match step {
        RabbitmqReconcileStep::AfterCreateHeadlessService => is_create_headless_service_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterCreateService => is_create_service_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterCreateErlangCookieSecret => is_create_erlang_secret_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterCreateDefaultUserSecret => is_create_default_user_secret_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterCreatePluginsConfigMap => is_create_plugins_config_map_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterGetServerConfigMap => is_get_server_config_map_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterCreateServerConfigMap => is_create_server_config_map_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterCreateServiceAccount => is_create_service_account_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterCreateRole => is_create_role_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterCreateRoleBinding => is_create_role_binding_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterGetStatefulSet => is_get_stateful_set_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterCreateStatefulSet => is_create_stateful_set_request(request, rabbitmq),
        RabbitmqReconcileStep::AfterUpdateServerConfigMap => true,
        RabbitmqReconcileStep::AfterUpdateStatefulSet => true,
        _ => false
    }
}

pub open spec fn is_correct_pending_request_msg_with_object_at_rabbitmq_step(
    step: RabbitmqReconcileStep, msg: RMQMessage, rabbitmq: RabbitmqClusterView, object: DynamicObjectView
) -> bool {
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_APIRequest()
    &&& is_correct_pending_request_with_object_at_rabbitmq_step(step, msg.content.get_APIRequest_0(), rabbitmq, object)
}

pub open spec fn is_correct_pending_request_with_object_at_rabbitmq_step(
    step: RabbitmqReconcileStep, request: APIRequest, rabbitmq: RabbitmqClusterView, object: DynamicObjectView
) -> bool {
    match step {
        RabbitmqReconcileStep::AfterUpdateServerConfigMap => is_update_server_config_map_request(request, rabbitmq, object),
        RabbitmqReconcileStep::AfterUpdateStatefulSet => is_update_stateful_set_request(request, rabbitmq, object),
        _ => false
    }
}

pub open spec fn is_create_headless_service_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_headless_service(rabbitmq).marshal()
}

pub open spec fn is_create_service_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_main_service(rabbitmq).marshal()
}

pub open spec fn is_create_erlang_secret_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_erlang_secret(rabbitmq).marshal()
}

pub open spec fn is_create_default_user_secret_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_default_user_secret(rabbitmq).marshal()
}

pub open spec fn is_create_plugins_config_map_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_plugins_config_map(rabbitmq).marshal()
}

pub open spec fn is_create_server_config_map_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_server_config_map(rabbitmq).marshal()
}

pub open spec fn is_create_service_account_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_service_account(rabbitmq).marshal()
}

pub open spec fn is_create_role_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_role(rabbitmq).marshal()
}

pub open spec fn is_create_role_binding_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_role_binding(rabbitmq).marshal()
}

pub open spec fn is_create_stateful_set_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_stateful_set(rabbitmq).marshal()
}

pub open spec fn is_get_server_config_map_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool
    recommends
        rabbitmq.well_formed(),
{
    &&& request.is_GetRequest()
    &&& request.get_GetRequest_0().key == make_server_config_map_key(rabbitmq.object_ref())
}

pub open spec fn is_update_stateful_set_request(request: APIRequest, rabbitmq: RabbitmqClusterView, object: DynamicObjectView) -> bool
    recommends
        rabbitmq.well_formed(),
{
    &&& request.is_UpdateRequest()
    &&& request.get_UpdateRequest_0().key == make_stateful_set_key(rabbitmq.object_ref())
    &&& request.get_UpdateRequest_0().obj == update_stateful_set(
        rabbitmq, StatefulSetView::unmarshal(object).get_Ok_0()
    ).marshal()
}

pub open spec fn is_get_stateful_set_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool
    recommends
        rabbitmq.well_formed(),
{
    &&& request.is_GetRequest()
    &&& request.get_GetRequest_0().key == make_stateful_set_key(rabbitmq.object_ref())
}

pub open spec fn is_update_server_config_map_request(request: APIRequest, rabbitmq: RabbitmqClusterView, object: DynamicObjectView) -> bool
    recommends
        rabbitmq.well_formed(),
{
    &&& request.is_UpdateRequest()
    &&& request.get_UpdateRequest_0().key == make_server_config_map_key(rabbitmq.object_ref())
    &&& request.get_UpdateRequest_0().obj == update_server_config_map(
        rabbitmq, ConfigMapView::unmarshal(object).get_Ok_0()
    ).marshal()
}

pub open spec fn at_after_get_server_config_map_step_with_rabbitmq_and_exists_ok_resp_in_flight(
    rabbitmq: RabbitmqClusterView, object: DynamicObjectView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::AfterGetServerConfigMap)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& is_correct_pending_request_msg_at_rabbitmq_step(
            RabbitmqReconcileStep::AfterGetServerConfigMap, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
        }
    }
}

pub open spec fn at_after_get_stateful_set_step_with_rabbitmq_and_exists_ok_resp_in_flight(
    rabbitmq: RabbitmqClusterView, object: DynamicObjectView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::AfterGetStatefulSet)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& is_correct_pending_request_msg_at_rabbitmq_step(
            RabbitmqReconcileStep::AfterGetStatefulSet, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
        }
    }
}

pub open spec fn at_after_get_server_config_map_step_with_rabbitmq_and_exists_not_found_resp_in_flight(
    rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::AfterGetServerConfigMap)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& is_correct_pending_request_msg_at_rabbitmq_step(
            RabbitmqReconcileStep::AfterGetServerConfigMap, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn at_after_get_stateful_set_step_with_rabbitmq_and_exists_not_found_resp_in_flight(
    rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::AfterGetStatefulSet)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& is_correct_pending_request_msg_at_rabbitmq_step(
            RabbitmqReconcileStep::AfterGetStatefulSet, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn at_after_get_server_config_map_step_with_rabbitmq_and_exists_not_found_err_resp_in_flight(
    rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::AfterGetServerConfigMap)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& is_correct_pending_request_msg_at_rabbitmq_step(
            RabbitmqReconcileStep::AfterGetServerConfigMap, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn sts_create_request_msg(key: ObjectRef) -> FnSpec(RMQMessage) -> bool {
    |msg: RMQMessage|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_create_request()
        && msg.content.get_create_request().namespace == make_stateful_set_key(key).namespace
        && msg.content.get_create_request().obj.metadata.name.get_Some_0() == make_stateful_set_key(key).name
        && msg.content.get_create_request().obj.kind == make_stateful_set_key(key).kind
}

pub open spec fn sts_update_request_msg(key: ObjectRef) -> FnSpec(RMQMessage) -> bool {
    |msg: RMQMessage|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_update_request()
        && msg.content.get_update_request().key == make_stateful_set_key(key)
        && msg.content.get_update_request().obj.kind == Kind::StatefulSetKind
}

pub open spec fn sts_get_request_msg(key: ObjectRef) -> FnSpec(RMQMessage) -> bool {
    |msg: RMQMessage|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_get_request()
        && msg.content.get_get_request().key == make_stateful_set_key(key)
}

pub open spec fn sts_get_response_msg(key: ObjectRef) -> FnSpec(RMQMessage) -> bool {
    |msg: RMQMessage|
        msg.src.is_KubernetesAPI()
        && msg.content.is_get_response()
        && (
            msg.content.get_get_response().res.is_Ok()
            ==> msg.content.get_get_response().res.get_Ok_0().object_ref() == make_stateful_set_key(key)
        )
}

}
