// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::EmptyAPI;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::proof::controller_runtime::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::{rabbitmqcluster::*, reconciler::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub type RMQCluster = Cluster<RabbitmqClusterView, EmptyAPI, RabbitmqReconciler>;

pub open spec fn cluster_spec() -> TempPred<RMQCluster> {
    RMQCluster::sm_spec()
}

pub open spec fn at_rabbitmq_step(key: ObjectRef, step: RabbitmqReconcileStep) -> StatePred<RMQCluster>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: RMQCluster| {
        &&& s.reconcile_state_contains(key)
        &&& s.reconcile_state_of(key).local_state.reconcile_step == step
    }
}

pub open spec fn at_step_closure(step: RabbitmqReconcileStep) -> FnSpec(RabbitmqReconcileState) -> bool {
    |s: RabbitmqReconcileState| s.reconcile_step == step
}

pub open spec fn at_rabbitmq_step_with_rabbitmq(rabbitmq: RabbitmqClusterView, step: RabbitmqReconcileStep) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& s.reconcile_state_contains(rabbitmq.object_ref())
        // &&& s.reconcile_state_of(rabbitmq.object_ref()).triggering_cr.object_ref() == rabbitmq.object_ref()
        &&& s.reconcile_state_of(rabbitmq.object_ref()).triggering_cr == rabbitmq
        &&& s.reconcile_state_of(rabbitmq.object_ref()).local_state.reconcile_step == step
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
        &&& s.message_in_flight(s.pending_req_of(rabbitmq.object_ref()))
        &&& is_correct_pending_request_msg_at_rabbitmq_step(step, s.pending_req_of(rabbitmq.object_ref()), rabbitmq)
    }
}

pub open spec fn pending_req_with_object_in_flight_at_rabbitmq_step_with_rabbitmq(
    step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, object: DynamicObjectView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& s.message_in_flight(s.pending_req_of(rabbitmq.object_ref()))
        &&& is_correct_pending_request_msg_with_object_at_rabbitmq_step(step, s.pending_req_of(rabbitmq.object_ref()), rabbitmq, object)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(
    step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, req_msg: Message
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg_is(s, rabbitmq.object_ref(), req_msg)
        &&& s.message_in_flight(req_msg)
        &&& is_correct_pending_request_msg_at_rabbitmq_step(step, req_msg, rabbitmq)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_with_object_at_rabbitmq_step_with_rabbitmq(
    step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, req_msg: Message, object: DynamicObjectView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg_is(s, rabbitmq.object_ref(), req_msg)
        &&& s.message_in_flight(req_msg)
        &&& is_correct_pending_request_msg_with_object_at_rabbitmq_step(step, req_msg, rabbitmq, object)
    }
}

pub open spec fn exists_resp_in_flight_at_rabbitmq_step_with_rabbitmq(
    step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& is_correct_pending_request_msg_at_rabbitmq_step(step, s.pending_req_of(rabbitmq.object_ref()), rabbitmq)
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(rabbitmq.object_ref()))
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(
    step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, resp_msg: Message
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& is_correct_pending_request_msg_at_rabbitmq_step(step, s.pending_req_of(rabbitmq.object_ref()), rabbitmq)
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(rabbitmq.object_ref()))
    }
}

pub open spec fn is_correct_pending_request_msg_at_rabbitmq_step(
    step: RabbitmqReconcileStep, msg: Message, rabbitmq: RabbitmqClusterView
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
        _ => false
    }
}

pub open spec fn is_correct_pending_request_msg_with_object_at_rabbitmq_step(
    step: RabbitmqReconcileStep, msg: Message, rabbitmq: RabbitmqClusterView, object: DynamicObjectView
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
    &&& request.get_CreateRequest_0().obj == make_headless_service(rabbitmq).to_dynamic_object()
}

pub open spec fn is_create_service_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_main_service(rabbitmq).to_dynamic_object()
}

pub open spec fn is_create_erlang_secret_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_erlang_secret(rabbitmq).to_dynamic_object()
}

pub open spec fn is_create_default_user_secret_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_default_user_secret(rabbitmq).to_dynamic_object()
}

pub open spec fn is_create_plugins_config_map_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_plugins_config_map(rabbitmq).to_dynamic_object()
}

pub open spec fn is_create_server_config_map_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_server_config_map(rabbitmq).to_dynamic_object()
}

pub open spec fn is_create_service_account_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_service_account(rabbitmq).to_dynamic_object()
}

pub open spec fn is_create_role_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_role(rabbitmq).to_dynamic_object()
}

pub open spec fn is_create_role_binding_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_role_binding(rabbitmq).to_dynamic_object()
}

pub open spec fn is_create_stateful_set_request(request: APIRequest, rabbitmq: RabbitmqClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_stateful_set(rabbitmq).to_dynamic_object()
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
        rabbitmq, StatefulSetView::from_dynamic_object(object).get_Ok_0()
    ).to_dynamic_object()
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
    &&& request.get_UpdateRequest_0().obj == ConfigMapView::from_dynamic_object(object).get_Ok_0()
                                            .set_data(make_server_config_map(rabbitmq).data.get_Some_0())
                                            .to_dynamic_object()
}

pub open spec fn at_after_get_server_config_map_step_with_rabbitmq_and_exists_ok_resp_in_flight(
    rabbitmq: RabbitmqClusterView, object: DynamicObjectView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, RabbitmqReconcileStep::AfterGetServerConfigMap)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& is_correct_pending_request_msg_at_rabbitmq_step(
            RabbitmqReconcileStep::AfterGetServerConfigMap, s.pending_req_of(rabbitmq.object_ref()), rabbitmq
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(rabbitmq.object_ref()))
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
            RabbitmqReconcileStep::AfterGetServerConfigMap, s.pending_req_of(rabbitmq.object_ref()), rabbitmq
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(rabbitmq.object_ref()))
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
            RabbitmqReconcileStep::AfterGetServerConfigMap, s.pending_req_of(rabbitmq.object_ref()), rabbitmq
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(rabbitmq.object_ref()))
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

}
