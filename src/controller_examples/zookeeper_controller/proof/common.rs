// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    controller::controller_runtime::{continue_reconcile, end_reconcile, run_scheduled_reconcile},
    message::*,
};
use crate::temporal_logic::defs::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::spec::{reconciler::*, zookeepercluster::*};
use vstd::prelude::*;

verus! {

pub type ClusterState = State<ZookeeperClusterView, ZookeeperReconcileState>;

pub open spec fn cluster_spec() -> TempPred<ClusterState> {
    sm_spec::<ZookeeperClusterView, ZookeeperReconcileState, ZookeeperReconciler>()
}

pub open spec fn at_zookeeper_step(key: ObjectRef, step: ZookeeperReconcileStep) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: ClusterState| {
        &&& s.reconcile_state_contains(key)
        &&& s.reconcile_state_of(key).local_state.reconcile_step == step
    }
}

pub open spec fn at_zookeeper_step_with_zk(zk: ZookeeperClusterView, step: ZookeeperReconcileStep) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.reconcile_state_contains(zk.object_ref())
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.object_ref() == zk.object_ref()
        &&& s.reconcile_state_of(zk.object_ref()).triggering_cr.spec == zk.spec
        &&& s.reconcile_state_of(zk.object_ref()).local_state.reconcile_step == step
    }
}

pub open spec fn no_pending_req_at_zookeeper_step_with_zk(zk: ZookeeperClusterView, step: ZookeeperReconcileStep) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_zookeeper_step_with_zk(zk, step)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_None()
    }
}

pub open spec fn pending_req_in_flight_at_zookeeper_step_with_zk(
    step: ZookeeperReconcileStep, zk: ZookeeperClusterView, object: DynamicObjectView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_zookeeper_step_with_zk(zk, step)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& s.message_in_flight(s.pending_req_of(zk.object_ref()))
        &&& is_correct_pending_request_msg_at_zookeeper_step(step, s.pending_req_of(zk.object_ref()), zk, object)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(
    step: ZookeeperReconcileStep, zk: ZookeeperClusterView, req_msg: Message, object: DynamicObjectView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_zookeeper_step_with_zk(zk, step)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg == Option::Some(req_msg)
        &&& s.message_in_flight(req_msg)
        &&& is_correct_pending_request_msg_at_zookeeper_step(step, req_msg, zk, object)
    }
}

pub open spec fn exists_resp_in_flight_at_zookeeper_step_with_zk(
    step: ZookeeperReconcileStep, zk: ZookeeperClusterView, object: DynamicObjectView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_zookeeper_step_with_zk(zk, step)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_correct_pending_request_msg_at_zookeeper_step(step, s.pending_req_of(zk.object_ref()), zk, object)
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_zookeeper_step_with_zk(
    step: ZookeeperReconcileStep, zk: ZookeeperClusterView, resp_msg: Message, object: DynamicObjectView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_zookeeper_step_with_zk(zk, step)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_correct_pending_request_msg_at_zookeeper_step(step, s.pending_req_of(zk.object_ref()), zk, object)
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
    }
}

pub open spec fn at_after_get_stateful_set_step_with_zk_and_exists_ok_resp_in_flight(
    zk: ZookeeperClusterView, object: DynamicObjectView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::AfterGetStatefulSet)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_correct_pending_request_msg_at_zookeeper_step(
            ZookeeperReconcileStep::AfterGetStatefulSet, s.pending_req_of(zk.object_ref()), zk, arbitrary()
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
        }
    }
}

pub open spec fn at_after_get_stateful_set_step_with_zk_and_exists_not_found_resp_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::AfterGetStatefulSet)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_correct_pending_request_msg_at_zookeeper_step(
            ZookeeperReconcileStep::AfterGetStatefulSet, s.pending_req_of(zk.object_ref()), zk, arbitrary()
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn at_after_get_stateful_set_step_with_zk_and_exists_not_found_err_resp_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::AfterGetStatefulSet)(s)
        &&& s.reconcile_state_of(zk.object_ref()).pending_req_msg.is_Some()
        &&& is_correct_pending_request_msg_at_zookeeper_step(
            ZookeeperReconcileStep::AfterGetStatefulSet, s.pending_req_of(zk.object_ref()), zk, arbitrary()
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, s.pending_req_of(zk.object_ref()))
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn is_correct_pending_request_msg_at_zookeeper_step(
    step: ZookeeperReconcileStep, msg: Message, zk: ZookeeperClusterView, object: DynamicObjectView
) -> bool {
    &&& msg.src == HostId::CustomController
    &&& msg.dst == HostId::KubernetesAPI
    &&& msg.content.is_APIRequest()
    &&& is_correct_pending_request_at_zookeeper_step(step, msg.content.get_APIRequest_0(), zk, object)
}

pub open spec fn is_correct_pending_request_at_zookeeper_step(
    step: ZookeeperReconcileStep, request: APIRequest, zk: ZookeeperClusterView, object: DynamicObjectView
) -> bool {
    match step {
        ZookeeperReconcileStep::AfterCreateHeadlessService => is_create_headless_service_request(request, zk),
        ZookeeperReconcileStep::AfterCreateClientService => is_create_client_service_request(request, zk),
        ZookeeperReconcileStep::AfterCreateAdminServerService => is_create_admin_server_service_request(request, zk),
        ZookeeperReconcileStep::AfterCreateConfigMap => is_create_config_map_request(request, zk),
        ZookeeperReconcileStep::AfterGetStatefulSet => is_get_stateful_set_request(request, zk),
        ZookeeperReconcileStep::AfterCreateStatefulSet => is_create_stateful_set_request(request, zk),
        ZookeeperReconcileStep::AfterUpdateStatefulSet => is_update_stateful_set_request(request, zk, object),
        _ => false
    }
}

pub open spec fn is_create_headless_service_request(request: APIRequest, zk: ZookeeperClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == zk.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_headless_service(zk).to_dynamic_object()
}

pub open spec fn is_create_client_service_request(request: APIRequest, zk: ZookeeperClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == zk.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_client_service(zk).to_dynamic_object()
}

pub open spec fn is_create_admin_server_service_request(request: APIRequest, zk: ZookeeperClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == zk.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_admin_server_service(zk).to_dynamic_object()
}

pub open spec fn is_create_config_map_request(request: APIRequest, zk: ZookeeperClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == zk.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_config_map(zk).to_dynamic_object()
}

pub open spec fn is_get_stateful_set_request(request: APIRequest, zk: ZookeeperClusterView) -> bool
    recommends
        zk.well_formed(),
{
    &&& request.is_GetRequest()
    &&& request.get_GetRequest_0().key == ObjectRef {
        kind: StatefulSetView::kind(),
        name: make_stateful_set_name(zk.metadata.name.get_Some_0()),
        namespace: zk.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn is_create_stateful_set_request(request: APIRequest, zk: ZookeeperClusterView) -> bool
    recommends
        zk.well_formed(),
{
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == zk.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_stateful_set(zk).to_dynamic_object()
}

pub open spec fn is_update_stateful_set_request(request: APIRequest, zk: ZookeeperClusterView, object: DynamicObjectView) -> bool
    recommends
        zk.well_formed(),
{
    &&& request.is_UpdateRequest()
    &&& request.get_UpdateRequest_0().key == make_stateful_set_key(zk.object_ref())
    &&& request.get_UpdateRequest_0().obj == update_stateful_set(
        zk, StatefulSetView::from_dynamic_object(object).get_Ok_0()
    ).to_dynamic_object()
}

}
