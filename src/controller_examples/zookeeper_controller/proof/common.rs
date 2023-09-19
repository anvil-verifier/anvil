// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::proof::controller_runtime::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::defs::*;
use crate::zookeeper_controller::common::*;
use crate::zookeeper_controller::spec::zookeeper_api::*;
use crate::zookeeper_controller::spec::{reconciler::*, zookeepercluster::*};
use vstd::prelude::*;

verus! {

pub type ZKCluster = Cluster<ZookeeperClusterView, ZKAPI, ZookeeperReconciler>;

pub type ZKMessage = Message<ZKAPIInputView, ZKAPIOutputView>;

pub open spec fn cluster_spec() -> TempPred<ZKCluster> {
    ZKCluster::sm_spec()
}

pub open spec fn zookeeper_reconcile_state_with_sts(step: ZookeeperReconcileStep, sts: Option<StatefulSetView>) -> ZookeeperReconcileState {
    ZookeeperReconcileState {
        reconcile_step: step,
        sts_from_get: sts,
    }
}

pub open spec fn zookeeper_reconcile_state(step: ZookeeperReconcileStep) -> FnSpec(ZookeeperReconcileState) -> bool {
    |s: ZookeeperReconcileState| s.reconcile_step == step
}

pub open spec fn at_zookeeper_step(key: ObjectRef, step: ZookeeperReconcileStep) -> StatePred<ZKCluster>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: ZKCluster| {
        &&& s.ongoing_reconciles().contains_key(key)
        &&& s.ongoing_reconciles()[key].local_state.reconcile_step == step
    }
}

pub open spec fn at_zookeeper_step_with_zk(zk: ZookeeperClusterView, step: ZookeeperReconcileStep) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& s.ongoing_reconciles().contains_key(zk.object_ref())
        &&& s.ongoing_reconciles()[zk.object_ref()].triggering_cr.object_ref() == zk.object_ref()
        &&& s.ongoing_reconciles()[zk.object_ref()].triggering_cr.spec == zk.spec
        &&& s.ongoing_reconciles()[zk.object_ref()].local_state.reconcile_step == step
    }
}

pub open spec fn no_pending_req_at_zookeeper_step_with_zk(zk: ZookeeperClusterView, step: ZookeeperReconcileStep) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& at_zookeeper_step_with_zk(zk, step)(s)
        &&& ZKCluster::no_pending_req_msg_or_external_api_input(s, zk.object_ref())
    }
}

pub open spec fn pending_req_in_flight_at_zookeeper_step_with_zk(
    step: ZookeeperReconcileStep, zk: ZookeeperClusterView, object: DynamicObjectView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& at_zookeeper_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_k8s_api_req_msg(s, zk.object_ref())
        &&& s.in_flight().contains(s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0())
        &&& is_correct_pending_request_msg_at_zookeeper_step(step, s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0(), zk, object)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_zookeeper_step_with_zk(
    step: ZookeeperReconcileStep, zk: ZookeeperClusterView, req_msg: ZKMessage, object: DynamicObjectView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& at_zookeeper_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_k8s_api_req_msg_is(s, zk.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& is_correct_pending_request_msg_at_zookeeper_step(step, req_msg, zk, object)
    }
}

pub open spec fn exists_resp_in_flight_at_zookeeper_step_with_zk(
    step: ZookeeperReconcileStep, zk: ZookeeperClusterView, object: DynamicObjectView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& at_zookeeper_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_k8s_api_req_msg(s, zk.object_ref())
        &&& is_correct_pending_request_msg_at_zookeeper_step(step, s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0(), zk, object)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0())
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_zookeeper_step_with_zk(
    step: ZookeeperReconcileStep, zk: ZookeeperClusterView, resp_msg: ZKMessage, object: DynamicObjectView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& at_zookeeper_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_k8s_api_req_msg(s, zk.object_ref())
        &&& is_correct_pending_request_msg_at_zookeeper_step(step, s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0(), zk, object)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0())
    }
}

pub open spec fn at_after_get_stateful_set_step_with_zk_and_exists_ok_resp_in_flight(
    zk: ZookeeperClusterView, object: DynamicObjectView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::AfterGetStatefulSet)(s)
        &&& ZKCluster::pending_k8s_api_req_msg(s, zk.object_ref())
        &&& is_correct_pending_request_msg_at_zookeeper_step(
            ZookeeperReconcileStep::AfterGetStatefulSet, s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0(), zk, arbitrary()
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0())
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == object
        }
    }
}

pub open spec fn at_after_get_stateful_set_step_with_zk_and_exists_not_found_resp_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::AfterGetStatefulSet)(s)
        &&& ZKCluster::pending_k8s_api_req_msg(s, zk.object_ref())
        &&& is_correct_pending_request_msg_at_zookeeper_step(
            ZookeeperReconcileStep::AfterGetStatefulSet, s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0(), zk, arbitrary()
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0())
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn at_after_get_stateful_set_step_with_zk_and_exists_not_found_err_resp_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& at_zookeeper_step_with_zk(zk, ZookeeperReconcileStep::AfterGetStatefulSet)(s)
        &&& ZKCluster::pending_k8s_api_req_msg(s, zk.object_ref())
        &&& is_correct_pending_request_msg_at_zookeeper_step(
            ZookeeperReconcileStep::AfterGetStatefulSet, s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0(), zk, arbitrary()
        )
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0())
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn is_correct_pending_request_msg_at_zookeeper_step(
    step: ZookeeperReconcileStep, msg: ZKMessage, zk: ZookeeperClusterView, object: DynamicObjectView
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
    &&& request.get_CreateRequest_0().obj == make_headless_service(zk).marshal()
}

pub open spec fn is_create_client_service_request(request: APIRequest, zk: ZookeeperClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == zk.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_client_service(zk).marshal()
}

pub open spec fn is_create_admin_server_service_request(request: APIRequest, zk: ZookeeperClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == zk.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_admin_server_service(zk).marshal()
}

pub open spec fn is_create_config_map_request(request: APIRequest, zk: ZookeeperClusterView) -> bool {
    &&& request.is_CreateRequest()
    &&& request.get_CreateRequest_0().namespace == zk.metadata.namespace.get_Some_0()
    &&& request.get_CreateRequest_0().obj == make_config_map(zk).marshal()
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
    &&& request.get_CreateRequest_0().obj == make_stateful_set(zk).marshal()
}

pub open spec fn is_update_stateful_set_request(request: APIRequest, zk: ZookeeperClusterView, object: DynamicObjectView) -> bool
    recommends
        zk.well_formed(),
{
    &&& request.is_UpdateRequest()
    &&& request.get_UpdateRequest_0().key == make_stateful_set_key(zk.object_ref())
    &&& request.get_UpdateRequest_0().obj == update_stateful_set(
        zk, StatefulSetView::unmarshal(object).get_Ok_0()
    ).marshal()
}

}
