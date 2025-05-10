// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, prelude::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::proof::controller_runtime::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::defs::*;
use crate::zookeeper_controller::model::{reconciler::*, resource::*};
use crate::zookeeper_controller::proof::resource::*;
use crate::zookeeper_controller::trusted::{
    liveness_theorem::*, spec_types::*, step::*, zookeeper_api_spec::*,
};
use vstd::prelude::*;

verus! {

pub open spec fn sub_resource_state_matches(sub_resource: SubResource, zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        resource_state_matches::<ZookeeperMaker>(sub_resource, zk, s.resources())
    }
}

pub open spec fn at_step_closure(step: ZookeeperReconcileStep) -> spec_fn(ZookeeperReconcileState) -> bool {
    |s: ZookeeperReconcileState| s.reconcile_step == step
}

pub open spec fn at_zk_step(key: ObjectRef, step: ZookeeperReconcileStep) -> StatePred<ZKCluster>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: ZKCluster| {
        &&& s.ongoing_reconciles().contains_key(key)
        &&& s.ongoing_reconciles()[key].local_state.reconcile_step == step
    }
}

pub open spec fn at_zk_step_with_zk(zk: ZookeeperClusterView, step: ZookeeperReconcileStep) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& s.ongoing_reconciles().contains_key(zk.object_ref())
        &&& s.ongoing_reconciles()[zk.object_ref()].triggering_cr.object_ref() == zk.object_ref()
        &&& s.ongoing_reconciles()[zk.object_ref()].triggering_cr.spec() == zk.spec()
        &&& s.ongoing_reconciles()[zk.object_ref()].triggering_cr.metadata().uid == zk.metadata().uid
        &&& s.ongoing_reconciles()[zk.object_ref()].local_state.reconcile_step == step
    }
}

pub open spec fn no_pending_req_at_zookeeper_step_with_zookeeper(zk: ZookeeperClusterView, step: ZookeeperReconcileStep) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::no_pending_req_msg(s, zk.object_ref())
    }
}

pub open spec fn after_get_k_request_step(sub_resource: SubResource) -> ZookeeperReconcileStep {
    ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource)
}

pub open spec fn after_create_k_request_step(sub_resource: SubResource) -> ZookeeperReconcileStep {
    ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource)
}

pub open spec fn after_update_k_request_step(sub_resource: SubResource) -> ZookeeperReconcileStep {
    ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource)
}

pub open spec fn next_resource_after(sub_resource: SubResource) -> ZookeeperReconcileStep {
    match sub_resource {
        SubResource::HeadlessService => after_get_k_request_step(SubResource::ClientService),
        SubResource::ClientService => after_get_k_request_step(SubResource::AdminServerService),
        SubResource::AdminServerService => after_get_k_request_step(SubResource::ConfigMap),
        SubResource::ConfigMap => ZookeeperReconcileStep::AfterExistsStatefulSet,
        SubResource::StatefulSet => ZookeeperReconcileStep::AfterUpdateStatus,
    }
}

pub open spec fn pending_req_in_flight_at_after_get_resource_step(
    sub_resource: SubResource, zk: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, zk)
    }
}

pub open spec fn pending_req_in_flight_at_after_exists_stateful_set_step(
    zk: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsStatefulSet;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(SubResource::StatefulSet, zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(
    sub_resource: SubResource, zk: ZookeeperClusterView, req_msg: ZKMessage
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_get_k_request_step(sub_resource);
        let request = req_msg.content.get_APIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_req_msg_is(s, zk.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& req_msg.dst == HostId::ApiServer
        &&& req_msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_exists_stateful_set_step(
    zk: ZookeeperClusterView, req_msg: ZKMessage
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsStatefulSet;
        let request = req_msg.content.get_APIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_req_msg_is(s, zk.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& req_msg.dst == HostId::ApiServer
        &&& req_msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(SubResource::StatefulSet, zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(
    sub_resource: SubResource, zk: ZookeeperClusterView, req_msg: ZKMessage
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        &&& s.resources().contains_key(get_request(sub_resource, zk).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, zk, req_msg)(s)
    }
}

pub open spec fn at_after_get_resource_step_and_exists_not_found_resp_in_flight(
    sub_resource: SubResource, zk: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, zk)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn at_after_exists_stateful_set_step_and_exists_not_found_resp_in_flight(
    zk: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsStatefulSet;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(SubResource::StatefulSet, zk)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn at_after_get_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, zk: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        // TODO: rethink whether we should keep s.resources().contains_key(key) here
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, zk).key;
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, zk)
        &&& s.resources().contains_key(key)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == s.resources()[key]
        }
    }
}

pub open spec fn at_after_exists_stateful_set_step_and_exists_ok_resp_in_flight(zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsStatefulSet;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(SubResource::StatefulSet, zk).key;
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(SubResource::StatefulSet, zk)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(
    sub_resource: SubResource, zk: ZookeeperClusterView, resp_msg: ZKMessage
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        // TODO: rethink whether we should keep s.resources().contains_key(key) here
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, zk).key;
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, zk)
        &&& s.resources().contains_key(key)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_get_response().res.is_Ok()
        &&& resp_msg.content.get_get_response().res.get_Ok_0() == s.resources()[key]
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_exists_stateful_set_step(zk: ZookeeperClusterView, resp_msg: ZKMessage) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsStatefulSet;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(SubResource::StatefulSet, zk).key;
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(SubResource::StatefulSet, zk)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_get_response().res.is_Ok()
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_after_get_resource_step(
    sub_resource: SubResource, zk: ZookeeperClusterView, resp_msg: ZKMessage
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, zk)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_after_exists_stateful_set_step(
    zk: ZookeeperClusterView, resp_msg: ZKMessage
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsStatefulSet;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(SubResource::StatefulSet, zk)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
    }
}

pub open spec fn zk_set_data_request_msg(zk: ZookeeperClusterView) -> spec_fn(ZKMessage) -> bool {
    |msg: ZKMessage|
        msg.dst.is_ExternalAPI()
        && msg.content.is_ExternalAPIRequest()
        && msg.content.get_ExternalAPIRequest_0().is_SetDataRequest()
        && msg.content.get_ExternalAPIRequest_0().get_SetDataRequest_0() == zk.metadata.name.get_Some_0()
        && msg.content.get_ExternalAPIRequest_0().get_SetDataRequest_1() == zk.metadata.namespace.get_Some_0()
}

pub open spec fn zk_create_node_request_msg(zk: ZookeeperClusterView) -> spec_fn(ZKMessage) -> bool {
    |msg: ZKMessage|
        msg.dst.is_ExternalAPI()
        && msg.content.is_ExternalAPIRequest()
        && msg.content.get_ExternalAPIRequest_0().is_CreateRequest()
        && msg.content.get_ExternalAPIRequest_0().get_CreateRequest_0() == zk.metadata.name.get_Some_0()
        && msg.content.get_ExternalAPIRequest_0().get_CreateRequest_1() == zk.metadata.namespace.get_Some_0()
        && msg.content.get_ExternalAPIRequest_0().get_CreateRequest_3() == zk_node_path(zk)
}

pub open spec fn pending_req_in_flight_at_after_create_resource_step(
    sub_resource: SubResource, zk: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& resource_create_request_msg(get_request(sub_resource, zk).key)(msg)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(
    sub_resource: SubResource, zk: ZookeeperClusterView, req_msg: ZKMessage
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_create_k_request_step(sub_resource);
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_req_msg_is(s, zk.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& resource_create_request_msg(get_request(sub_resource, zk).key)(req_msg)
    }
}

pub open spec fn at_after_create_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, zk: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, zk).key;
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_create_request_msg(key)(msg)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_create_response().res.is_Ok()
            &&& state_after_create(sub_resource, zk, resp_msg.content.get_create_response().res.get_Ok_0(), s.ongoing_reconciles()[zk.object_ref()].local_state).is_Ok()
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(
    sub_resource: SubResource, zk: ZookeeperClusterView, resp_msg: ZKMessage
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, zk).key;
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_create_request_msg(key)(msg)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_create_response().res.is_Ok()
        &&& state_after_create(sub_resource, zk, resp_msg.content.get_create_response().res.get_Ok_0(), s.ongoing_reconciles()[zk.object_ref()].local_state).is_Ok()
    }
}

pub open spec fn pending_req_in_flight_at_after_update_resource_step(
    sub_resource: SubResource, zk: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let resource_key= get_request(sub_resource, zk).key;
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& resource_update_request_msg(resource_key)(msg)
        &&& s.resources().contains_key(resource_key)
        &&& msg.content.get_update_request().obj.metadata.resource_version.is_Some()
        &&& msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(
    sub_resource: SubResource, zk: ZookeeperClusterView, req_msg: ZKMessage
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_update_k_request_step(sub_resource);
        let resource_key = get_request(sub_resource, zk).key;
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_req_msg_is(s, zk.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& resource_update_request_msg(get_request(sub_resource, zk).key)(req_msg)
        &&& s.resources().contains_key(resource_key)
        &&& req_msg.content.get_update_request().obj.metadata.resource_version.is_Some()
        &&& req_msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
    }
}

pub open spec fn at_after_update_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, zk: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, zk).key;
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_update_request_msg(key)(msg)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_update_response().res.is_Ok()
            &&& state_after_update(sub_resource, zk, resp_msg.content.get_update_response().res.get_Ok_0(), s.ongoing_reconciles()[zk.object_ref()].local_state).is_Ok()
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(
    sub_resource: SubResource, zk: ZookeeperClusterView, resp_msg: ZKMessage
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, zk).key;
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::has_pending_k8s_api_req_msg(s, zk.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_update_request_msg(key)(msg)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_update_response().res.is_Ok()
        &&& state_after_update(sub_resource, zk, resp_msg.content.get_update_response().res.get_Ok_0(), s.ongoing_reconciles()[zk.object_ref()].local_state).is_Ok()
    }
}

// Predicates below are for zookeeper_api reasoning

pub open spec fn pending_req_in_flight_at_after_exists_zk_node_step(zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsZKNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_ExternalAPIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& request == zk_exists_request(zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_exists_zk_node_step(zk: ZookeeperClusterView, req_msg: ZKMessage) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsZKNode;
        let request = req_msg.content.get_ExternalAPIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_req_msg_is(s, zk.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& req_msg.dst == HostId::ExternalAPI
        &&& req_msg.content.is_ExternalAPIRequest()
        &&& request == zk_exists_request(zk)
    }
}

pub open spec fn zk_node_addr(s: ZKCluster, zk: ZookeeperClusterView) -> ZKNodeAddr {
    let sts_uid = s.resources()[get_request(SubResource::StatefulSet, zk).key].metadata.uid.get_Some_0();
    ZKNodeAddr::new(zk.metadata.name.get_Some_0(), zk.metadata.namespace.get_Some_0(), sts_uid, zk_node_path(zk))
}

pub open spec fn zk_parent_node_addr(s: ZKCluster, zk: ZookeeperClusterView) -> ZKNodeAddr {
    let sts_uid = s.resources()[get_request(SubResource::StatefulSet, zk).key].metadata.uid.get_Some_0();
    ZKNodeAddr::new(zk.metadata.name.get_Some_0(), zk.metadata.namespace.get_Some_0(), sts_uid, zk_parent_node_path(zk))
}

pub open spec fn at_after_exists_zk_node_step_and_exists_ok_resp_in_flight(zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsZKNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let addr = zk_node_addr(s, zk);
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& exists |resp_msg: ZKMessage| {
            let resp = resp_msg.content.get_ExternalAPIResponse_0();
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp == ZKAPIOutputView::ExistsResponse(ZKAPIExistsResultView{res: Ok(Some(s.external_state().data[addr].1))})
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_exists_zk_node_step(zk: ZookeeperClusterView, resp_msg: ZKMessage) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsZKNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let resp = resp_msg.content.get_ExternalAPIResponse_0();
        let addr = zk_node_addr(s, zk);
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp == ZKAPIOutputView::ExistsResponse(ZKAPIExistsResultView{res: Ok(Some(s.external_state().data[addr].1))})
    }
}

pub open spec fn pending_req_in_flight_at_after_update_zk_node_step(zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterUpdateZKNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_ExternalAPIRequest_0();
        let addr = zk_node_addr(s, zk);
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& request == zk_set_data_request(zk, s.external_state().data[addr].1)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_update_zk_node_step(zk: ZookeeperClusterView, req_msg: ZKMessage) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterUpdateZKNode;
        let request = req_msg.content.get_ExternalAPIRequest_0();
        let addr = zk_node_addr(s, zk);
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_req_msg_is(s, zk.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& req_msg.dst == HostId::ExternalAPI
        &&& req_msg.content.is_ExternalAPIRequest()
        &&& request == zk_set_data_request(zk, s.external_state().data[addr].1)
    }
}

pub open spec fn at_after_update_zk_node_step_and_exists_ok_resp_in_flight(zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterUpdateZKNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& exists |resp_msg: ZKMessage| {
            let resp = resp_msg.content.get_ExternalAPIResponse_0();
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp == ZKAPIOutputView::SetDataResponse(ZKAPISetDataResultView{res: Ok(())})
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_update_zk_node_step(zk: ZookeeperClusterView, resp_msg: ZKMessage) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterUpdateZKNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let resp = resp_msg.content.get_ExternalAPIResponse_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp == ZKAPIOutputView::SetDataResponse(ZKAPISetDataResultView{res: Ok(())})
    }
}

pub open spec fn at_after_exists_zk_node_step_and_exists_not_found_resp_in_flight(zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsZKNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& exists |resp_msg: ZKMessage| {
            let resp = resp_msg.content.get_ExternalAPIResponse_0();
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp == ZKAPIOutputView::ExistsResponse(ZKAPIExistsResultView{res: Ok(None)})
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_not_found_resp_at_after_exists_zk_node_step(zk: ZookeeperClusterView, resp_msg: ZKMessage) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterExistsZKNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let resp = resp_msg.content.get_ExternalAPIResponse_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp == ZKAPIOutputView::ExistsResponse(ZKAPIExistsResultView{res: Ok(None)})
    }
}

pub open spec fn pending_req_in_flight_at_after_create_zk_parent_node_step(zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterCreateZKParentNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_ExternalAPIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& request == zk_create_parent_node_request(zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_zk_parent_node_step(zk: ZookeeperClusterView, req_msg: ZKMessage) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterCreateZKParentNode;
        let request = req_msg.content.get_ExternalAPIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_req_msg_is(s, zk.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& req_msg.dst == HostId::ExternalAPI
        &&& req_msg.content.is_ExternalAPIRequest()
        &&& request == zk_create_parent_node_request(zk)
    }
}

pub open spec fn at_after_create_zk_parent_node_step_and_exists_ok_or_already_exists_resp_in_flight(zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterCreateZKParentNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& exists |resp_msg: ZKMessage| {
            let resp = resp_msg.content.get_ExternalAPIResponse_0();
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& (resp == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Ok(())})
                || resp == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Err(ZKAPIError::ZKNodeCreateAlreadyExists)}))
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_or_already_exists_resp_at_after_create_zk_parent_node_step(zk: ZookeeperClusterView, resp_msg: ZKMessage) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterCreateZKParentNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let resp = resp_msg.content.get_ExternalAPIResponse_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& (resp == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Ok(())})
            || resp == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Err(ZKAPIError::ZKNodeCreateAlreadyExists)}))
    }
}

pub open spec fn pending_req_in_flight_at_after_create_zk_node_step(zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterCreateZKNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_ExternalAPIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& request == zk_create_node_request(zk)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_zk_node_step(zk: ZookeeperClusterView, req_msg: ZKMessage) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterCreateZKNode;
        let request = req_msg.content.get_ExternalAPIRequest_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& ZKCluster::pending_req_msg_is(s, zk.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& req_msg.dst == HostId::ExternalAPI
        &&& req_msg.content.is_ExternalAPIRequest()
        &&& request == zk_create_node_request(zk)
    }
}

pub open spec fn at_after_create_zk_node_step_and_exists_ok_resp_in_flight(zk: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterCreateZKNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& exists |resp_msg: ZKMessage| {
            let resp = resp_msg.content.get_ExternalAPIResponse_0();
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Ok(())})
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_create_zk_node_step(zk: ZookeeperClusterView, resp_msg: ZKMessage) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let step = ZookeeperReconcileStep::AfterCreateZKNode;
        let msg = s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.get_Some_0();
        let resp = resp_msg.content.get_ExternalAPIResponse_0();
        &&& at_zk_step_with_zk(zk, step)(s)
        &&& s.ongoing_reconciles()[zk.object_ref()].pending_req_msg.is_Some()
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ExternalAPI
        &&& msg.content.is_ExternalAPIRequest()
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp == ZKAPIOutputView::CreateResponse(ZKAPICreateResultView{res: Ok(())})
    }
}


}
