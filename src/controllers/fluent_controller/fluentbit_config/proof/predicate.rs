// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::fluent_controller::fluentbit_config::model::{reconciler::*, resource::*};
use crate::fluent_controller::fluentbit_config::proof::resource::*;
use crate::fluent_controller::fluentbit_config::trusted::{
    liveness_theorem::*, spec_types::*, step::*,
};
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
use vstd::prelude::*;

verus! {

pub open spec fn sub_resource_state_matches(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        resource_state_matches::<FluentBitConfigMaker>(sub_resource, fbc, s.resources())
    }
}

pub open spec fn at_fbc_step(key: ObjectRef, step: FluentBitConfigReconcileStep) -> StatePred<FBCCluster>
    recommends
        key.kind.is_CustomResourceKind()
{
    |s: FBCCluster| {
        &&& s.ongoing_reconciles().contains_key(key)
        &&& s.ongoing_reconciles()[key].local_state.reconcile_step == step
    }
}

pub open spec fn at_fbc_step_with_fbc(fbc: FluentBitConfigView, step: FluentBitConfigReconcileStep) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        &&& s.ongoing_reconciles().contains_key(fbc.object_ref())
        &&& s.ongoing_reconciles()[fbc.object_ref()].triggering_cr.object_ref() == fbc.object_ref()
        &&& s.ongoing_reconciles()[fbc.object_ref()].triggering_cr.spec() == fbc.spec()
        &&& s.ongoing_reconciles()[fbc.object_ref()].triggering_cr.metadata().uid == fbc.metadata().uid
        &&& s.ongoing_reconciles()[fbc.object_ref()].local_state.reconcile_step == step
    }
}

pub open spec fn no_pending_req_at_fbc_step_with_fbc(fbc: FluentBitConfigView, step: FluentBitConfigReconcileStep) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::no_pending_req_msg(s, fbc.object_ref())
    }
}

pub open spec fn at_step_closure(step: FluentBitConfigReconcileStep) -> spec_fn(FluentBitConfigReconcileState) -> bool {
    |s: FluentBitConfigReconcileState| s.reconcile_step == step
}

pub open spec fn at_step1_or_step2_closure(step1: FluentBitConfigReconcileStep, step2: FluentBitConfigReconcileStep) -> spec_fn(FluentBitConfigReconcileState) -> bool {
    |s: FluentBitConfigReconcileState| s.reconcile_step == step1 || s.reconcile_step == step2
}

pub open spec fn after_get_k_request_step(sub_resource: SubResource) -> FluentBitConfigReconcileStep {
    FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource)
}

pub open spec fn after_create_k_request_step(sub_resource: SubResource) -> FluentBitConfigReconcileStep {
    FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource)
}

pub open spec fn after_update_k_request_step(sub_resource: SubResource) -> FluentBitConfigReconcileStep {
    FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource)
}

pub open spec fn next_resource_after(sub_resource: SubResource) -> FluentBitConfigReconcileStep {
    match sub_resource {
        SubResource::Secret => FluentBitConfigReconcileStep::Done,
    }
}

pub open spec fn pending_req_in_flight_at_after_get_resource_step(
    sub_resource: SubResource, fbc: FluentBitConfigView
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg->0;
        let request = msg.content.get_APIRequest_0();
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::has_pending_k8s_api_req_msg(s, fbc.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, fbc)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(
    sub_resource: SubResource, fbc: FluentBitConfigView, req_msg: FBCMessage
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_get_k_request_step(sub_resource);
        let request = req_msg.content.get_APIRequest_0();
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::pending_req_msg_is(s, fbc.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& req_msg.dst == HostId::ApiServer
        &&& req_msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, fbc)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(
    sub_resource: SubResource, fbc: FluentBitConfigView, req_msg: FBCMessage
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        &&& s.resources().contains_key(get_request(sub_resource, fbc).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, fbc, req_msg)(s)
    }
}

pub open spec fn at_after_get_resource_step_and_exists_not_found_resp_in_flight(
    sub_resource: SubResource, fbc: FluentBitConfigView
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg->0;
        let request = msg.content.get_APIRequest_0();
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::has_pending_k8s_api_req_msg(s, fbc.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, fbc)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_response().res is Err
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn at_after_get_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, fbc: FluentBitConfigView
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg->0;
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, fbc).key;
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::has_pending_k8s_api_req_msg(s, fbc.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, fbc)
        &&& s.resources().contains_key(key)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_response().res is Ok
            &&& resp_msg.content.get_get_response().res->Ok_0 == s.resources()[key]
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(
    sub_resource: SubResource, fbc: FluentBitConfigView, resp_msg: FBCMessage
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg->0;
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, fbc).key;
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::has_pending_k8s_api_req_msg(s, fbc.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, fbc)
        &&& s.resources().contains_key(key)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_get_response().res is Ok
        &&& resp_msg.content.get_get_response().res->Ok_0 == s.resources()[key]
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_after_get_resource_step(
    sub_resource: SubResource, fbc: FluentBitConfigView, resp_msg: FBCMessage
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg->0;
        let request = msg.content.get_APIRequest_0();
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::has_pending_k8s_api_req_msg(s, fbc.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::ApiServer
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, fbc)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
    }
}

pub open spec fn pending_req_in_flight_at_after_create_resource_step(
    sub_resource: SubResource, fbc: FluentBitConfigView
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg->0;
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::has_pending_k8s_api_req_msg(s, fbc.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& resource_create_request_msg(get_request(sub_resource, fbc).key)(msg)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(
    sub_resource: SubResource, fbc: FluentBitConfigView, req_msg: FBCMessage
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_create_k_request_step(sub_resource);
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::pending_req_msg_is(s, fbc.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& resource_create_request_msg(get_request(sub_resource, fbc).key)(req_msg)
    }
}

pub open spec fn at_after_create_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, fbc: FluentBitConfigView
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg->0;
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, fbc).key;
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::has_pending_k8s_api_req_msg(s, fbc.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_create_request_msg(key)(msg)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_create_response().res is Ok
            &&& state_after_create(sub_resource, fbc, resp_msg.content.get_create_response().res->Ok_0, s.ongoing_reconciles()[fbc.object_ref()].local_state) is Ok
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(
    sub_resource: SubResource, fbc: FluentBitConfigView, resp_msg: FBCMessage
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg->0;
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, fbc).key;
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::has_pending_k8s_api_req_msg(s, fbc.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_create_request_msg(key)(msg)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_create_response().res is Ok
        &&& state_after_create(sub_resource, fbc, resp_msg.content.get_create_response().res->Ok_0, s.ongoing_reconciles()[fbc.object_ref()].local_state) is Ok
    }
}

pub open spec fn pending_req_in_flight_at_after_update_resource_step(
    sub_resource: SubResource, fbc: FluentBitConfigView
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg->0;
        let resource_key = get_request(sub_resource, fbc).key;
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::has_pending_k8s_api_req_msg(s, fbc.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& resource_update_request_msg(get_request(sub_resource, fbc).key)(msg)
        &&& s.resources().contains_key(resource_key)
        &&& msg.content.get_update_request().obj.metadata.resource_version is Some
        &&& msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(
    sub_resource: SubResource, fbc: FluentBitConfigView, req_msg: FBCMessage
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_update_k_request_step(sub_resource);
        let resource_key = get_request(sub_resource, fbc).key;
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::pending_req_msg_is(s, fbc.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& resource_update_request_msg(get_request(sub_resource, fbc).key)(req_msg)
        &&& s.resources().contains_key(resource_key)
        &&& req_msg.content.get_update_request().obj.metadata.resource_version is Some
        &&& req_msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
    }
}

pub open spec fn at_after_update_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, fbc: FluentBitConfigView
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg->0;
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, fbc).key;
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::has_pending_k8s_api_req_msg(s, fbc.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_update_request_msg(key)(msg)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_update_response().res is Ok
            &&& state_after_update(sub_resource, fbc, resp_msg.content.get_update_response().res->Ok_0, s.ongoing_reconciles()[fbc.object_ref()].local_state) is Ok
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(
    sub_resource: SubResource, fbc: FluentBitConfigView, resp_msg: FBCMessage
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[fbc.object_ref()].pending_req_msg->0;
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, fbc).key;
        &&& at_fbc_step_with_fbc(fbc, step)(s)
        &&& FBCCluster::has_pending_k8s_api_req_msg(s, fbc.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_update_request_msg(key)(msg)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_update_response().res is Ok
        &&& state_after_update(sub_resource, fbc, resp_msg.content.get_update_response().res->Ok_0, s.ongoing_reconciles()[fbc.object_ref()].local_state) is Ok
    }
}

}
