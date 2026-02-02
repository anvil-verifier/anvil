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
use crate::rabbitmq_controller::proof::resource::*;
use crate::rabbitmq_controller::trusted::{
    spec_types::*, step::*,
};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub open spec fn sub_resource_state_matches(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        resource_state_matches(sub_resource, rabbitmq, s.resources())
    }
}

pub open spec fn resource_state_matches(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resources: StoredState) -> bool {
    let key = get_request(sub_resource, rabbitmq).key;
    let obj = resources[key];
    let made_spec = make(sub_resource, rabbitmq, RabbitmqReconcileState {
        reconcile_step: RabbitmqReconcileStep::Init,
        latest_config_map_rv_opt: if resources.contains_key(get_request(SubResource::ServerConfigMap, rabbitmq).key) && resources[get_request(SubResource::ServerConfigMap, rabbitmq).key].metadata.resource_version is Some {
            Some(int_to_string_view(resources[get_request(SubResource::ServerConfigMap, rabbitmq).key].metadata.resource_version->0))
        } else {
            None
        },
    });
    &&& resources.contains_key(key)
    &&& made_spec is Ok
    &&& obj.spec == made_spec->Ok_0.spec
}

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

pub open spec fn at_step_closure(step: RabbitmqReconcileStep) -> spec_fn(RabbitmqReconcileState) -> bool {
    |s: RabbitmqReconcileState| s.reconcile_step == step
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
        SubResource::RoleBinding => after_get_k_request_step(SubResource::StatefulSet),
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

pub open spec fn pending_req_in_flight_at_after_create_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_create_k_request_step(sub_resource);
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(req_msg)
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
        let resource_key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::has_pending_k8s_api_req_msg(controller_id, s, rabbitmq.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_update_request_msg(resource_key)(msg)
        &&& s.resources().contains_key(resource_key)
        &&& msg.content.get_update_request().obj.metadata.resource_version is Some
        &&& msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, controller_id: int, req_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = after_update_k_request_step(sub_resource);
        let resource_key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
        &&& resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(req_msg)
        &&& s.resources().contains_key(resource_key)
        &&& req_msg.content.get_update_request().obj.metadata.resource_version is Some
        &&& req_msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
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

}
