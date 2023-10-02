// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, prelude::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::proof::controller_runtime::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::proof::resource::*;
use crate::rabbitmq_controller::spec::{reconciler::*, resource::*, types::*};
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

pub open spec fn at_rabbitmq_step_with_rabbitmq(rabbitmq: RabbitmqClusterView, step: RabbitmqReconcileStep) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& s.ongoing_reconciles().contains_key(rabbitmq.object_ref())
        &&& s.ongoing_reconciles()[rabbitmq.object_ref()].triggering_cr.object_ref() == rabbitmq.object_ref()
        &&& s.ongoing_reconciles()[rabbitmq.object_ref()].triggering_cr.spec() == rabbitmq.spec()
        &&& s.ongoing_reconciles()[rabbitmq.object_ref()].triggering_cr.metadata().uid == rabbitmq.metadata().uid
        &&& s.ongoing_reconciles()[rabbitmq.object_ref()].local_state.reconcile_step == step
    }
}

pub open spec fn at_step_closure(step: RabbitmqReconcileStep) -> FnSpec(RabbitmqReconcileState) -> bool {
    |s: RabbitmqReconcileState| s.reconcile_step == step
}

pub open spec fn after_create_k_request_step(sub_resource: SubResource) -> RabbitmqReconcileStep {
    RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource)
}

pub open spec fn after_update_k_request_step(sub_resource: SubResource) -> RabbitmqReconcileStep {
    RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource)
}

pub open spec fn pending_req_in_flight_at_after_get_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, rabbitmq)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_get_k_request_step(sub_resource);
        let request = req_msg.content.get_APIRequest_0();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg_is(s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& req_msg.dst == HostId::KubernetesAPI
        &&& req_msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, rabbitmq)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_get_resource_step_and_key_exists(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        &&& s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        &&& req_msg_is_the_in_flight_pending_req_at_after_get_resource_step(sub_resource, rabbitmq, req_msg)(s)
    }
}

pub open spec fn at_after_get_resource_step_and_exists_not_found_resp_in_flight(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, rabbitmq)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_response().res.is_Err()
            &&& resp_msg.content.get_get_response().res.get_Err_0().is_ObjectNotFound()
        }
    }
}

pub open spec fn at_after_get_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, rabbitmq)
        &&& s.resources().contains_key(key)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_get_response().res.is_Ok()
            &&& resp_msg.content.get_get_response().res.get_Ok_0() == s.resources()[key]
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_get_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: RMQMessage
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, rabbitmq)
        &&& s.resources().contains_key(key)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_get_response().res.is_Ok()
        &&& resp_msg.content.get_get_response().res.get_Ok_0() == s.resources()[key]
    }
}

pub open spec fn resp_msg_is_the_in_flight_resp_at_after_get_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: RMQMessage
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_get_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, rabbitmq)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
    }
}

pub open spec fn resource_create_request_msg(key: ObjectRef) -> FnSpec(RMQMessage) -> bool {
    |msg: RMQMessage|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_create_request()
        && msg.content.get_create_request().namespace == key.namespace
        && msg.content.get_create_request().obj.metadata.name == Some(key.name)
        && msg.content.get_create_request().obj.kind == key.kind
}

pub open spec fn resource_update_request_msg(key: ObjectRef) -> FnSpec(RMQMessage) -> bool {
    |msg: RMQMessage|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_update_request()
        && msg.content.get_update_request().key() == key
}

pub open spec fn pending_req_in_flight_at_after_create_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_create_k_request_step(sub_resource);
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg_is(s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(req_msg)
    }
}

pub open spec fn at_after_create_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_create_request_msg(key)(msg)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_create_response().res.is_Ok()
            &&& state_after_create_or_update(sub_resource, resp_msg.content.get_create_response().res.get_Ok_0(), s.ongoing_reconciles()[rabbitmq.object_ref()].local_state).is_Ok()
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_create_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: RMQMessage
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_create_request_msg(key)(msg)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_create_response().res.is_Ok()
        &&& state_after_create_or_update(sub_resource, resp_msg.content.get_create_response().res.get_Ok_0(), s.ongoing_reconciles()[rabbitmq.object_ref()].local_state).is_Ok()
    }
}

pub open spec fn pending_req_in_flight_at_after_update_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_update_k_request_step(sub_resource);
        let resource_key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg_is(s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(req_msg)
        &&& req_msg.src == HostId::CustomController
        &&& resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(req_msg)
    }
}

pub open spec fn at_after_update_resource_step_and_exists_ok_resp_in_flight(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_update_request_msg(key)(msg)
        &&& exists |resp_msg| {
            &&& #[trigger] s.in_flight().contains(resp_msg)
            &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
            &&& resp_msg.content.get_update_response().res.is_Ok()
            &&& state_after_create_or_update(sub_resource, resp_msg.content.get_update_response().res.get_Ok_0(), s.ongoing_reconciles()[rabbitmq.object_ref()].local_state).is_Ok()
        }
    }
}

pub open spec fn resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resp_msg: RMQMessage
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_update_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        let key = get_request(sub_resource, rabbitmq).key;
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& msg.src == HostId::CustomController
        &&& resource_update_request_msg(key)(msg)
        &&& s.in_flight().contains(resp_msg)
        &&& Message::resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg.content.get_update_response().res.is_Ok()
        &&& state_after_create_or_update(sub_resource, resp_msg.content.get_update_response().res.get_Ok_0(), s.ongoing_reconciles()[rabbitmq.object_ref()].local_state).is_Ok()
    }
}

}
