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

pub open spec fn valid_created_obj(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, s: RMQCluster) -> bool {
    let created_obj = DynamicObjectView {
        kind: obj.kind,
        metadata: ObjectMetaView {
            namespace: Some(rabbitmq.metadata.namespace.get_Some_0()), // Set namespace for new object
            resource_version: Some(s.kubernetes_api_state.resource_version_counter), // Set rv for new object
            uid: Some(s.kubernetes_api_state.uid_counter), // Set uid for new object
            deletion_timestamp: None, // Unset deletion timestamp for new object
            ..obj.metadata
        },
        spec: obj.spec,
        status: RMQCluster::marshalled_default_status(obj), // Overwrite the status with the default one
    };
    &&& obj.metadata.name.is_Some()
    &&& obj.metadata.namespace.is_Some()
    &&& obj.metadata.namespace.get_Some_0() == rabbitmq.metadata.namespace.get_Some_0()
    &&& obj.object_ref() == get_request(sub_resource, rabbitmq).key
    &&& !RMQCluster::unmarshallable_object(obj)
    &&& RMQCluster::created_object_validity_check(created_obj).is_None()
    &&& resource_state_matches(sub_resource, rabbitmq, s.resources().insert(created_obj.object_ref(), created_obj))
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
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg_is(s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_APIRequest()
        &&& request.is_GetRequest()
        &&& request.get_GetRequest_0() == get_request(sub_resource, rabbitmq)
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

pub open spec fn pending_req_in_flight_at_after_create_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_APIRequest()
        &&& request.is_CreateRequest()
        &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
        &&& valid_created_obj(sub_resource, rabbitmq, request.get_CreateRequest_0().obj, s)
    }
}

pub open spec fn req_msg_is_the_in_flight_pending_req_at_after_create_resource_step(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let step = after_create_k_request_step(sub_resource);
        let msg = s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0();
        let request = msg.content.get_APIRequest_0();
        &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
        &&& RMQCluster::pending_k8s_api_req_msg_is(s, rabbitmq.object_ref(), req_msg)
        &&& s.in_flight().contains(msg)
        &&& msg.src == HostId::CustomController
        &&& msg.dst == HostId::KubernetesAPI
        &&& msg.content.is_APIRequest()
        &&& request.is_CreateRequest()
        &&& request.get_CreateRequest_0().namespace == rabbitmq.metadata.namespace.get_Some_0()
        &&& valid_created_obj(sub_resource, rabbitmq, request.get_CreateRequest_0().obj, s)
    }
}

// pub open spec fn pending_req_in_flight_at_rabbitmq_step_with_rabbitmq(
//     step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView
// ) -> StatePred<RMQCluster> {
//     |s: RMQCluster| {
//         &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
//         &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
//         &&& s.in_flight().contains(s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
//         &&& is_correct_pending_request_msg_at_rabbitmq_step(step, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq, s.ongoing_reconciles()[rabbitmq.object_ref()].local_state)
//     }
// }

// pub open spec fn pending_req_with_object_in_flight_at_rabbitmq_step_with_rabbitmq(
//     step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, object: DynamicObjectView
// ) -> StatePred<RMQCluster> {
//     |s: RMQCluster| {
//         &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
//         &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
//         &&& s.in_flight().contains(s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
//         &&& is_correct_pending_request_msg_with_object_at_rabbitmq_step(step, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq, object)
//     }
// }

// pub open spec fn req_msg_is_the_in_flight_pending_req_at_rabbitmq_step_with_rabbitmq(
//     step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage
// ) -> StatePred<RMQCluster> {
//     |s: RMQCluster| {
//         &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
//         &&& RMQCluster::pending_k8s_api_req_msg_is(s, rabbitmq.object_ref(), req_msg)
//         &&& s.in_flight().contains(req_msg)
//         &&& is_correct_pending_request_msg_at_rabbitmq_step(step, req_msg, rabbitmq, s.ongoing_reconciles()[rabbitmq.object_ref()].local_state)
//     }
// }

// pub open spec fn req_msg_is_the_in_flight_pending_req_with_object_at_rabbitmq_step_with_rabbitmq(
//     step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, req_msg: RMQMessage, object: DynamicObjectView
// ) -> StatePred<RMQCluster> {
//     |s: RMQCluster| {
//         &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
//         &&& RMQCluster::pending_k8s_api_req_msg_is(s, rabbitmq.object_ref(), req_msg)
//         &&& s.in_flight().contains(req_msg)
//         &&& is_correct_pending_request_msg_with_object_at_rabbitmq_step(step, req_msg, rabbitmq, object)
//     }
// }

// pub open spec fn exists_resp_in_flight_at_rabbitmq_step_with_rabbitmq(
//     step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView
// ) -> StatePred<RMQCluster> {
//     |s: RMQCluster| {
//         &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
//         &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
//         &&& is_correct_pending_request_msg_at_rabbitmq_step(step, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq, s.ongoing_reconciles()[rabbitmq.object_ref()].local_state)
//         &&& exists |resp_msg| {
//             &&& #[trigger] s.in_flight().contains(resp_msg)
//             &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
//         }
//     }
// }

// pub open spec fn resp_msg_is_the_in_flight_resp_at_rabbitmq_step_with_rabbitmq(
//     step: RabbitmqReconcileStep, rabbitmq: RabbitmqClusterView, resp_msg: RMQMessage
// ) -> StatePred<RMQCluster> {
//     |s: RMQCluster| {
//         &&& at_rabbitmq_step_with_rabbitmq(rabbitmq, step)(s)
//         &&& RMQCluster::pending_k8s_api_req_msg(s, rabbitmq.object_ref())
//         &&& is_correct_pending_request_msg_at_rabbitmq_step(step, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0(), rabbitmq, s.ongoing_reconciles()[rabbitmq.object_ref()].local_state)
//         &&& s.in_flight().contains(resp_msg)
//         &&& Message::resp_msg_matches_req_msg(resp_msg, s.ongoing_reconciles()[rabbitmq.object_ref()].pending_req_msg.get_Some_0())
//     }
// }

}
