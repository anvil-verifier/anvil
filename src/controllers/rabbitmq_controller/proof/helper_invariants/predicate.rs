// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    model::reconciler::*,
    proof::{predicate::*, resource::*},
    trusted::{spec_types::*, step::*},
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub open spec fn rabbitmq_is_well_formed(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| rabbitmq.well_formed()
}

pub open spec fn resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    let key = get_request(sub_resource, rabbitmq).key;
    |s: ClusterState| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.deletion_timestamp is None
            && s.resources()[key].metadata.finalizers is None
            && exists |uid: Uid| #![auto]
            s.resources()[key].metadata.owner_references == Some(seq![OwnerReferenceView {
                block_owner_deletion: None,
                controller: Some(true),
                kind: RabbitmqClusterView::kind(),
                name: rabbitmq.metadata.name->0,
                uid: uid,
            }])
    }
}

pub open spec fn resource_get_response_msg(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.src is APIServer
        && msg.content.is_get_response()
        && (
            msg.content.get_get_response().res is Ok
            ==> msg.content.get_get_response().res->Ok_0.object_ref() == key
        )
}

pub open spec fn resource_update_response_msg(key: ObjectRef, s: ClusterState) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.src is APIServer
        && msg.content.is_update_response()
        && (
            msg.content.get_update_response().res is Ok
            ==> (
                s.resources().contains_key(key)
                && msg.content.get_update_response().res->Ok_0 == s.resources()[key]
            )
        )
}

pub open spec fn resource_create_response_msg(key: ObjectRef, s: ClusterState) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.src is APIServer
        && msg.content.is_create_response()
        && (
            msg.content.get_create_response().res is Ok
            ==> (
                s.resources().contains_key(key)
                && msg.content.get_create_response().res->Ok_0 == s.resources()[key]
            )
        )
}

// This spec tells that when the reconciler is at AfterGetStatefulSet, and there is a matched response, the reponse must be
// sts_get_response_msg. This lemma is used to show that the response message, if is ok, has an object whose reference is
// stateful_set_key. resp_msg_matches_req_msg doesn't talk about the object in response should match the key in request
// so we need this extra spec and lemma.
//
// If we don't have this, we have no idea of what is inside the response message.
pub open spec fn response_at_after_get_resource_step_is_resource_get_response(
    controller_id: int,
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<ClusterState> {
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    |s: ClusterState| {
        at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
        ==> s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
            && resource_get_request_msg(resource_key)(s.ongoing_reconciles(controller_id)[key].pending_req_msg->0)
            && (
                forall |msg: Message|
                    #[trigger] s.in_flight().contains(msg)
                    && resp_msg_matches_req_msg(msg, s.ongoing_reconciles(controller_id)[key].pending_req_msg->0)
                    ==> resource_get_response_msg(resource_key)(msg)
            )
    }
}

pub open spec fn request_at_after_get_request_step_is_resource_get_request(
    controller_id: int,
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<ClusterState> {
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    |s: ClusterState| {
        at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
        ==> s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
            && resource_get_request_msg(resource_key)(s.ongoing_reconciles(controller_id)[key].pending_req_msg->0)
    }
}

pub open spec fn object_in_response_at_after_update_resource_step_is_same_as_etcd(
    controller_id: int,
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<ClusterState> {
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    |s: ClusterState| {
        let pending_req = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;

        at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
        ==> s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
            && resource_update_request_msg(resource_key)(pending_req)
            && (
                forall |msg: Message|
                    #[trigger] s.in_flight().contains(msg)
                    && resp_msg_matches_req_msg(msg, s.ongoing_reconciles(controller_id)[key].pending_req_msg->0)
                    ==> resource_update_response_msg(resource_key, s)(msg)
            )
    }
}

pub open spec fn object_in_response_at_after_create_resource_step_is_same_as_etcd(
    controller_id: int,
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<ClusterState> {
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    |s: ClusterState| {
        let pending_req = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;

        at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
        ==> s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
            && resource_create_request_msg(resource_key)(pending_req)
            && (
                forall |msg: Message|
                    #[trigger] s.in_flight().contains(msg)
                    && resp_msg_matches_req_msg(msg, s.ongoing_reconciles(controller_id)[key].pending_req_msg->0)
                    ==> resource_create_response_msg(resource_key, s)(msg)
            )
    }
}

pub open spec fn object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id: int, sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = rabbitmq.object_ref();
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
        }
    }
}

pub open spec fn every_resource_create_request_implies_at_after_create_resource_step(controller_id: int, sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = rabbitmq.object_ref();
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
            &&& make(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap()) is Ok
            &&& msg.content.get_create_request().obj == make(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap())->Ok_0
        }
    }
}

pub open spec fn every_resource_update_request_implies_at_after_update_resource_step(controller_id: int, sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = rabbitmq.object_ref();
        let resource_key = get_request(sub_resource, rabbitmq).key;
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.resource_version is Some
            &&& msg.content.get_update_request().obj.metadata.resource_version->0 < s.api_server.resource_version_counter
            &&& (
                s.resources().contains_key(resource_key)
                && msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
            ) ==> (
                update(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap(), s.resources()[resource_key]) is Ok
                && msg.content.get_update_request().obj == update(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap(), s.resources()[resource_key])->Ok_0
            )
        }
    }
}

pub open spec fn resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    let key = get_request(sub_resource, rabbitmq).key;
    |s: ClusterState| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
    }
}

pub open spec fn no_create_resource_request_msg_without_name_in_flight(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    let resource_key = get_request(sub_resource, rabbitmq).key;
    Cluster::no_create_msg_that_uses_generate_name(resource_key.kind, resource_key.namespace)
}

pub open spec fn no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #[trigger] s.in_flight().contains(msg)
        ==> !{
            ||| resource_delete_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
            ||| resource_get_then_delete_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
            ||| resource_get_then_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
            ||| resource_get_then_update_status_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
        }
    }
}

pub open spec fn no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        sub_resource != SubResource::VStatefulSetView
        ==> {
            forall |msg: Message|
                #[trigger] s.in_flight().contains(msg)
                ==> !(resource_update_status_request_msg(get_request(sub_resource, rabbitmq).key)(msg))
        }
    }
}

pub open spec fn no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(controller_id: int, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg)
            && msg.dst is APIServer
            && !(msg.src is BuiltinController)
            ==> !resource_update_status_request_msg(get_request(SubResource::VStatefulSetView, rabbitmq).key)(msg)
    }
}

// We only need it for AfterGetStatefulSet, but keeping all the steps makes the invariant easier to prove.
pub open spec fn cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id: int, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = rabbitmq.object_ref();
        let local_state = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
        s.ongoing_reconciles(controller_id).contains_key(key)
        ==> match local_state.reconcile_step {
            RabbitmqReconcileStep::AfterKRequestStep(_, sub_resource) => {
                match sub_resource {
                    SubResource::ServiceAccount | SubResource::Role | SubResource::RoleBinding | SubResource::VStatefulSetView => {
                        let cm_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
                        &&& s.resources().contains_key(cm_key)
                        &&& s.resources()[cm_key].metadata.resource_version is Some
                        &&& local_state.latest_config_map_rv_opt == Some(int_to_string_view(s.resources()[cm_key].metadata.resource_version->0))
                    },
                    _ => true,
                }
            }
            _ => true,
        }
    }
}

pub open spec fn object_in_etcd_satisfies_unchangeable(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        ==> unchangeable(sub_resource, s.resources()[get_request(sub_resource, rabbitmq).key], rabbitmq)
    }
}

pub open spec fn cm_rv_stays_unchanged(rabbitmq: RabbitmqClusterView) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        let cm_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
        &&& s.resources().contains_key(cm_key)
        &&& s_prime.resources().contains_key(cm_key)
        &&& s.resources()[cm_key].metadata.resource_version is Some
        &&& s.resources()[cm_key].metadata.resource_version == s_prime.resources()[cm_key].metadata.resource_version
    }
}

pub open spec fn stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id: int, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let sts_key = get_request(SubResource::VStatefulSetView, rabbitmq).key;
        ||| !s.resources().contains_key(sts_key)
        ||| sub_resource_state_matches(SubResource::VStatefulSetView, rabbitmq, controller_id)(s)
        ||| {
            &&& forall |msg: Message|
                    #[trigger] s.in_flight().contains(msg)
                    ==> !(resource_update_status_request_msg(get_request(SubResource::VStatefulSetView, rabbitmq).key)(msg))
        }
    }
}

}
