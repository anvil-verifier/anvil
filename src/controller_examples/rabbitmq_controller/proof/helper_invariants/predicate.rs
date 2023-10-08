// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, error::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::{predicate::*, resource::*},
    spec::{reconciler::*, types::*},
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub open spec fn the_object_in_reconcile_satisfies_state_validation() -> StatePred<RMQCluster>
{
    |s: RMQCluster| {
        forall |key: ObjectRef|
        #[trigger] s.ongoing_reconciles().contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> s.ongoing_reconciles()[key].triggering_cr.state_validation()
    }
}

pub open spec fn the_object_in_schedule_satisfies_state_validation() -> StatePred<RMQCluster>
{
    |s: RMQCluster| {
        forall |key: ObjectRef|
        #[trigger] s.scheduled_reconciles().contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> s.scheduled_reconciles()[key].state_validation()
    }
}

pub open spec fn cr_objects_in_etcd_satisfy_state_validation() -> StatePred<RMQCluster>
{
    |s: RMQCluster| {
        forall |key: ObjectRef|
        #[trigger] s.resources().contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> RabbitmqClusterView::unmarshal(s.resources()[key]).is_Ok()
            && RabbitmqClusterView::unmarshal(s.resources()[key]).get_Ok_0().state_validation()
    }
}

pub open spec fn resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    let key = get_request(sub_resource, rabbitmq).key;
    |s: RMQCluster| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.deletion_timestamp.is_None()
            && s.resources()[key].metadata.finalizers.is_None()
            && exists |uid: Uid| #![auto]
            s.resources()[key].metadata.owner_references == Some(seq![OwnerReferenceView {
                block_owner_deletion: None,
                controller: Some(true),
                kind: RabbitmqClusterView::kind(),
                name: rabbitmq.metadata.name.get_Some_0(),
                uid: uid,
            }])
    }
}

pub open spec fn resource_get_response_msg(key: ObjectRef) -> FnSpec(RMQMessage) -> bool {
    |msg: RMQMessage|
        msg.src.is_KubernetesAPI()
        && msg.content.is_get_response()
        && (
            msg.content.get_get_response().res.is_Ok()
            ==> msg.content.get_get_response().res.get_Ok_0().object_ref() == key
        )
}

pub open spec fn resource_update_response_msg(key: ObjectRef, s: RMQCluster) -> FnSpec(RMQMessage) -> bool {
    |msg: RMQMessage|
        msg.src.is_KubernetesAPI()
        && msg.content.is_update_response()
        && (
            msg.content.get_update_response().res.is_Ok()
            ==> (
                s.resources().contains_key(key)
                && msg.content.get_update_response().res.get_Ok_0() == s.resources()[key]
            )
        )
}

/// This spec tells that when the reconciler is at AfterGetStatefulSet, and there is a matched response, the reponse must be
/// sts_get_response_msg. This lemma is used to show that the response message, if is ok, has an object whose reference is
/// stateful_set_key. resp_msg_matches_req_msg doesn't talk about the object in response should match the key in request
/// so we need this extra spec and lemma.
///
/// If we don't have this, we have no idea of what is inside the response message.
pub open spec fn response_at_after_get_resource_step_is_resource_get_response(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    |s: RMQCluster| {
        at_rabbitmq_step(key, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
        ==> s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && resource_get_request_msg(resource_key)(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            && (
                forall |msg: RMQMessage|
                    #[trigger] s.in_flight().contains(msg)
                    && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
                    ==> resource_get_response_msg(resource_key)(msg)
            )
    }
}

pub open spec fn object_in_response_at_after_get_update_step_is_same_as_etcd(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    |s: RMQCluster| {
        let pending_req = s.ongoing_reconciles()[key].pending_req_msg.get_Some_0();

        at_rabbitmq_step(key, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
        ==> s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && resource_update_request_msg(resource_key)(pending_req)
            && (
                forall |msg: RMQMessage|
                    #[trigger] s.in_flight().contains(msg)
                    && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
                    ==> resource_update_response_msg(resource_key, s)(msg)
            )
    }
}

pub open spec fn object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let resource_key = get_request(sub_resource, rabbitmq).key;
        forall |msg: RMQMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& resource_update_request_msg(resource_key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& RMQCluster::pending_k8s_api_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
        }
    }
}

pub open spec fn every_resource_create_request_implies_at_after_create_resource_step(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let resource_key = get_request(sub_resource, rabbitmq).key;
        forall |msg: RMQMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& resource_create_request_msg(resource_key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
            &&& RMQCluster::pending_k8s_api_req_msg_is(s, key, msg)
            &&& make(sub_resource, rabbitmq, s.ongoing_reconciles()[key].local_state).is_Ok()
            &&& msg.content.get_create_request().obj == make(sub_resource, rabbitmq, s.ongoing_reconciles()[key].local_state).get_Ok_0()
        }
    }
}

pub open spec fn every_resource_update_request_implies_at_after_update_resource_step(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let resource_key = get_request(sub_resource, rabbitmq).key;
        forall |msg: RMQMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& resource_update_request_msg(resource_key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& RMQCluster::pending_k8s_api_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.resource_version.is_Some()
            &&& msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
            &&& (
                s.resources().contains_key(resource_key)
                && msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
            ) ==> (
                update(sub_resource, rabbitmq, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).is_Ok()
                && msg.content.get_update_request().obj == update(sub_resource, rabbitmq, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).get_Ok_0()
            )
        }
    }
}

pub open spec fn resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    let key = get_request(sub_resource, rabbitmq).key;
    |s: RMQCluster| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
    }
}

pub open spec fn no_delete_request_msg_in_flight_of(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |msg: RMQMessage| !{
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst.is_KubernetesAPI()
            &&& msg.content.is_delete_request()
            &&& msg.content.get_delete_request().key == get_request(sub_resource, rabbitmq).key
        }
    }
}

pub open spec fn no_update_status_request_msg_in_flight_of(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |msg: RMQMessage| //#![trigger s.in_flight().contains(msg), msg.content.is_update_status_request()]
            #[trigger] s.in_flight().contains(msg)
            // && msg.dst.is_KubernetesAPI()
            && msg.content.is_update_status_request()
            ==> msg.content.get_update_status_request().key() != get_request(sub_resource, rabbitmq).key
    }
}

/// We only need it for AfterGetStatefulSet, but keeping all the steps makes the invariant easier to prove.
pub open spec fn cm_rv_is_some_after_cm_is_updated(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let local_state = s.ongoing_reconciles()[key].local_state;
        s.ongoing_reconciles().contains_key(key)
        ==> match local_state.reconcile_step {
            RabbitmqReconcileStep::AfterKRequestStep(_, sub_resource) => {
                match sub_resource {
                    SubResource::ServiceAccount | SubResource::Role | SubResource::RoleBinding | SubResource::StatefulSet => {
                        local_state.latest_config_map_rv_opt.is_Some()
                    },
                    _ => true,
                }
            }
            _ => true,
        }
    }
}

/// We only need it for AfterGetStatefulSet, but keeping all the steps makes the invariant easier to prove.
pub open spec fn cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let local_state = s.ongoing_reconciles()[key].local_state;
        s.ongoing_reconciles().contains_key(key)
        ==> match local_state.reconcile_step {
            RabbitmqReconcileStep::AfterKRequestStep(_, sub_resource) => {
                match sub_resource {
                    SubResource::ServiceAccount | SubResource::Role | SubResource::RoleBinding | SubResource::StatefulSet => {
                        let cm_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
                        &&& s.resources().contains_key(cm_key)
                        &&& s.resources()[cm_key].metadata.resource_version.is_Some()
                        &&& local_state.latest_config_map_rv_opt == Some(int_to_string_view(s.resources()[cm_key].metadata.resource_version.get_Some_0()))
                    },
                    _ => true,
                }
            }
            _ => true,
        }
    }
}

pub open spec fn object_in_etcd_satisfies_unchangeable(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        s.resources().contains_key(get_request(sub_resource, rabbitmq).key)
        ==> unchangeable(sub_resource, s.resources()[get_request(sub_resource, rabbitmq).key], rabbitmq)
    }
}

pub open spec fn cm_rv_stays_unchanged(rabbitmq: RabbitmqClusterView) -> ActionPred<RMQCluster> {
    |s: RMQCluster, s_prime: RMQCluster| {
        let cm_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
        &&& s.resources().contains_key(cm_key)
        &&& s_prime.resources().contains_key(cm_key)
        &&& s.resources()[cm_key].metadata.resource_version.is_Some()
        &&& s.resources()[cm_key].metadata.resource_version == s_prime.resources()[cm_key].metadata.resource_version
    }
}

}
