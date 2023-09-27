// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, error::*, owner_reference::*, resource::*,
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

pub open spec fn object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(key: ObjectRef, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
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

pub open spec fn resource_create_request_msg(key: ObjectRef) -> FnSpec(RMQMessage) -> bool {
    |msg: RMQMessage|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_create_request()
        && msg.content.get_create_request().namespace == key.namespace
        && msg.content.get_create_request().obj.metadata.name.get_Some_0() == key.name
        && msg.content.get_create_request().obj.kind == key.kind
}

pub open spec fn resource_update_request_msg(key: ObjectRef) -> FnSpec(RMQMessage) -> bool {
    |msg: RMQMessage|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_update_request()
        && msg.content.get_update_request().key() == key
}

pub open spec fn every_resource_object_in_create_request_does_the_make_method(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let resource_key = get_request(sub_resource, rabbitmq).key;
        let made_object = make(sub_resource, rabbitmq, s.ongoing_reconciles()[key].local_state);
        forall |msg: RMQMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& resource_create_request_msg(resource_key)(msg)
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
            &&& RMQCluster::pending_k8s_api_req_msg(s, key)
            &&& msg == s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()
            &&& made_object.is_Ok()
            &&& msg.content.get_create_request().obj == made_object.get_Ok_0()
        }
            // A reminder: The last predicate implies:
            // && msg.content.get_create_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    }
}

/// We have to impose constraint on the resource version of update request message now instead of making no distinction
/// to update request messages before. This is because we don't update the whole spec/data for the object now (we only update
/// part of the fields).
///
/// Note that in order to prove this invariant, we should take advantage of every get response message, if with the same rv,
/// has the same object as etcd.
///
/// Also, with the invariant proved, we also need to prove for every resource builder, (!!at the update step!!) the updated object
/// (as long as the non-metadata part) matches the desired state.
pub open spec fn every_resource_object_in_update_request_does_the_update_method(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        rabbitmq.well_formed(),
{
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let resource_key = get_request(sub_resource, rabbitmq).key;
        let resources = s.resources();
        let updated_obj = update(sub_resource, rabbitmq, s.ongoing_reconciles()[key].local_state, resources[resource_key]);
        forall |msg: RMQMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& resource_update_request_msg(resource_key)(msg)
            &&& resources.contains_key(resource_key)
            &&& msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() == resources[resource_key].metadata.resource_version.get_Some_0()
        } ==> {
            &&& at_rabbitmq_step(key, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& RMQCluster::pending_k8s_api_req_msg(s, key)
            &&& msg == s.ongoing_reconciles()[key].pending_req_msg.get_Some_0()
            &&& updated_obj.is_Ok()
            &&& msg.content.get_update_request().obj == updated_obj.get_Ok_0()
        }
            // A reminder: The last predicate implies:
            // && msg.content.get_update_request().obj.metadata.owner_references == Some(seq![rabbitmq.controller_owner_ref()])
    }
}

pub open spec fn object_of_key_only_has_owner_reference_pointing_to_current_cr(key: ObjectRef, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
    }
}

pub open spec fn no_delete_request_msg_in_flight_with_key(key: ObjectRef) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |msg: RMQMessage| !{
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst.is_KubernetesAPI()
            &&& msg.content.is_delete_request()
            &&& msg.content.get_delete_request().key == key
        }
    }
}

}
