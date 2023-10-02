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
            &&& s.resources().contains_key(resource_key)
            &&& update(sub_resource, rabbitmq, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).is_Ok()
            &&& msg.content.get_update_request().obj == update(sub_resource, rabbitmq, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).get_Ok_0()
        }
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

pub open spec fn no_update_status_request_msg_in_flight_with_key(key: ObjectRef) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |msg: RMQMessage| !{
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst.is_KubernetesAPI()
            &&& msg.content.is_update_status_request()
            &&& msg.content.get_update_status_request().key() == key
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
