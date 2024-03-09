// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use crate::zookeeper_controller::{
    model::reconciler::*,
    proof::{predicate::*, resource::*},
    trusted::{spec_types::*, step::*},
};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub open spec fn zookeeper_is_well_formed(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| zookeeper.well_formed()
}

pub open spec fn the_object_in_reconcile_satisfies_state_validation(key: ObjectRef) -> StatePred<ZKCluster>
{
    |s: ZKCluster| {
        s.ongoing_reconciles().contains_key(key)
        ==> s.ongoing_reconciles()[key].triggering_cr.state_validation()
    }
}

pub open spec fn the_object_in_schedule_satisfies_state_validation() -> StatePred<ZKCluster>
{
    |s: ZKCluster| {
        forall |key: ObjectRef|
        #[trigger] s.scheduled_reconciles().contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> s.scheduled_reconciles()[key].state_validation()
    }
}

pub open spec fn cr_objects_in_etcd_satisfy_state_validation() -> StatePred<ZKCluster>
{
    |s: ZKCluster| {
        forall |key: ObjectRef|
        #[trigger] s.resources().contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> ZookeeperClusterView::unmarshal(s.resources()[key]).is_Ok()
            && ZookeeperClusterView::unmarshal(s.resources()[key]).get_Ok_0().state_validation()
    }
}

pub open spec fn resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    let key = get_request(sub_resource, zookeeper).key;
    |s: ZKCluster| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.deletion_timestamp.is_None()
            && s.resources()[key].metadata.finalizers.is_None()
            && exists |uid: Uid| #![auto]
            s.resources()[key].metadata.owner_references == Some(seq![OwnerReferenceView {
                block_owner_deletion: None,
                controller: Some(true),
                kind: ZookeeperClusterView::kind(),
                name: zookeeper.metadata.name.get_Some_0(),
                uid: uid,
            }])
    }
}

pub open spec fn resource_get_response_msg(key: ObjectRef) -> spec_fn(ZKMessage) -> bool {
    |msg: ZKMessage|
        msg.src.is_ApiServer()
        && msg.content.is_get_response()
        && (
            msg.content.get_get_response().res.is_Ok()
            ==> msg.content.get_get_response().res.get_Ok_0().object_ref() == key
        )
}

pub open spec fn resource_update_response_msg(key: ObjectRef, s: ZKCluster) -> spec_fn(ZKMessage) -> bool {
    |msg: ZKMessage|
        msg.src.is_ApiServer()
        && msg.content.is_update_response()
        && (
            msg.content.get_update_response().res.is_Ok()
            ==> (
                s.resources().contains_key(key)
                && msg.content.get_update_response().res.get_Ok_0() == s.resources()[key]
            )
        )
}

pub open spec fn resource_create_response_msg(key: ObjectRef, s: ZKCluster) -> spec_fn(ZKMessage) -> bool {
    |msg: ZKMessage|
        msg.src.is_ApiServer()
        && msg.content.is_create_response()
        && (
            msg.content.get_create_response().res.is_Ok()
            ==> (
                s.resources().contains_key(key)
                && msg.content.get_create_response().res.get_Ok_0() == s.resources()[key]
            )
        )
}

pub open spec fn response_at_after_get_resource_step_is_resource_get_response(
    sub_resource: SubResource, zookeeper: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    let key = zookeeper.object_ref();
    let resource_key = get_request(sub_resource, zookeeper).key;
    |s: ZKCluster| {
        at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
        ==> s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && resource_get_request_msg(resource_key)(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            && (
                forall |msg: ZKMessage|
                    #[trigger] s.in_flight().contains(msg)
                    && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
                    ==> resource_get_response_msg(resource_key)(msg)
            )
    }
}

pub open spec fn object_in_response_at_after_update_resource_step_is_same_as_etcd(
    sub_resource: SubResource, zookeeper: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    let key = zookeeper.object_ref();
    let resource_key = get_request(sub_resource, zookeeper).key;
    |s: ZKCluster| {
        let pending_req = s.ongoing_reconciles()[key].pending_req_msg.get_Some_0();

        at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
        ==> s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && resource_update_request_msg(resource_key)(pending_req)
            && (
                forall |msg: ZKMessage|
                    #[trigger] s.in_flight().contains(msg)
                    && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
                    ==> resource_update_response_msg(resource_key, s)(msg)
            )
    }
}

pub open spec fn object_in_response_at_after_create_resource_step_is_same_as_etcd(
    sub_resource: SubResource, zookeeper: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    let key = zookeeper.object_ref();
    let resource_key = get_request(sub_resource, zookeeper).key;
    |s: ZKCluster| {
        let pending_req = s.ongoing_reconciles()[key].pending_req_msg.get_Some_0();

        at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
        ==> s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && resource_create_request_msg(resource_key)(pending_req)
            && (
                forall |msg: ZKMessage|
                    #[trigger] s.in_flight().contains(msg)
                    && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
                    ==> resource_create_response_msg(resource_key, s)(msg)
            )
    }
}

pub open spec fn object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = zookeeper.object_ref();
        forall |msg: ZKMessage| {
            &&& s.in_flight().contains(msg)
            &&& #[trigger] resource_update_request_msg(get_request(sub_resource, zookeeper).key)(msg)
        } ==> {
            &&& at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& ZKCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.owner_references_only_contains(zookeeper.controller_owner_ref())
        }
    }
}

pub open spec fn every_resource_create_request_implies_at_after_create_resource_step(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = zookeeper.object_ref();
        forall |msg: ZKMessage| {
            &&& s.in_flight().contains(msg)
            &&& #[trigger] resource_create_request_msg(get_request(sub_resource, zookeeper).key)(msg)
        } ==> {
            &&& at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
            &&& ZKCluster::pending_req_msg_is(s, key, msg)
            &&& make(sub_resource, zookeeper, s.ongoing_reconciles()[key].local_state).is_Ok()
            &&& msg.content.get_create_request().obj == make(sub_resource, zookeeper, s.ongoing_reconciles()[key].local_state).get_Ok_0()
        }
    }
}

pub open spec fn every_resource_update_request_implies_at_after_update_resource_step(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = zookeeper.object_ref();
        let resource_key = get_request(sub_resource, zookeeper).key;
        forall |msg: ZKMessage| {
            &&& s.in_flight().contains(msg)
            &&& #[trigger] resource_update_request_msg(get_request(sub_resource, zookeeper).key)(msg)
        } ==> {
            &&& at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& ZKCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.resource_version.is_Some()
            &&& msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
            &&& (
                s.resources().contains_key(resource_key)
                && msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
            ) ==> (
                update(sub_resource, zookeeper, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).is_Ok()
                && msg.content.get_update_request().obj == update(sub_resource, zookeeper, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).get_Ok_0()
            )
        }
    }
}

pub open spec fn resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    let key = get_request(sub_resource, zookeeper).key;
    |s: ZKCluster| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.owner_references_only_contains(zookeeper.controller_owner_ref())
    }
}

pub open spec fn no_delete_resource_request_msg_in_flight(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        forall |msg: ZKMessage| !{
            &&& s.in_flight().contains(msg)
            &&& #[trigger] resource_delete_request_msg(get_request(sub_resource, zookeeper).key)(msg)
        }
    }
}

pub open spec fn no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        sub_resource != SubResource::StatefulSet
        ==> {
            forall |msg: ZKMessage|
                #[trigger] s.in_flight().contains(msg)
                ==> !(#[trigger] resource_update_status_request_msg(get_request(sub_resource, zookeeper).key)(msg))
        }
    }
}

pub open spec fn no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        forall |msg: ZKMessage|
            #[trigger] s.in_flight().contains(msg)
            && msg.dst.is_ApiServer()
            && !msg.src.is_BuiltinController()
            ==> !resource_update_status_request_msg(get_request(SubResource::StatefulSet, zookeeper).key)(msg)
    }
}

pub open spec fn cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = zookeeper.object_ref();
        let local_state = s.ongoing_reconciles()[key].local_state;
        s.ongoing_reconciles().contains_key(key)
        ==> match local_state.reconcile_step {
            ZookeeperReconcileStep::AfterKRequestStep(_, sub_resource) => {
                match sub_resource {
                    SubResource::StatefulSet => {
                        let cm_key = get_request(SubResource::ConfigMap, zookeeper).key;
                        &&& s.resources().contains_key(cm_key)
                        &&& s.resources()[cm_key].metadata.resource_version.is_Some()
                        &&& local_state.latest_config_map_rv_opt == Some(int_to_string_view(s.resources()[cm_key].metadata.resource_version.get_Some_0()))
                    },
                    _ => true,
                }
            }
            ZookeeperReconcileStep::AfterExistsStatefulSet | ZookeeperReconcileStep::AfterExistsZKNode | ZookeeperReconcileStep::AfterCreateZKParentNode | ZookeeperReconcileStep::AfterCreateZKNode | ZookeeperReconcileStep::AfterUpdateZKNode => {
                let cm_key = get_request(SubResource::ConfigMap, zookeeper).key;
                &&& s.resources().contains_key(cm_key)
                &&& s.resources()[cm_key].metadata.resource_version.is_Some()
                &&& local_state.latest_config_map_rv_opt == Some(int_to_string_view(s.resources()[cm_key].metadata.resource_version.get_Some_0()))
            }
            _ => true,
        }
    }
}

pub open spec fn object_in_etcd_satisfies_unchangeable(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        s.resources().contains_key(get_request(sub_resource, zookeeper).key)
        ==> unchangeable(sub_resource, s.resources()[get_request(sub_resource, zookeeper).key], zookeeper)
    }
}

pub open spec fn cm_rv_stays_unchanged(zookeeper: ZookeeperClusterView) -> ActionPred<ZKCluster> {
    |s: ZKCluster, s_prime: ZKCluster| {
        let cm_key = get_request(SubResource::ConfigMap, zookeeper).key;
        &&& s.resources().contains_key(cm_key)
        &&& s_prime.resources().contains_key(cm_key)
        &&& s.resources()[cm_key].metadata.resource_version.is_Some()
        &&& s.resources()[cm_key].metadata.resource_version == s_prime.resources()[cm_key].metadata.resource_version
    }
}

pub open spec fn stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
        ||| !s.resources().contains_key(sts_key)
        ||| sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s)
        ||| {
            &&& forall |msg: ZKMessage|
                s.in_flight().contains(msg)
                ==> !(#[trigger] resource_update_status_request_msg(get_request(SubResource::StatefulSet, zookeeper).key)(msg))
            &&& s.stable_resources().contains(sts_key)
        }
    }
}

}
