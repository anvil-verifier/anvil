// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::fluent_controller::fluentbit_config::{
    model::reconciler::*,
    proof::{predicate::*, resource::*},
    trusted::{spec_types::*, step::*},
};
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, owner_reference::*, resource::*, stateful_set::*,
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
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub open spec fn fbc_is_well_formed(fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| fbc.well_formed()
}

pub open spec fn the_object_in_reconcile_satisfies_state_validation(key: ObjectRef) -> StatePred<FBCCluster>
{
    |s: FBCCluster| {
        s.ongoing_reconciles().contains_key(key)
        ==> s.ongoing_reconciles()[key].triggering_cr.state_validation()
    }
}

pub open spec fn the_object_in_schedule_satisfies_state_validation() -> StatePred<FBCCluster>
{
    |s: FBCCluster| {
        forall |key: ObjectRef|
        #[trigger] s.scheduled_reconciles().contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> s.scheduled_reconciles()[key].state_validation()
    }
}

pub open spec fn cr_objects_in_etcd_satisfy_state_validation() -> StatePred<FBCCluster>
{
    |s: FBCCluster| {
        forall |key: ObjectRef|
        #[trigger] s.resources().contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> FluentBitConfigView::unmarshal(s.resources()[key]).is_Ok()
            && FluentBitConfigView::unmarshal(s.resources()[key]).get_Ok_0().state_validation()
    }
}

pub open spec fn resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    let key = get_request(sub_resource, fbc).key;
    |s: FBCCluster| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.deletion_timestamp.is_None()
            && s.resources()[key].metadata.finalizers.is_None()
            && exists |uid: Uid| #![auto]
            s.resources()[key].metadata.owner_references == Some(seq![OwnerReferenceView {
                block_owner_deletion: None,
                controller: Some(true),
                kind: FluentBitConfigView::kind(),
                name: fbc.metadata.name.get_Some_0(),
                uid: uid,
            }])
    }
}

pub open spec fn resource_get_response_msg(key: ObjectRef) -> spec_fn(FBCMessage) -> bool {
    |msg: FBCMessage|
        msg.src.is_ApiServer()
        && msg.content.is_get_response()
        && (
            msg.content.get_get_response().res.is_Ok()
            ==> msg.content.get_get_response().res.get_Ok_0().object_ref() == key
        )
}

pub open spec fn resource_update_response_msg(key: ObjectRef, s: FBCCluster) -> spec_fn(FBCMessage) -> bool {
    |msg: FBCMessage|
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

pub open spec fn resource_create_response_msg(key: ObjectRef, s: FBCCluster) -> spec_fn(FBCMessage) -> bool {
    |msg: FBCMessage|
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
    sub_resource: SubResource, fbc: FluentBitConfigView
) -> StatePred<FBCCluster> {
    let key = fbc.object_ref();
    let resource_key = get_request(sub_resource, fbc).key;
    |s: FBCCluster| {
        at_fbc_step(key, FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
        ==> s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && resource_get_request_msg(resource_key)(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            && (
                forall |msg: FBCMessage|
                    #[trigger] s.in_flight().contains(msg)
                    && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
                    ==> resource_get_response_msg(resource_key)(msg)
            )
    }
}

pub open spec fn object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let key = fbc.object_ref();
        let resource_key = get_request(sub_resource, fbc).key;
        forall |msg: FBCMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& resource_update_request_msg(resource_key)(msg)
        } ==> {
            &&& at_fbc_step(key, FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& FBCCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.owner_references_only_contains(fbc.controller_owner_ref())
        }
    }
}

pub open spec fn every_resource_create_request_implies_at_after_create_resource_step(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let key = fbc.object_ref();
        let resource_key = get_request(sub_resource, fbc).key;
        forall |msg: FBCMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& resource_create_request_msg(resource_key)(msg)
        } ==> {
            &&& at_fbc_step(key, FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
            &&& FBCCluster::pending_req_msg_is(s, key, msg)
            &&& make(sub_resource, fbc, s.ongoing_reconciles()[key].local_state).is_Ok()
            &&& msg.content.get_create_request().obj == make(sub_resource, fbc, s.ongoing_reconciles()[key].local_state).get_Ok_0()
        }
    }
}

pub open spec fn every_resource_update_request_implies_at_after_update_resource_step(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let key = fbc.object_ref();
        let resource_key = get_request(sub_resource, fbc).key;
        forall |msg: FBCMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& resource_update_request_msg(resource_key)(msg)
        } ==> {
            &&& at_fbc_step(key, FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& FBCCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.resource_version.is_Some()
            &&& msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
            &&& (
                s.resources().contains_key(resource_key)
                && msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
            ) ==> (
                update(sub_resource, fbc, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).is_Ok()
                && msg.content.get_update_request().obj == update(sub_resource, fbc, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).get_Ok_0()
            )
        }
    }
}

pub open spec fn resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    let key = get_request(sub_resource, fbc).key;
    |s: FBCCluster| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.owner_references_only_contains(fbc.controller_owner_ref())
    }
}

pub open spec fn no_delete_resource_request_msg_in_flight(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        forall |msg: FBCMessage| !{
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst.is_ApiServer()
            &&& msg.content.is_delete_request()
            &&& msg.content.get_delete_request().key == get_request(sub_resource, fbc).key
        }
    }
}

pub open spec fn no_update_status_request_msg_in_flight(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
            forall |msg: FBCMessage|
                #[trigger] s.in_flight().contains(msg)
                && msg.content.is_update_status_request()
                ==> msg.content.get_update_status_request().key() != get_request(sub_resource, fbc).key
    }
}

}
