// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::fluent_controller::fluentbit::{
    model::reconciler::*,
    proof::{predicate::*, resource::*},
    trusted::{spec_types::*, step::*},
};
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, daemon_set::*, owner_reference::*, resource::*,
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

pub open spec fn fb_is_well_formed(fb: FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| fb.well_formed()
}

pub open spec fn the_object_in_reconcile_satisfies_state_validation(key: ObjectRef) -> StatePred<FBCluster>
{
    |s: FBCluster| {
        s.ongoing_reconciles().contains_key(key)
        ==> s.ongoing_reconciles()[key].triggering_cr.state_validation()
    }
}

pub open spec fn the_object_in_schedule_satisfies_state_validation() -> StatePred<FBCluster>
{
    |s: FBCluster| {
        forall |key: ObjectRef|
        #[trigger] s.scheduled_reconciles().contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> s.scheduled_reconciles()[key].state_validation()
    }
}

pub open spec fn cr_objects_in_etcd_satisfy_state_validation() -> StatePred<FBCluster>
{
    |s: FBCluster| {
        forall |key: ObjectRef|
        #[trigger] s.resources().contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> FluentBitView::unmarshal(s.resources()[key]).is_Ok()
            && FluentBitView::unmarshal(s.resources()[key]).get_Ok_0().state_validation()
    }
}

pub open spec fn resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource: SubResource, fb: FluentBitView) -> StatePred<FBCluster> {
    let key = get_request(sub_resource, fb).key;
    |s: FBCluster| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.deletion_timestamp.is_None()
            && s.resources()[key].metadata.finalizers.is_None()
            && exists |uid: Uid| #![auto]
            s.resources()[key].metadata.owner_references == Some(seq![OwnerReferenceView {
                block_owner_deletion: None,
                controller: Some(true),
                kind: FluentBitView::kind(),
                name: fb.metadata.name.get_Some_0(),
                uid: uid,
            }])
    }
}

pub open spec fn resource_get_response_msg(key: ObjectRef) -> spec_fn(FBMessage) -> bool {
    |msg: FBMessage|
        msg.src.is_ApiServer()
        && msg.content.is_get_response()
        && (
            msg.content.get_get_response().res.is_Ok()
            ==> msg.content.get_get_response().res.get_Ok_0().object_ref() == key
        )
}

pub open spec fn resource_update_response_msg(key: ObjectRef, s: FBCluster) -> spec_fn(FBMessage) -> bool {
    |msg: FBMessage|
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

pub open spec fn resource_create_response_msg(key: ObjectRef, s: FBCluster) -> spec_fn(FBMessage) -> bool {
    |msg: FBMessage|
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

/// This spec tells that when the reconciler is at AfterGetDaemonSet, and there is a matched response, the reponse must be
/// sts_get_response_msg. This lemma is used to show that the response message, if is ok, has an object whose reference is
/// daemon_set_key. resp_msg_matches_req_msg doesn't talk about the object in response should match the key in request
/// so we need this extra spec and lemma.
///
/// If we don't have this, we have no idea of what is inside the response message.
pub open spec fn response_at_after_get_resource_step_is_resource_get_response(
    sub_resource: SubResource, fb: FluentBitView
) -> StatePred<FBCluster> {
    let key = fb.object_ref();
    let resource_key = get_request(sub_resource, fb).key;
    |s: FBCluster| {
        at_fb_step(key, FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
        ==> s.ongoing_reconciles()[key].pending_req_msg.is_Some()
            && resource_get_request_msg(resource_key)(s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
            && (
                forall |msg: FBMessage|
                    #[trigger] s.in_flight().contains(msg)
                    && Message::resp_msg_matches_req_msg(msg, s.ongoing_reconciles()[key].pending_req_msg.get_Some_0())
                    ==> resource_get_response_msg(resource_key)(msg)
            )
    }
}

pub open spec fn object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource: SubResource, fb: FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| {
        let key = fb.object_ref();
        forall |msg: FBMessage| {
            &&& s.network_state.in_flight.contains(msg)
            &&& #[trigger] resource_update_request_msg(get_request(sub_resource, fb).key)(msg)
        } ==> {
            &&& at_fb_step(key, FluentBitReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& FBCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.owner_references_only_contains(fb.controller_owner_ref())
        }
    }
}

pub open spec fn every_resource_create_request_implies_at_after_create_resource_step(sub_resource: SubResource, fb: FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| {
        let key = fb.object_ref();
        forall |msg: FBMessage| {
            &&& s.network_state.in_flight.contains(msg)
            &&& #[trigger] resource_create_request_msg(get_request(sub_resource, fb).key)(msg)
        } ==> {
            &&& at_fb_step(key, FluentBitReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
            &&& FBCluster::pending_req_msg_is(s, key, msg)
            &&& make(sub_resource, fb, s.ongoing_reconciles()[key].local_state).is_Ok()
            &&& msg.content.get_create_request().obj == make(sub_resource, fb, s.ongoing_reconciles()[key].local_state).get_Ok_0()
        }
    }
}

pub open spec fn every_resource_update_request_implies_at_after_update_resource_step(sub_resource: SubResource, fb: FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| {
        let key = fb.object_ref();
        let resource_key = get_request(sub_resource, fb).key;
        forall |msg: FBMessage| {
            &&& s.in_flight().contains(msg)
            &&& #[trigger] resource_update_request_msg(get_request(sub_resource, fb).key)(msg)
        } ==> {
            &&& at_fb_step(key, FluentBitReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& FBCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.resource_version.is_Some()
            &&& msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
            &&& (
                s.resources().contains_key(resource_key)
                && msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
            ) ==> (
                update(sub_resource, fb, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).is_Ok()
                && msg.content.get_update_request().obj == update(sub_resource, fb, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).get_Ok_0()
            )
        }
    }
}

pub open spec fn resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource: SubResource, fb: FluentBitView) -> StatePred<FBCluster> {
    let key = get_request(sub_resource, fb).key;
    |s: FBCluster| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.owner_references_only_contains(fb.controller_owner_ref())
    }
}

pub open spec fn no_delete_resource_request_msg_in_flight(sub_resource: SubResource, fb: FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| {
        forall |msg: FBMessage| !{
            &&& s.in_flight().contains(msg)
            &&& #[trigger] resource_delete_request_msg(get_request(sub_resource, fb).key)(msg)
        }
    }
}

pub open spec fn no_update_status_request_msg_in_flight_of_except_daemon_set(sub_resource: SubResource, fb: FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| {
        sub_resource != SubResource::DaemonSet
        ==> {
            forall |msg: FBMessage|
                s.in_flight().contains(msg)
                ==> !(#[trigger] resource_update_status_request_msg(get_request(sub_resource, fb).key)(msg))
        }
    }
}

pub open spec fn no_update_status_request_msg_not_from_bc_in_flight_of_daemon_set(fb: FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| {
        forall |msg: FBMessage|
            #[trigger] s.in_flight().contains(msg)
            && msg.dst.is_ApiServer()
            && !msg.src.is_BuiltinController()
            ==> !resource_update_status_request_msg(get_request(SubResource::DaemonSet, fb).key)(msg)
    }
}

pub open spec fn object_in_etcd_satisfies_unchangeable(sub_resource: SubResource, fb: FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| {
        s.resources().contains_key(get_request(sub_resource, fb).key)
        ==> unchangeable(sub_resource, s.resources()[get_request(sub_resource, fb).key], fb)
    }
}

pub open spec fn daemon_set_not_exists_or_matches_or_no_more_status_update(fb: FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| {
        let sts_key = get_request(SubResource::DaemonSet, fb).key;
        ||| !s.resources().contains_key(sts_key)
        ||| sub_resource_state_matches(SubResource::DaemonSet, fb)(s)
        ||| {
            &&& forall |msg: FBMessage|
                    s.in_flight().contains(msg)
                    ==> !(#[trigger] resource_update_status_request_msg(get_request(SubResource::DaemonSet, fb).key)(msg))
            &&& s.stable_resources().contains(sts_key)
        }
    }
}

}
