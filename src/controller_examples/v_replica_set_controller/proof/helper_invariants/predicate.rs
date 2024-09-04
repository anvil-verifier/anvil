// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
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
use crate::v_replica_set_controller::{
    model::reconciler::*,
    proof::{predicate::*},
    trusted::{spec_types::*, step::*, liveness_theorem::*},
};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub open spec fn cluster_resources_is_finite() -> StatePred<VRSCluster> {
    |s: VRSCluster| s.resources().dom().finite()
} 

pub open spec fn every_create_request_is_well_formed() -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        forall |msg: VRSMessage| #![trigger msg.dst.is_ApiServer(), msg.content.is_APIRequest()] {
            let content = msg.content;
            let obj = content.get_create_request().obj;
            &&& s.in_flight().contains(msg)
            &&& msg.dst.is_ApiServer()
            &&& msg.content.is_APIRequest()
            &&& content.is_create_request()
        } ==> {
            let content = msg.content;
            let obj = content.get_create_request().obj;
            &&& obj.metadata.deletion_timestamp.is_None()
            &&& content.get_create_request().namespace == obj.metadata.namespace.unwrap()
        }
    }
}

pub open spec fn no_pending_update_or_update_status_request_on_pods() -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        forall |msg: VRSMessage| {
            &&& s.in_flight().contains(msg)
            &&& #[trigger] msg.dst.is_ApiServer()
            &&& #[trigger] msg.content.is_APIRequest()
        } ==> {
            &&& msg.content.is_update_request() ==> msg.content.get_update_request().key().kind != PodView::kind()
            &&& msg.content.is_update_status_request() ==> msg.content.get_update_status_request().key().kind != PodView::kind()
        }
    }
}


pub open spec fn every_create_matching_pod_request_implies_at_after_create_pod_step(
    vrs: VReplicaSetView
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        forall |msg: VRSMessage| #![trigger msg.dst.is_ApiServer(), msg.content.is_APIRequest()] {
            let content = msg.content;
            let obj = content.get_create_request().obj;
            &&& s.in_flight().contains(msg)
            &&& msg.dst.is_ApiServer()
            &&& msg.content.is_APIRequest()
            &&& content.is_create_request()
            &&& owned_selector_match_is(vrs, obj)
        } ==> {
            &&& exists |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterCreatePod(diff))(s)
            &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), msg)
        }
    }
}

pub open spec fn every_delete_matching_pod_request_implies_at_after_delete_pod_step(
    vrs: VReplicaSetView
) -> StatePred<VRSCluster> {
    |s: VRSCluster| {
        forall |msg: VRSMessage| #![trigger msg.dst.is_ApiServer(), msg.content.is_APIRequest()] {
            let content = msg.content;
            let key = content.get_delete_request().key;
            let obj = s.resources()[key];
            &&& s.in_flight().contains(msg)
            &&& msg.dst.is_ApiServer()
            &&& msg.content.is_APIRequest()
            &&& content.is_delete_request()
            &&& s.resources().contains_key(key)
            &&& owned_selector_match_is(vrs, obj)
        } ==> {
            &&& exists |diff: usize| #[trigger] at_vrs_step_with_vrs(vrs, VReplicaSetReconcileStep::AfterDeletePod(diff))(s)
            &&& VRSCluster::pending_req_msg_is(s, vrs.object_ref(), msg)
        }
    }
}

}
