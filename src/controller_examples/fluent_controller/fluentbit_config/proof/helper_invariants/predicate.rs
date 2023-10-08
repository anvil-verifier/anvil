// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::fluent_controller::fluentbit_config::{
    common::*,
    proof::{predicate::*, resource::*},
    spec::{reconciler::*, types::*},
};
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
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

// TODO: some of the invariants here might not be useful

pub open spec fn triggering_cr_satisfies_state_validation() -> StatePred<FBCCluster>
{
    |s: FBCCluster| {
        forall |key: ObjectRef|
        #[trigger] s.ongoing_reconciles().contains_key(key)
        && key.kind.is_CustomResourceKind()
        ==> s.ongoing_reconciles()[key].triggering_cr.state_validation()
    }
}

pub open spec fn object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(key: ObjectRef, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
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

pub open spec fn every_resource_create_request_implies_at_after_create_resource_step(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster>
    recommends
        fbc.well_formed(),
{
    |s: FBCCluster| {
        let key = fbc.object_ref();
        let resource_key = get_request(sub_resource, fbc).key;
        forall |msg: FBCMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& resource_create_request_msg(resource_key)(msg)
        } ==> {
            &&& at_fbc_step(key, FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
            &&& FBCCluster::pending_k8s_api_req_msg_is(s, key, msg)
            &&& make(sub_resource, fbc, s.ongoing_reconciles()[key].local_state).is_Ok()
            &&& msg.content.get_create_request().obj == make(sub_resource, fbc, s.ongoing_reconciles()[key].local_state).get_Ok_0()
        }
    }
}

pub open spec fn every_resource_update_request_implies_at_after_update_resource_step(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster>
    recommends
        fbc.well_formed(),
{
    |s: FBCCluster| {
        let key = fbc.object_ref();
        let resource_key = get_request(sub_resource, fbc).key;
        forall |msg: FBCMessage| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& resource_update_request_msg(resource_key)(msg)
        } ==> {
            &&& at_fbc_step(key, FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& FBCCluster::pending_k8s_api_req_msg_is(s, key, msg)
            &&& s.resources().contains_key(resource_key)
            &&& update(sub_resource, fbc, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).is_Ok()
            &&& msg.content.get_update_request().obj == update(sub_resource, fbc, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).get_Ok_0()
        }
    }
}

pub open spec fn object_of_key_only_has_owner_reference_pointing_to_current_cr(key: ObjectRef, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.owner_references_only_contains(fbc.controller_owner_ref())
    }
}

pub open spec fn no_delete_request_msg_in_flight_with_key(key: ObjectRef) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        forall |msg: FBCMessage| !{
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst.is_KubernetesAPI()
            &&& msg.content.is_delete_request()
            &&& msg.content.get_delete_request().key == key
        }
    }
}

pub open spec fn no_update_status_request_msg_in_flight_with_key(key: ObjectRef) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        forall |msg: FBCMessage| !{
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst.is_KubernetesAPI()
            &&& msg.content.is_update_status_request()
            &&& msg.content.get_update_status_request().key() == key
        }
    }
}

pub open spec fn object_in_etcd_satisfies_unchangeable(sub_resource: SubResource, fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        s.resources().contains_key(get_request(sub_resource, fbc).key)
        ==> unchangeable(sub_resource, s.resources()[get_request(sub_resource, fbc).key], fbc)
    }
}

}
