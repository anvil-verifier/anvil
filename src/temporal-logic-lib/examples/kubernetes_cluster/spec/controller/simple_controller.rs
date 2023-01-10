// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::kubernetes_cluster::spec::{common::*, controller::common::*};
use crate::pervasive::{map::*, option::*, seq::*, set::*};
use crate::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

/// This is a highly simplified triggering condition
/// which only considers creation/update to CR objects.
/// TODO: Reason about ownership and other relationships.
pub open spec fn relevant_cr_key(msg: Message) -> Option<ResourceKey>
    recommends
        msg.content.is_WatchEvent(),
{
    if msg.is_watch_event_of_kind(ResourceKind::CustomResourceKind) {
        if msg.is_added_event() {
            Option::Some(msg.get_added_event().obj.key)
        } else if msg.is_modified_event() {
            Option::Some(msg.get_modified_event().obj.key)
        } else {
            Option::None
        }
    } else {
        Option::None
    }
}

/// This is a highly simplified reconcile core spec:
/// it sends requests to create a configmap for the cr.
/// TODO: make the reconcile_core create more resources such as a statefulset
pub open spec fn reconcile_core(cr_key: ResourceKey, step: ReconcileCoreStep, resp_o: Option<APIResponse>) -> (ReconcileCoreStep, Option<APIRequest>)
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    match step {
        ReconcileCoreStep::Init => {
            (ReconcileCoreStep::GetCRDone, Option::Some(APIRequest::GetRequest(GetRequest{key: cr_key})))
        },
        ReconcileCoreStep::GetCRDone => {
            (ReconcileCoreStep::CreateCMDone, Option::Some(create_cm_req(cr_key)))
            // if resp_o.is_None() {
            //     (ReconcileCoreStep::Error, Option::None)
            // } else {
            //     if is_ok_resp(resp_o.get_Some_0()) {
            //         (ReconcileCoreStep::CreateCMDone, Option::Some(create_cm_req(cr_key)))
            //     } else {
            //         (ReconcileCoreStep::Done, Option::None)
            //     }
            // }
        },
        ReconcileCoreStep::CreateCMDone => {
            (ReconcileCoreStep::Done, Option::None)
            // if resp_o.is_None() {
            //     (ReconcileCoreStep::Error, Option::None)
            // } else {
            //     if is_ok_resp(resp_o.get_Some_0()) {
            //         (ReconcileCoreStep::Done, Option::None)
            //         // (ReconcileCoreStep::CreateStsDone, Option::Some(create_sts_req(cr_key)))
            //     } else {
            //         (ReconcileCoreStep::Error, Option::None)
            //     }
            // }
        },
        // ReconcileCoreStep::CreateStsDone => {
        //     if resp_o.is_None() {
        //         (ReconcileCoreStep::Error, Option::None)
        //     } else {
        //         if is_ok_resp(resp_o.get_Some_0()) {
        //             (ReconcileCoreStep::Done, Option::None)
        //         } else {
        //             (ReconcileCoreStep::Error, Option::None)
        //         }
        //     }
        // },
        ReconcileCoreStep::Done => {
            (ReconcileCoreStep::Done, Option::None)
        },
        ReconcileCoreStep::Error => {
            (ReconcileCoreStep::Error, Option::None)
        }
    }
}

pub open spec fn subresource_configmap(cr_key: ResourceKey) -> ResourceObj
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    ResourceObj {
        key: ResourceKey {
            name: cr_key.name + cm_suffix(),
            namespace: cr_key.namespace,
            kind: ResourceKind::ConfigMapKind
        },
    }
}

pub open spec fn create_cm_req(cr_key: ResourceKey) -> APIRequest
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    APIRequest::CreateRequest(CreateRequest{
        obj: subresource_configmap(cr_key),
    })
}

pub open spec fn create_sts_req(cr_key: ResourceKey) -> APIRequest
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    APIRequest::CreateRequest(CreateRequest{
        obj: ResourceObj {
            key: ResourceKey {
                name: cr_key.name + sts_suffix(),
                namespace: cr_key.namespace,
                kind: ResourceKind::StatefulSetKind
            },
        },
    })
}

}
