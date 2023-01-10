// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::examples::kubernetes_cluster::spec::{common::*, reconciler::*};
use crate::pervasive::{map::*, option::*, seq::*, set::*};
use crate::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

/// We use Reconciler to pack up everything specific to the custom controller,
/// including reconcile function (reconcile_core) and triggering conditions (reconcile_trigger)
pub open spec fn simple_reconciler() -> Reconciler {
    Reconciler {
        reconcile_init_state: || reconcile_init_state(),
        reconcile_trigger: |msg: Message| reconcile_trigger(msg),
        reconcile_core: |cr_key: ResourceKey, resp_o: Option<APIResponse>, state: ReconcileState| reconcile_core(cr_key, resp_o, state),
        reconcile_done: |state: ReconcileState| reconcile_done(state),
    }
}

pub open spec fn reconcile_init_state() -> ReconcileState {
    ReconcileState {
        reconcile_pc: 0,
    }
}

/// This is a highly simplified triggering condition
/// which only considers creation/update to CR objects.
/// TODO: Reason about ownership and other relationships.
pub open spec fn reconcile_trigger(msg: Message) -> Option<ResourceKey>
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
pub open spec fn reconcile_core(cr_key: ResourceKey, resp_o: Option<APIResponse>, state: ReconcileState) -> (ReconcileState, Option<APIRequest>)
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    let pc = state.reconcile_pc;
    if pc === init_pc() {
        let state_prime = ReconcileState {
            reconcile_pc: after_get_cr_pc(),
        };
        let req_o = Option::Some(APIRequest::GetRequest(GetRequest{key: cr_key}));
        (state_prime, req_o)
    } else if pc === after_get_cr_pc() {
        let state_prime = ReconcileState {
            reconcile_pc: after_create_cm_pc(),
        };
        let req_o = Option::Some(create_cm_req(cr_key));
        (state_prime, req_o)
    } else {
        (state, Option::None)
    }
}

pub open spec fn reconcile_done(state: ReconcileState) -> bool {
    &&& state.reconcile_pc !== init_pc()
    &&& state.reconcile_pc !== after_get_cr_pc()
}

pub open spec fn init_pc() -> nat { 0 }

pub open spec fn after_get_cr_pc() -> nat { 1 }

pub open spec fn after_create_cm_pc() -> nat { 2 }

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
