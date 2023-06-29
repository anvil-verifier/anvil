// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, resource::*};
use crate::kubernetes_cluster::{
    proof::{kubernetes_api_safety, wf1_assistant::controller_action_pre_implies_next_pre},
    spec::{
        cluster::*,
        controller::common::ControllerAction,
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::controller,
        message::*,
    },
};
use crate::reconciler::spec::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

pub open spec fn reconciler_init_and_no_pending_req
<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(cr_key: ObjectRef) -> StatePred<State<K, T>> {
    |s: State<K, T>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state == ReconcilerType::reconcile_init_state()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    }
}

pub open spec fn reconciler_reconcile_init<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(cr_key: ObjectRef)
    -> StatePred<State<K, T>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<K, T>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& ReconcilerType::reconcile_init_state() == s.reconcile_state_of(cr_key).local_state
    }
}

pub open spec fn reconciler_reconcile_done<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(cr_key: ObjectRef)
    -> StatePred<State<K, T>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<K, T>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& ReconcilerType::reconcile_done(s.reconcile_state_of(cr_key).local_state)
    }
}

pub open spec fn reconciler_reconcile_error<K: ResourceView, T, ReconcilerType: Reconciler<K, T>>(cr_key: ObjectRef)
    -> StatePred<State<K, T>>
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    |s: State<K, T>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& ReconcilerType::reconcile_error(s.reconcile_state_of(cr_key).local_state)
    }
}

}
