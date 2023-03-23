// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, config_map::*, object::*};
use crate::kubernetes_cluster::spec::{message::*, reconciler::*};
use crate::pervasive::prelude::*;
use crate::pervasive_ext::string_const::*;
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;

verus! {

/// SimpleReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct SimpleReconcileState {
    // reconcile_pc, like a program counter, is used to track the progress of reconcile_core
    // since reconcile_core is frequently "trapped" into the controller_runtime spec.
    pub reconcile_pc: nat,
}

/// We use Reconciler to pack up everything specific to the custom controller,
/// including reconcile function (reconcile_core) and triggering conditions (reconcile_trigger)
pub open spec fn simple_reconciler() -> Reconciler<SimpleReconcileState> {
    Reconciler {
        reconcile_init_state: || reconcile_init_state(),
        reconcile_core: |cr_key: ObjectRef, resp_o: Option<APIResponse>, state: SimpleReconcileState| reconcile_core(cr_key, resp_o, state),
        reconcile_done: |state: SimpleReconcileState| reconcile_done(state),
        reconcile_error: |state: SimpleReconcileState| reconcile_error(state),
    }
}

pub open spec fn reconcile_init_state() -> SimpleReconcileState {
    SimpleReconcileState {
        reconcile_pc: 0,
    }
}

/// This is a highly simplified reconcile core spec:
/// it sends requests to create a configmap for the cr.
/// TODO: make the reconcile_core create more resources such as a statefulset
pub open spec fn reconcile_core(cr_key: ObjectRef, resp_o: Option<APIResponse>, state: SimpleReconcileState) -> (SimpleReconcileState, Option<APIRequest>)
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    let pc = state.reconcile_pc;
    if pc == init_pc() {
        let state_prime = SimpleReconcileState {
            reconcile_pc: after_get_cr_pc(),
        };
        let req_o = Option::Some(APIRequest::GetRequest(GetRequest{key: cr_key}));
        (state_prime, req_o)
    } else if pc == after_get_cr_pc() {
        let state_prime = SimpleReconcileState {
            reconcile_pc: after_create_cm_pc(),
        };
        let req_o = Option::Some(create_cm_req(cr_key));
        (state_prime, req_o)
    } else {
        (state, Option::None)
    }
}

pub open spec fn reconcile_done(state: SimpleReconcileState) -> bool {
    state.reconcile_pc == after_create_cm_pc()
}

pub open spec fn reconcile_error(state: SimpleReconcileState) -> bool {
    &&& state.reconcile_pc !== init_pc()
    &&& state.reconcile_pc !== after_get_cr_pc()
    &&& state.reconcile_pc !== after_create_cm_pc()
}

pub open spec fn init_pc() -> nat { 0 }

pub open spec fn after_get_cr_pc() -> nat { 1 }

pub open spec fn after_create_cm_pc() -> nat { 2 }

pub open spec fn subresource_configmap(cr_key: ObjectRef) -> ConfigMapView
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    let config_map = ConfigMapView::default().set_name(cr_key.name + cm_suffix()).set_namespace(cr_key.namespace);
    config_map
}

pub open spec fn create_cm_req(cr_key: ObjectRef) -> APIRequest
    recommends
        cr_key.kind.is_CustomResourceKind(),
{
    APIRequest::CreateRequest(CreateRequest{
        obj: KubernetesObject::ConfigMap(subresource_configmap(cr_key)),
    })
}

}
