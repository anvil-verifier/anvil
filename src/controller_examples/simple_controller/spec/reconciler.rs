// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_examples::simple_controller::spec::custom_resource::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::DynamicObjectView, resource::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_const::*;
use crate::reconciler::spec::*;
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::string::new_strlit;

verus! {

/// SimpleReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct SimpleReconcileState {
    // reconcile_pc, like a program counter, is used to track the progress of reconcile_core
    // since reconcile_core is frequently "trapped" into the controller_runtime spec.
    pub reconcile_pc: nat,
}

/// We use Reconciler to pack up everything specific to the custom controller,
/// including reconcile function (reconcile_core) and triggering conditions (reconcile_trigger)
pub open spec fn simple_reconciler() -> Reconciler<CustomResourceView, SimpleReconcileState> {
    Reconciler {
        reconcile_init_state: || reconcile_init_state(),
        reconcile_core: |cr_key: ObjectRef, resp_o: Option<APIResponse>, state: SimpleReconcileState| reconcile_core(cr_key, resp_o, state),
        reconcile_done: |state: SimpleReconcileState| reconcile_done(state),
        reconcile_error: |state: SimpleReconcileState| reconcile_error(state),
        consume_kubernetes_resource_type: |cr: CustomResourceView| cr,
    }
}

pub open spec fn reconcile_init_state() -> SimpleReconcileState {
    SimpleReconcileState {
        reconcile_pc: init_pc(),
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
        if resp_o.is_Some() && resp_o.get_Some_0().is_GetResponse() && resp_o.get_Some_0().get_GetResponse_0().res.is_Ok() {
            let state_prime = SimpleReconcileState {
                reconcile_pc: after_create_cm_pc(),
            };
            let cr = CustomResourceView::from_dynamic_object(resp_o.get_Some_0().get_GetResponse_0().res.get_Ok_0());
            if (cr.metadata.name.is_Some() && cr.metadata.namespace.is_Some()) {
                (state_prime, Option::Some(create_cm_req(cr)))
            } else {
                let state_prime = SimpleReconcileState {
                    reconcile_pc: error_pc(),
                };
                (state_prime, Option::None)
            }
        } else {
            let state_prime = SimpleReconcileState {
                reconcile_pc: error_pc(),
            };
            (state_prime, Option::None)
        }
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

pub open spec fn error_pc() -> nat { 3 }

pub open spec fn subresource_configmap(cr: CustomResourceView) -> ConfigMapView
{
    let config_map = ConfigMapView::default().set_name(cr.metadata.name.get_Some_0() + cm_suffix()).set_namespace(cr.metadata.namespace.get_Some_0()).set_data(Map::empty().insert(new_strlit("content")@, cr.spec.content));
    config_map
}

pub open spec fn create_cm_req(cr: CustomResourceView) -> APIRequest
{
    APIRequest::CreateRequest(CreateRequest{
        obj: subresource_configmap(cr).to_dynamic_object(),
    })
}

}
