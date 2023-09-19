// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::DynamicObjectView, dynamic::*,
    object_meta::*, resource::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::simple_controller::common::*;
use crate::simple_controller::spec::custom_resource::*;
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::new_strlit;

verus! {

/// SimpleReconcileState describes the local state with which the reconcile functions makes decisions.
pub struct SimpleReconcileState {
    // reconcile_pc, like a program counter, is used to track the progress of reconcile_core
    // since reconcile_core is frequently "trapped" into the controller_runtime spec.
    pub reconcile_step: SimpleReconcileStep,
}

/// We use Reconciler to pack up everything specific to the custom controller,
/// including reconcile function (reconcile_core) and triggering conditions (reconcile_trigger)
pub struct SimpleReconciler {}

impl Reconciler<SimpleCRView, EmptyAPI> for SimpleReconciler {
    type T = SimpleReconcileState;

    open spec fn reconcile_init_state() -> SimpleReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(
        cr: SimpleCRView, resp_o: Option<ResponseView<EmptyTypeView>>, state: SimpleReconcileState
    ) -> (SimpleReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(cr, resp_o, state)
    }

    open spec fn reconcile_done(state: SimpleReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: SimpleReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool {
        false // Don't expect anything from the user except the cr object
    }
}

pub open spec fn simple_reconciler() -> SimpleReconciler {
    SimpleReconciler{}
}

pub open spec fn reconcile_init_state() -> SimpleReconcileState {
    SimpleReconcileState {
        reconcile_step: SimpleReconcileStep::Init,
    }
}

pub open spec fn reconcile_done(state: SimpleReconcileState) -> bool {
    match state.reconcile_step {
        SimpleReconcileStep::AfterCreateConfigMap => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: SimpleReconcileState) -> bool {
    match state.reconcile_step {
        SimpleReconcileStep::Init => false,
        SimpleReconcileStep::AfterCreateConfigMap => false,
        _ => true,
    }
}

/// This is a highly simplified reconcile core spec:
/// it sends requests to create a configmap for the cr.
/// TODO: make the reconcile_core create more resources such as a statefulset
pub open spec fn reconcile_core(
    cr: SimpleCRView, resp_o: Option<ResponseView<EmptyTypeView>>, state: SimpleReconcileState
) -> (SimpleReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        cr.metadata.name.is_Some(),
        cr.metadata.namespace.is_Some(),
{
    let step = state.reconcile_step;
    match step {
        SimpleReconcileStep::Init => {
            let state_prime = SimpleReconcileState {
                reconcile_step: SimpleReconcileStep::AfterCreateConfigMap,
                ..state
            };
            let req_o = Some(RequestView::KRequest(create_cm_req(cr)));
            (state_prime, req_o)
        }
        _ => {
            let state_prime = SimpleReconcileState {
                reconcile_step: step,
                ..state
            };
            let req_o = None;
            (state_prime, req_o)
        }
    }
}

pub open spec fn make_config_map(cr: SimpleCRView) -> ConfigMapView
{
    let config_map = ConfigMapView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(cr.metadata.name.get_Some_0() + new_strlit("-cm")@)
        )
        .set_data(Map::empty().insert(new_strlit("content")@, cr.spec.content));
    config_map
}

pub open spec fn create_cm_req(cr: SimpleCRView) -> APIRequest
{
    APIRequest::CreateRequest(CreateRequest{
        namespace: cr.metadata.namespace.get_Some_0(),
        obj: make_config_map(cr).marshal(),
    })
}

}
