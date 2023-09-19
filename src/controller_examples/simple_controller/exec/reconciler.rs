// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, object_meta::*, resource::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::simple_controller::common::*;
use crate::simple_controller::spec::custom_resource::*;
use crate::simple_controller::spec::reconciler as simple_spec;
use vstd::prelude::*;
use vstd::string::*;

verus! {

/// SimpleReconcileState has the local variables used in one invocation
/// of reconcile() (i.e., multiple calls to reconcile_core()).
/// Its view is simple_spec::SimpleReconcileState.
pub struct SimpleReconcileState {
    pub reconcile_step: SimpleReconcileStep,
}

impl SimpleReconcileState {
    pub open spec fn to_view(&self) -> simple_spec::SimpleReconcileState {
        simple_spec::SimpleReconcileState {
            reconcile_step: self.reconcile_step,
        }
    }
}

pub struct SimpleReconciler {}

#[verifier(external)]
impl Reconciler<SimpleCR, SimpleReconcileState, EmptyType, EmptyType, EmptyAPIShimLayer> for SimpleReconciler {
    fn reconcile_init_state(&self) -> SimpleReconcileState {
        reconcile_init_state()
    }

    fn reconcile_core(&self, cr: &SimpleCR, resp_o: Option<Response<EmptyType>>, state: SimpleReconcileState) -> (SimpleReconcileState, Option<Request<EmptyType>>) {
        reconcile_core(cr, resp_o, state)
    }

    fn reconcile_done(&self, state: &SimpleReconcileState) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(&self, state: &SimpleReconcileState) -> bool {
        reconcile_error(state)
    }
}

impl Default for SimpleReconciler {
    fn default() -> SimpleReconciler { SimpleReconciler{} }
}

pub fn reconcile_init_state() -> (res: SimpleReconcileState)
    ensures
        simple_spec::reconcile_init_state() == res.to_view(),
{
    SimpleReconcileState {
        reconcile_step: SimpleReconcileStep::Init,
    }
}

pub fn reconcile_done(state: &SimpleReconcileState) -> (res: bool)
    ensures
        simple_spec::reconcile_done(state.to_view()) == res,
{
    match state.reconcile_step {
        SimpleReconcileStep::AfterCreateConfigMap => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &SimpleReconcileState) -> (res: bool)
    ensures
        simple_spec::reconcile_error(state.to_view()) == res,
{
    match state.reconcile_step {
        SimpleReconcileStep::Init => false,
        SimpleReconcileStep::AfterCreateConfigMap => false,
        _ => true,
    }
}

/// reconcile_core is the exec implementation of the core reconciliation logic.
/// It will be called by the reconcile() function in a loop in our shim layer, and reconcile()
/// will be called by kube-rs framework when related events happen.
/// The postcondition ensures that it conforms to the spec of reconciliation logic.

// TODO: Maybe we should make state a mutable reference; revisit it later
// TODO: need to prove whether the object is valid; See an example:
// ConfigMap "foo_cm" is invalid: metadata.name: Invalid value: "foo_cm": a lowercase RFC 1123 subdomain must consist of lower case alphanumeric characters, '-' or '.',
// and must start and end with an alphanumeric character (e.g. 'example.com', regex used for validation is '[a-z0-9]([-a-z0-9]*[a-z0-9])?(\.[a-z0-9]([-a-z0-9]*[a-z0-9])?)*')
pub fn reconcile_core(cr: &SimpleCR, resp_o: Option<Response<EmptyType>>, state: SimpleReconcileState) -> (res: (SimpleReconcileState, Option<Request<EmptyType>>))
    requires
        cr@.metadata.name.is_Some(),
        cr@.metadata.namespace.is_Some(),
    ensures
        (res.0.to_view(), opt_request_to_view(&res.1)) == simple_spec::reconcile_core(cr@, opt_response_to_view(&resp_o), state.to_view()),
{
    let step = state.reconcile_step;
    match step {
        SimpleReconcileStep::Init => {
            let state_prime = SimpleReconcileState {
                reconcile_step: SimpleReconcileStep::AfterCreateConfigMap,
                ..state
            };
            let config_map = make_configmap(cr);
            let req_o = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                api_resource: ConfigMap::api_resource(),
                namespace: cr.metadata().namespace().unwrap(),
                obj: config_map.marshal(),
            });
            (state_prime, Some(Request::KRequest(req_o)))
        }
        _ => {
            let state_prime = SimpleReconcileState {
                reconcile_step: step,
                ..state
            };
            (state_prime, None)
        }
    }
}

pub fn make_configmap(cr: &SimpleCR) -> (cm: ConfigMap)
    requires
        cr@.metadata.name.is_Some(),
        cr@.metadata.namespace.is_Some(),
    ensures
        cm@ == simple_spec::make_config_map(cr@),
{
    let mut config_map = ConfigMap::default();
    config_map.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(cr.metadata().name().unwrap().clone().concat(new_strlit("-cm")));
        metadata
    });
    config_map.set_data({
        let mut data = StringMap::new();
        data.insert(String::from_str(new_strlit("content")), cr.spec().content());
        data
    });
    config_map
}

}
