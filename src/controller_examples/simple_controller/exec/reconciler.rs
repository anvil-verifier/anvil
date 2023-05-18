// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_examples::simple_controller::spec::custom_resource::*;
use crate::controller_examples::simple_controller::spec::reconciler::reconcile_core as reconcile_core_spec;
use crate::controller_examples::simple_controller::spec::reconciler::reconcile_done as reconcile_done_spec;
use crate::controller_examples::simple_controller::spec::reconciler::reconcile_error as reconcile_error_spec;
use crate::controller_examples::simple_controller::spec::reconciler::reconcile_init_state as reconcile_init_state_spec;
use crate::controller_examples::simple_controller::spec::reconciler::SimpleReconcileState as SimpleReconcileStateView;
use crate::kubernetes_api_objects::{api_method::*, common::*, config_map::*};
use crate::pervasive_ext::string_map::StringMap;
use crate::reconciler::exec::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

/// SimpleReconcileState has the local variables used in one invocation
/// of reconcile() (i.e., multiple calls to reconcile_core()).
/// Its view is SimpleReconcileStateView.
pub struct SimpleReconcileState {
    pub reconcile_pc: u64,
}

impl SimpleReconcileState {
    pub open spec fn to_view(&self) -> SimpleReconcileStateView {
        SimpleReconcileStateView {
            reconcile_pc: self.reconcile_pc as nat,
        }
    }
}

pub struct SimpleReconciler {}

#[verifier(external)]
impl Reconciler<SimpleReconcileState> for SimpleReconciler {
    fn reconcile_init_state(&self) -> SimpleReconcileState {
        SimpleReconcileState {
            reconcile_pc: init_pc(),
        }
    }

    fn reconcile_core(&self, cr_key: &KubeObjectRef, resp_o: &Option<KubeAPIResponse>, state: &SimpleReconcileState) -> (SimpleReconcileState, Option<KubeAPIRequest>) {
        reconcile_core(cr_key, resp_o, state)
    }

    fn reconcile_done(&self, state: &SimpleReconcileState) -> bool {
        state.reconcile_pc == after_create_cm_pc()
    }

    fn reconcile_error(&self, state: &SimpleReconcileState) -> bool {
        state.reconcile_pc != init_pc() && state.reconcile_pc != after_get_cr_pc() && state.reconcile_pc != after_create_cm_pc()
    }
}

impl Default for SimpleReconciler {
    fn default() -> SimpleReconciler { SimpleReconciler{} }
}

pub fn reconcile_init_state() -> (res: SimpleReconcileState)
    ensures
        reconcile_init_state_spec() == res.to_view(),
{
    SimpleReconcileState {
        reconcile_pc: init_pc(),
    }
}

pub fn reconcile_done(state: &SimpleReconcileState) -> (res: bool)
    ensures
        reconcile_done_spec(state.to_view()) == res,
{
    state.reconcile_pc == after_create_cm_pc()
}

pub fn reconcile_error(state: &SimpleReconcileState) -> (res: bool)
    ensures
        reconcile_error_spec(state.to_view()) == res,
{
    state.reconcile_pc != init_pc() && state.reconcile_pc != after_get_cr_pc() && state.reconcile_pc != after_create_cm_pc()
}

/// reconcile_core is the exec implementation of the core reconciliation logic.
/// It will be called by the reconcile() function in a loop in our shim layer, and reconcile()
/// will be called by kube-rs framework when related events happen.
/// The postcondition ensures that it conforms to the spec of reconciliation logic.

// TODO: Maybe we should make state a mutable reference; revisit it later
// TODO: need to prove whether the object is valid; See an example:
// ConfigMap "foo_cm" is invalid: metadata.name: Invalid value: "foo_cm": a lowercase RFC 1123 subdomain must consist of lower case alphanumeric characters, '-' or '.',
// and must start and end with an alphanumeric character (e.g. 'example.com', regex used for validation is '[a-z0-9]([-a-z0-9]*[a-z0-9])?(\.[a-z0-9]([-a-z0-9]*[a-z0-9])?)*')
pub fn reconcile_core(cr_key: &KubeObjectRef, resp_o: &Option<KubeAPIResponse>, state: &SimpleReconcileState) -> (res: (SimpleReconcileState, Option<KubeAPIRequest>))
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        (res.0.to_view(), opt_req_to_view(&res.1)) == reconcile_core_spec(cr_key.to_view(), opt_resp_to_view(&resp_o), state.to_view()),
{
    let pc = state.reconcile_pc;
    if pc == init_pc() {
        let state_prime = SimpleReconcileState {
            reconcile_pc: after_get_cr_pc(),
        };
        let req_o = Option::Some(KubeAPIRequest::GetRequest(
            KubeGetRequest {
                api_resource: CustomResource::api_resource(),
                name: cr_key.name.clone(),
                namespace: cr_key.namespace.clone(),
            }
        ));
        (state_prime, req_o)
    } else if pc == after_get_cr_pc() {
        if resp_o.is_some() {
            let resp = resp_o.as_ref().unwrap();
            if resp.is_get_response() && resp.as_get_response_ref().res.is_ok() {
                let state_prime = SimpleReconcileState {
                    reconcile_pc: after_create_cm_pc(),
                };
                let mut config_map = ConfigMap::default();
                config_map.set_name(cr_key.name.clone().concat(new_strlit("-cm")));
                config_map.set_namespace(cr_key.namespace.clone());
                let cr_map = StringMap::new();
                cr_map.insert(String::from_rust_string("content".to_string()), CustomResource::from_dynamic_object(resp.as_get_response_ref().res.get_Ok_0()).spec().content());
                config_map.set_data(cr_map);
                let req_o = Option::Some(KubeAPIRequest::CreateRequest(
                    KubeCreateRequest {
                        api_resource: ConfigMap::api_resource(),
                        obj: config_map.to_dynamic_object(),
                    }
                ));
                (state_prime, req_o)
            } else {
                let state_prime = SimpleReconcileState {
                    reconcile_pc: error_pc(),
                };
                let req_o = Option::None;
                (state_prime, req_o)
            }
        } else {
            let state_prime = SimpleReconcileState {
                reconcile_pc: error_pc(),
            };
            let req_o = Option::None;
            (state_prime, req_o)
        }
    } else {
        let state_prime = SimpleReconcileState {
            reconcile_pc: pc,
        };
        let req_o = Option::None;
        (state_prime, req_o)
    }
}

pub fn init_pc() -> (res: u64)
    ensures res as nat == 0,
{ 0 }

pub fn after_get_cr_pc() -> (res: u64)
    ensures res as nat == 1,
{ 1 }

pub fn after_create_cm_pc() -> (res: u64)
    ensures res as nat == 2,
{ 2 }

pub fn error_pc() -> (res: u64)
    ensures res as nat == 3,
{ 3 }

}
