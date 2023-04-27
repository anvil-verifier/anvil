// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*, config_map::*, object::*};
use crate::simple_controller::spec::simple_reconciler::reconcile_core as reconcile_core_spec;
use crate::simple_controller::spec::simple_reconciler::SimpleReconcileState as SimpleReconcileStateView;
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

// TODO: merge it into vstd
pub const fn is_result_ok<T, E>(result: &Result<T, E>) -> (res: bool)
    ensures res <==> result.is_Ok(),
{
    match result {
        Result::Ok(_) => true,
        Result::Err(_) => false,
    }
}

pub fn reconcile_init_state() -> SimpleReconcileState {
    SimpleReconcileState {
        reconcile_pc: 0,
    }
}

pub fn reconcile_done(state: &SimpleReconcileState) -> bool {
    state.reconcile_pc == 2
}

pub fn reconcile_error(state: &SimpleReconcileState) -> bool {
    state.reconcile_pc != 0 && state.reconcile_pc != 1 && state.reconcile_pc != 2
}

/// reconcile_core is the exec implementation of the core reconciliation logic.
/// It will be called by the reconcile() function in a loop in our shim layer, and reconcile()
/// will be called by kube-rs framework when related events happen.
/// The postcondition ensures that it conforms to the spec of reconciliation logic.
///
/// TODO: Maybe we should make state a mutable reference; revisit it later
pub fn reconcile_core(cr_key: &KubeObjectRef, resp_o: &Option<KubeAPIResponse>, state: &SimpleReconcileState) -> (res: (SimpleReconcileState, Option<KubeAPIRequest>))
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        (res.0.to_view(), opt_req_to_view(&res.1)) == reconcile_core_spec(cr_key.to_view(), opt_resp_to_view(&resp_o), state.to_view()),
{
    let pc = state.reconcile_pc;
    if pc == init_pc() {
        assert(pc as nat == 0);
        let state_prime = SimpleReconcileState {
            reconcile_pc: after_get_cr_pc(),
        };
        let req_o = Option::Some(KubeAPIRequest::CustomResourceRequest(
            KubeCustomResourceRequest::GetRequest(
                KubeGetRequest {
                    name: cr_key.name.clone(),
                    namespace: cr_key.namespace.clone(),
                }
            )
        ));
        (state_prime, req_o)
    } else if pc == after_get_cr_pc() {
        if resp_o.is_some() {
            let resp = resp_o.as_ref().unwrap();
            if resp.is_get_response() && is_result_ok(&resp.as_get_response_ref().res) {
                let state_prime = SimpleReconcileState {
                    reconcile_pc: after_create_cm_pc(),
                };
                let mut config_map = ConfigMap::default();
                config_map.set_name(cr_key.name.clone().concat(new_strlit("-cm")));
                config_map.set_namespace(cr_key.namespace.clone());
                let req_o = Option::Some(KubeAPIRequest::ConfigMapRequest(
                    KubeConfigMapRequest::CreateRequest(
                        KubeCreateRequest {
                            obj: config_map,
                        }
                    )
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
