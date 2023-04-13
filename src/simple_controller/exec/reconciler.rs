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

/// reconcile_core is the exec implementation of the core reconciliation logic.
/// It will be called by the reconcile() function in a loop in our shim layer, and reconcile()
/// will be called by kube-rs framework when related events happen.
/// The postcondition ensures that it conforms to the spec of reconciliation logic.
///
/// TODO: Maybe we should make state a mutable reference; revisit it later
/// TODO: Maybe we should just clone the String to APIRequest instead of passing a reference; revisit it later
/// TODO: Use the view of resp_o, instead of Option::None, when we need to check the response result to decide the next step
pub fn reconcile_core<'a>(cr_key: &'a KubeObjectRef, resp_o: &'a Option<KubeAPIResponse>, state: &'a SimpleReconcileState) -> (res: (SimpleReconcileState, Option<KubeAPIRequest<'a>>))
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        (res.0.to_view(), opt_req_to_view(&res.1)) == reconcile_core_spec(cr_key.to_view(), Option::None, state.to_view()),
{
    let pc = state.reconcile_pc;
    if pc == 0 {
        let state_prime = SimpleReconcileState {
            reconcile_pc: pc + 1,
        };
        let req_o = Option::Some(KubeAPIRequest::CustomResourceRequest(
            KubeCustomResourceRequest::GetRequest(
                KubeGetRequest {
                    name: &cr_key.name,
                    namespace: &cr_key.namespace,
                }
            )
        ));
        (state_prime, req_o)
    } else if pc == 1 {
        let state_prime = SimpleReconcileState {
            reconcile_pc: pc + 1,
        };
        let mut config_map = ConfigMap::default();
        config_map.set_name(cr_key.name.clone().concat(new_strlit("_cm")));
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
            reconcile_pc: pc,
        };
        let req_o = Option::None;
        (state_prime, req_o)
    }
}

}
