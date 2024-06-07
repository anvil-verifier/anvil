// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::v_replica_set_controller::trusted::{
    spec_types::*, step::*,
};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use vstd::{prelude::*, string::*};

verus! {

impl Reconciler<VReplicaSetView, EmptyAPI> for VReplicaSetReconciler {
    type T = VReplicaSetReconcileState;

    open spec fn reconcile_init_state() -> VReplicaSetReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(fb: VReplicaSetView, resp_o: Option<ResponseView<EmptyTypeView>>, state: VReplicaSetReconcileState)
    -> (VReplicaSetReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(fb, resp_o, state)
    }

    open spec fn reconcile_done(state: VReplicaSetReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: VReplicaSetReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool { false /* expect nothing: stub */ }
}

pub open spec fn reconcile_init_state() -> VReplicaSetReconcileState { 
    VReplicaSetReconcileState { 
        reconcile_step: VReplicaSetReconcileStepView::Init,
        filtered_pods: None,
    } 
}

pub open spec fn reconcile_done(state: VReplicaSetReconcileState) -> bool {
    false
}

pub open spec fn reconcile_error(state: VReplicaSetReconcileState) -> bool {
    false
}

pub open spec fn reconcile_core(
    fb: VReplicaSetView, resp_o: Option<ResponseView<EmptyTypeView>>, state: VReplicaSetReconcileState
) -> (VReplicaSetReconcileState, Option<RequestView<EmptyTypeView>>) {
    (state, None)
}

}
    