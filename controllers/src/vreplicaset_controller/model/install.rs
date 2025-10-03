// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use verifiable_controllers::kubernetes_api_objects::{error::*, spec::prelude::*};
use verifiable_controllers::kubernetes_cluster::spec::cluster::{Cluster, ControllerModel};
use verifiable_controllers::reconciler::spec::io::{VoidEReqView, VoidERespView};
use crate::vreplicaset_controller::model::reconciler::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

impl Marshallable for VReplicaSetReconcileState {
    uninterp spec fn marshal(self) -> Value;

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()) is Ok && o == Self::unmarshal(o.marshal())->Ok_0
    {}
}

pub open spec fn vrs_controller_model() -> ControllerModel {
    ControllerModel {
        reconcile_model: Cluster::installed_reconcile_model::<VReplicaSetReconciler, VReplicaSetReconcileState, VReplicaSetView, VoidEReqView, VoidERespView>(),
        external_model: None,
    }
}

}
