// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{error::*, spec::prelude::*};
use crate::kubernetes_cluster::spec::cluster::{Cluster, ControllerModel};
use crate::reconciler::spec::io::{VoidEReqView, VoidERespView};
use crate::vdeployment_controller::model::reconciler::*;
use crate::vdeployment_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

impl Marshallable for VDeploymentReconcileState {
    uninterp spec fn marshal(self) -> Value;

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()).is_Ok() && o == Self::unmarshal(o.marshal()).get_Ok_0()
    {}
}

pub open spec fn vd_controller_model() -> ControllerModel {
    ControllerModel {
        reconcile_model: Cluster::installed_reconcile_model::<VDeploymentReconciler, VDeploymentReconcileState, VDeploymentView, VoidEReqView, VoidERespView>(),
        external_model: None,
    }
}

}
