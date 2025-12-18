use crate::kubernetes_api_objects::{error::*, spec::prelude::*};
use crate::kubernetes_cluster::spec::cluster::{Cluster, ControllerModel};
use crate::reconciler::spec::io::{VoidEReqView, VoidERespView};
use crate::vstatefulset_controller::{
    model::reconciler::*,
    trusted::spec_types::*
};
use vstd::prelude::*;

verus! {

impl Marshallable for VStatefulSetReconcileState {
    uninterp spec fn marshal(self) -> Value;

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()) is Ok && o == Self::unmarshal(o.marshal())->Ok_0
    {}
}

pub open spec fn vsts_controller_model() -> ControllerModel {
    ControllerModel {
        reconcile_model: Cluster::installed_reconcile_model::<VStatefulSetReconciler, VStatefulSetReconcileState, VStatefulSetView, VoidEReqView, VoidERespView>(),
        external_model: None,
    }
}

}