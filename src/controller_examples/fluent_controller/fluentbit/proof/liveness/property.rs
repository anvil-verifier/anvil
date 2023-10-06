// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::{
    common::*,
    proof::{liveness::spec::*, predicate::*, resource::*},
    spec::{reconciler::*, types::*},
};
use crate::kubernetes_api_objects::prelude::*;
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub open spec fn liveness(fb: FluentBitView) -> TempPred<FBCluster>
    recommends
        fb.well_formed(),
{
    always(lift_state(desired_state_is(fb)))
        .leads_to(always(lift_state(current_state_matches(fb))))
}

pub open spec fn current_state_matches(fb: FluentBitView) -> StatePred<FBCluster> {
    |s: FBCluster| {
        forall |sub_resource: SubResource|
            #[trigger] resource_state_matches(sub_resource, fb, s.resources())
    }
}

}
