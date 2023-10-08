// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit_config::{
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

pub open spec fn liveness(fbc: FluentBitConfigView) -> TempPred<FBCCluster>
    recommends
        fbc.well_formed(),
{
    always(lift_state(desired_state_is(fbc)))
        .leads_to(always(lift_state(current_state_matches(fbc))))
}

pub open spec fn current_state_matches(fbc: FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        forall |sub_resource: SubResource|
            #[trigger] resource_state_matches(sub_resource, fbc, s.resources())
    }
}

}
