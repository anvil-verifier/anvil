// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::fluent_controller::fluentbit_config::{
    common::*,
    spec::{reconciler::*, resource::*, types::*},
};
use crate::kubernetes_api_objects::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, cluster_state_machine::Step, message::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::string_view::int_to_string_view;
use vstd::prelude::*;

verus! {

pub open spec fn liveness_theorem() -> bool {
    forall |fbc: FluentBitConfigView| #[trigger] cluster_spec().entails(liveness(fbc))
}

pub open spec fn cluster_spec() -> TempPred<FBCCluster> {
    FBCCluster::sm_spec()
}

pub open spec fn liveness(fbc:FluentBitConfigView) -> TempPred<FBCCluster> {
    always(lift_state(desired_state_is(fbc))).leads_to(always(lift_state(current_state_matches(fbc))))
}

pub open spec fn desired_state_is(fbc:FluentBitConfigView) -> StatePred<FBCCluster> {
    FBCCluster::desired_state_is(fbc)
}

pub open spec fn current_state_matches(fbc:FluentBitConfigView) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        forall |sub_resource: SubResource|
            #[trigger] resource_state_matches(sub_resource, fbc, s.resources())
    }
}

pub open spec fn resource_state_matches(sub_resource: SubResource, fbc:FluentBitConfigView, resources: StoredState) -> bool {
    match sub_resource {
        SubResource::Secret => {
            let key = make_secret_key(fbc);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& SecretView::unmarshal(obj).is_Ok()
            &&& SecretView::unmarshal(obj).get_Ok_0().data == make_secret(fbc).data
        }
    }
}

}
