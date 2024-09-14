// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::v2::kubernetes_cluster::spec::{cluster_state_machine::*, message::*};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn there_is_the_controller_state(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| s.controller_and_externals.contains_key(controller_id)
}

pub proof fn lemma_always_there_is_the_controller_state(self, spec: TempPred<ClusterState>, controller_id: int)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
{
    let invariant = Self::there_is_the_controller_state(controller_id);
    init_invariant::<ClusterState>(spec, self.init(), self.next(), invariant);
}

}

}
