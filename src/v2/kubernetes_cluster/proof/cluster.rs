// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::v2::kubernetes_cluster::spec::{cluster_state_machine::*, message::*};
use vstd::prelude::*;

verus! {

impl Cluster {

pub proof fn lemma_always_there_is_the_controller_state(self, spec: TempPred<ClusterState>, controller_id: int)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::controller_exists(controller_id)))),
{
    let invariant = Self::controller_exists(controller_id);
    init_invariant::<ClusterState>(spec, self.init(), self.next(), invariant);
}

}

}
