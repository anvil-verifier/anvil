// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_cluster::spec::cluster_state_machine::*;
use vstd::prelude::*;

verus! {

impl Cluster {

// Prove weak_fairness is stable.
pub proof fn action_weak_fairness_is_stable<Output>(action: Action<ClusterState, (), Output>)
    ensures
        valid(stable(action.weak_fairness(()))),
{
    let split_always = always(lift_state(action.pre(()))).implies(eventually(lift_action(action.forward(()))));
    always_p_is_stable::<ClusterState>(split_always);
}

// Prove weak_fairness for all input is stable.
pub proof fn tla_forall_action_weak_fairness_is_stable<Input, Output>(
    action: Action<ClusterState, Input, Output>
)
    ensures
        valid(stable(tla_forall(|input| action.weak_fairness(input)))),
{
    let split_always = |input| always(lift_state(action.pre(input))).implies(eventually(lift_action(action.forward(input))));
    tla_forall_always_equality_variant::<ClusterState, Input>(|input| action.weak_fairness(input), split_always);
    always_p_is_stable::<ClusterState>(tla_forall(split_always));
}

}

}
