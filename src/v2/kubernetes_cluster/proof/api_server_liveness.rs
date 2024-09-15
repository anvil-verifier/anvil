// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::v2::kubernetes_cluster::spec::{
    api_server::types::*, cluster_state_machine::*, message::*,
};
use vstd::prelude::*;

verus! {

impl Cluster {

pub proof fn lemma_pre_leads_to_post_by_api_server(
    self, spec: TempPred<ClusterState>, input: Option<Message>, next: ActionPred<ClusterState>, step: APIServerStep, pre: StatePred<ClusterState>, post: StatePred<ClusterState>
)
    requires
        forall |s, s_prime| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime| pre(s) && #[trigger] next(s, s_prime) && self.api_server_next().forward(input)(s, s_prime) ==> post(s_prime),
        forall |s| #[trigger] pre(s) ==> self.api_server_action_pre(step, input)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
    ensures spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<ClusterState, Option<Message>>(spec, |i| self.api_server_next().weak_fairness(i), input);
    self.api_server_action_pre_implies_next_pre(step, input);
    valid_implies_trans::<ClusterState>(
        lift_state(pre),
        lift_state(self.api_server_action_pre(step, input)),
        lift_state(self.api_server_next().pre(input))
    );
    self.api_server_next().wf1(input, spec, next, pre, post);
}

}

}
