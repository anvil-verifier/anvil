// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::v2::kubernetes_cluster::spec::{
    cluster_state_machine::*, external::types::*, message::*,
};
use vstd::prelude::*;

verus! {

impl Cluster {

pub proof fn lemma_pre_leads_to_post_by_external(
    self, spec: TempPred<ClusterState>, controller_id: int, input: Option<Message>, next: ActionPred<ClusterState>,
    step: ExternalStep, pre: StatePred<ClusterState>, post: StatePred<ClusterState>
)
    requires
        forall |s, s_prime| pre(s) && #[trigger] next(s, s_prime) ==> pre(s_prime) || post(s_prime),
        forall |s, s_prime| pre(s) && #[trigger] next(s, s_prime) && self.external_next().forward((controller_id, input))(s, s_prime) ==> post(s_prime),
        forall |s| #[trigger] pre(s) ==> self.external_action_pre(step, (controller_id, input))(s),
        spec.entails(always(lift_action(next))),
        spec.entails(tla_forall(|i| self.external_next().weak_fairness((controller_id, i)))),
    ensures spec.entails(lift_state(pre).leads_to(lift_state(post))),
{
    use_tla_forall::<ClusterState, Option<Message>>(spec, |i| self.external_next().weak_fairness((controller_id, i)), input);
    self.external_action_pre_implies_next_pre(step, (controller_id, input));
    valid_implies_trans::<ClusterState>(
        lift_state(pre),
        lift_state(self.external_action_pre(step, (controller_id, input))),
        lift_state(self.external_next().pre((controller_id, input)))
    );
    self.external_next().wf1((controller_id, input), spec, next, pre, post);
}

}

}
