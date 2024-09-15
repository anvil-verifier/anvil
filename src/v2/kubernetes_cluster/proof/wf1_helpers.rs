// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::v2::kubernetes_cluster::spec::{
    api_server::state_machine::api_server,
    api_server::types::*,
    builtin_controllers::state_machine::builtin_controllers,
    builtin_controllers::types::*,
    cluster_state_machine::*,
    controller::state_machine::{controller, init_controller_state},
    controller::types::*,
    external::state_machine::external,
    external::types::*,
    message::*,
    network::state_machine::network,
    network::types::*,
};
use vstd::prelude::*;

verus! {

impl Cluster {

pub proof fn lemma_pre_leads_to_post_by_api_server(
    self, spec: TempPred<ClusterState>, input: Option<Message>, next: ActionPred<ClusterState>,
    step: APIServerStep, pre: StatePred<ClusterState>, post: StatePred<ClusterState>
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

pub proof fn api_server_action_pre_implies_next_pre(self, step: APIServerStep, input: Option<Message>)
    ensures valid(lift_state(self.api_server_action_pre(step, input)).implies(lift_state(self.api_server_next().pre(input)))),
{
    assert forall |s| #[trigger] self.api_server_action_pre(step, input)(s) implies self.api_server_next().pre(input)(s) by {
        let action = (self.api_server().step_to_action)(step);
        let action_input = APIServerActionInput{recv: input};
        assert((action.precondition)(action_input, s.api_server));
    };
}

pub proof fn builtin_controllers_action_pre_implies_next_pre(self, step: BuiltinControllersStep, input: (BuiltinControllerChoice, ObjectRef))
    ensures valid(lift_state(self.builtin_controllers_action_pre(step, input)).implies(lift_state(self.builtin_controllers_next().pre(input)))),
{
    assert forall |s| #[trigger] self.builtin_controllers_action_pre(step, input)(s) implies self.builtin_controllers_next().pre(input)(s) by {
        let action = (self.builtin_controllers().step_to_action)(step);
        let action_input = BuiltinControllersActionInput{choice: input.0, key: input.1, rpc_id_allocator: s.rpc_id_allocator, resources: s.api_server.resources};
        assert((action.precondition)(action_input, ()));
    };
}

pub proof fn controller_action_pre_implies_next_pre(self, step: ControllerStep, input: (int, Option<Message>, Option<ObjectRef>))
    ensures valid(lift_state(self.controller_action_pre(step, input)).implies(lift_state(self.controller_next().pre(input)))),
{
    assert forall |s| #[trigger] self.controller_action_pre(step, input)(s) implies self.controller_next().pre(input)(s) by {
        let action = (self.controller(input.0).step_to_action)(step);
        let action_input = ControllerActionInput{recv: input.1, scheduled_cr_key: input.2, rpc_id_allocator: s.rpc_id_allocator};
        assert((action.precondition)(action_input, s.controller_and_externals[input.0].controller));
    };
}

pub proof fn external_action_pre_implies_next_pre(self, step: ExternalStep, input: (int, Option<Message>))
    ensures valid(lift_state(self.external_action_pre(step, input)).implies(lift_state(self.external_next().pre(input)))),
{
    assert forall |s| #[trigger] self.external_action_pre(step, input)(s) implies self.external_next().pre(input)(s) by {
        let action = (self.external(input.0).step_to_action)(step);
        let action_input = ExternalActionInput{recv: input.1, resources: s.api_server.resources};
        assert((action.precondition)(action_input, s.controller_and_externals[input.0].external.get_Some_0()));
    };
}

}

}
