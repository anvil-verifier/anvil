// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
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
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

impl Cluster {

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
