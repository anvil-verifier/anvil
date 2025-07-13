use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{external::types::*, message::*};
use crate::state_machine::{action::*, state_machine::*};
use vstd::{multiset::*, prelude::*};

verus! {

pub open spec fn transition_by_external(model: ExternalModel, req_msg: Message, resources: StoredState, s: ExternalState) -> (ExternalState, Message)
    recommends
        req_msg.content.is_ExternalRequest(),
{
    let (inner_s_prime, resp) = (model.transition)(req_msg.content.get_ExternalRequest_0(), s.state, resources);
    let s_prime = ExternalState {
        state: inner_s_prime,
        ..s
    };
    let resp_msg = form_external_resp_msg(req_msg, resp);
    (s_prime, resp_msg)
}

pub open spec fn handle_external_request(model: ExternalModel) -> ExternalAction {
    Action {
        precondition: |input: ExternalActionInput, s: ExternalState| {
            &&& input.recv is Some
            &&& input.recv->0.content.is_ExternalRequest()
        },
        transition: |input: ExternalActionInput, s: ExternalState| {
            let req_msg = input.recv->0;
            let resources = input.resources;
            let (s_prime, resp_msg) = transition_by_external(model, req_msg, resources, s);
            (s_prime, ExternalActionOutput {
                send: Multiset::singleton(resp_msg),
            })
        },
    }
}

pub open spec fn external(model: ExternalModel) -> ExternalStateMachine {
    StateMachine {
        init: |s: ExternalState| {
            s.state == (model.init)()
        },
        actions: set![handle_external_request(model)],
        step_to_action: |step: ExternalStep| {
            match step {
                ExternalStep::HandleExternalRequest => handle_external_request(model),
            }
        },
        action_input: |step: ExternalStep, input: ExternalActionInput| {
            input
        }
    }
}

}
