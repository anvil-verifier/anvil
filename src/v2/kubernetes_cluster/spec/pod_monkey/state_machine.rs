use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{message::*, pod_monkey::types::*};
use crate::state_machine::{action::*, state_machine::*};
use vstd::{multiset::*, prelude::*};

verus! {

pub open spec fn create_pod() -> PodMonkeyAction {
    Action {
        precondition: |input: PodMonkeyActionInput, s: ()| {
            true
        },
        transition: |input: PodMonkeyActionInput, s: ()| {
            let create_req_msg = pod_monkey_req_msg(
                input.rpc_id_allocator.allocate().1,
                create_req_msg_content(
                    input.pod.metadata.namespace.get_Some_0(),
                    input.pod.marshal()
                )
            );

            let s_prime = s;
            let output = PodMonkeyActionOutput {
                send: Multiset::singleton(create_req_msg),
                rpc_id_allocator: input.rpc_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn delete_pod() -> PodMonkeyAction {
    Action {
        precondition: |input: PodMonkeyActionInput, s: ()| {
            true
        },
        transition: |input: PodMonkeyActionInput, s: ()| {
            let delete_req_msg = pod_monkey_req_msg(
                input.rpc_id_allocator.allocate().1,
                // Monkey does not need a precondition to constrain itself.
                delete_req_msg_content(input.pod.object_ref(), None)
            );

            let s_prime = s;
            let output = PodMonkeyActionOutput {
                send: Multiset::singleton(delete_req_msg),
                rpc_id_allocator: input.rpc_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn update_pod() -> PodMonkeyAction {
    Action {
        precondition: |input: PodMonkeyActionInput, s: ()| {
            true
        },
        transition: |input: PodMonkeyActionInput, s: ()| {
            let update_req_msg = pod_monkey_req_msg(
                input.rpc_id_allocator.allocate().1,
                update_req_msg_content(
                    input.pod.metadata.namespace.get_Some_0(),
                    input.pod.metadata.name.get_Some_0(),
                    input.pod.marshal()
                )
            );

            let s_prime = s;
            let output = PodMonkeyActionOutput {
                send: Multiset::singleton(update_req_msg),
                rpc_id_allocator: input.rpc_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn update_pod_status() -> PodMonkeyAction {
    Action {
        precondition: |input: PodMonkeyActionInput, s: ()| {
            true
        },
        transition: |input: PodMonkeyActionInput, s: ()| {
            let update_status_req_msg = pod_monkey_req_msg(
                input.rpc_id_allocator.allocate().1,
                update_status_req_msg_content(
                    input.pod.metadata.namespace.get_Some_0(),
                    input.pod.metadata.name.get_Some_0(),
                    input.pod.marshal()
                )
            );

            let s_prime = s;
            let output = PodMonkeyActionOutput {
                send: Multiset::singleton(update_status_req_msg),
                rpc_id_allocator: input.rpc_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn pod_monkey() -> PodMonkeyStateMachine {
    StateMachine {
        init: |s: ()| {
            true
        },
        actions: set![create_pod(), delete_pod(), update_pod(), update_pod_status()],
        step_to_action: |step: PodMonkeyStep| {
            match step {
                PodMonkeyStep::CreatePod => create_pod(),
                PodMonkeyStep::UpdatePod => update_pod(),
                PodMonkeyStep::UpdatePodStatus => update_pod_status(),
                PodMonkeyStep::DeletePod => delete_pod(),
            }
        },
        action_input: |step: PodMonkeyStep, input: PodMonkeyActionInput| {
            input
        }
    }
}

}
