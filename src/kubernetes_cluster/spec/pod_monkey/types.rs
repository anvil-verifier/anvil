use crate::kubernetes_api_objects::spec::pod::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::{action::*, state_machine::*};
use vstd::{multiset::*, prelude::*};

verus! {

pub type PodMonkeyState = ();

pub enum PodMonkeyStep {
    CreatePod,
    UpdatePod,
    UpdatePodStatus,
    DeletePod,
}

pub struct PodMonkeyActionInput {
    pub pod: PodView,
    pub rpc_id_allocator: RPCIdAllocator,
}

pub struct PodMonkeyActionOutput {
    pub send: Multiset<Message>,
    pub rpc_id_allocator: RPCIdAllocator,
}

pub type PodMonkeyStateMachine = StateMachine<PodMonkeyState, PodMonkeyActionInput, PodMonkeyActionInput, PodMonkeyActionOutput, PodMonkeyStep>;

pub type PodMonkeyAction = Action<PodMonkeyState, PodMonkeyActionInput, PodMonkeyActionOutput>;

}
