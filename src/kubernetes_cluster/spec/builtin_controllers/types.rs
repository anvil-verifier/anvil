use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub enum BuiltinControllersStep {
    RunGarbageCollector,
}

pub enum BuiltinControllerChoice {
    GarbageCollector,
}

pub struct BuiltinControllersActionInput {
    pub choice: BuiltinControllerChoice,
    pub key: ObjectRef,
    pub rpc_id_allocator: RPCIdAllocator,
    pub resources: StoredState,
}

pub struct BuiltinControllersActionOutput {
    pub send: Multiset<Message>,
    pub rpc_id_allocator: RPCIdAllocator,
}

pub type BuiltinControllersStateMachine = StateMachine<(),
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionOutput,
                                            BuiltinControllersStep>;

pub type BuiltinControllersAction = Action<(),
                                        BuiltinControllersActionInput,
                                        BuiltinControllersActionOutput>;

}
