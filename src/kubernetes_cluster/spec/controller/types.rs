use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct ControllerState {
    pub ongoing_reconciles: Map<ObjectRef, OngoingReconcile>,
    pub scheduled_reconciles: Map<ObjectRef, DynamicObjectView>,
    pub reconcile_id_allocator: ReconcileIdAllocator,
}

pub type ReconcileLocalState = Value;

pub enum RequestContent {
    KubernetesRequest(APIRequest),
    ExternalRequest(ExternalRequest),
}

pub enum ResponseContent {
    KubernetesResponse(APIResponse),
    ExternalResponse(ExternalResponse),
}

pub type ReconcileId = nat;

// ReconcileIdAllocator allocates unique ReconcileId for each reconcile on a
// given controller_id.
pub struct ReconcileIdAllocator {
    pub reconcile_id_counter: ReconcileId,
}

impl ReconcileIdAllocator {
    // Allocate a ReconcileId which is the current reconcile_id_counter
    // and also returns a new ReconcileIdAllocator with a different reconcile_id_counter.
    //
    // The user (i.e., state machine) after allocating one ReconcileId, should use
    // the returned new ReconcileIdAllocator to allocate the next ReconcileId.
    // By doing so, the user of ReconcileIdAllocator always gets a ReconcileId
    // which differs from all the ReconcileIds allocated before because the
    // returned ReconcileIdAllocator has a incremented reconcile_id_counter.
    //
    // Besides the uniqueness, the allocated ReconcileId can also serve as a timestamp
    // if we need to say some reconciles happen before others.
    pub open spec fn allocate(self) -> (Self, ReconcileId) {
        (ReconcileIdAllocator {
            reconcile_id_counter: self.reconcile_id_counter + 1,
        }, self.reconcile_id_counter)
    }
}

pub struct ReconcileModel {
    pub kind: Kind,
    pub init: spec_fn() -> ReconcileLocalState,
    pub transition: spec_fn(DynamicObjectView, Option<ResponseContent>, ReconcileLocalState) -> (ReconcileLocalState, Option<RequestContent>),
    pub done: spec_fn(ReconcileLocalState) -> bool,
    pub error: spec_fn(ReconcileLocalState) -> bool,
}

pub struct OngoingReconcile {
    pub triggering_cr: DynamicObjectView,
    pub pending_req_msg: Option<Message>,
    pub local_state: ReconcileLocalState,
    pub reconcile_id: ReconcileId,
}

pub enum ControllerStep {
    RunScheduledReconcile,
    ContinueReconcile,
    EndReconcile,
}

pub struct ControllerActionInput {
    pub recv: Option<Message>,
    pub scheduled_cr_key: Option<ObjectRef>,
    pub rpc_id_allocator: RPCIdAllocator,
}

pub struct ControllerActionOutput {
    pub send: Multiset<Message>,
    pub rpc_id_allocator: RPCIdAllocator,
}

pub type ControllerStateMachine = StateMachine<ControllerState, ControllerActionInput, ControllerActionInput, ControllerActionOutput, ControllerStep>;

pub type ControllerAction = Action<ControllerState, ControllerActionInput, ControllerActionOutput>;

}
