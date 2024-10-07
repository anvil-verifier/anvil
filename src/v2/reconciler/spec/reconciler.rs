use crate::kubernetes_api_objects::spec::{api_method::*, common::*, dynamic::*, resource::*};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus! {

// Reconciler is used to model the custom controller as a state machine
// and install it to the Kubernetes cluster state machine.
//
// S: type of the reconciler state of the reconciler.
// K: type of the custom resource.
// EReq: type of request the controller sends to the external systems (if any).
// EResp: type of response the controller receives from the external systems (if any).
//
// The only reason that we don't make the types above as associated types is that
// we need to connect this spec Reconciler to the exec Reconciler to pose the proof obligation
// on the reconciler implementation. To do so, the exec Reconciler needs to pose a constraint
// on its S, K, EReq and EResp that their views are the same type as the spec Reconciler's S, K, EReq and EResp
// correspondingly. Since Rust doesn't support type equality constraint (see https://github.com/rust-lang/rust/issues/20041),
// instead of stating the equality constraint, we state that the spec Reconciler is built
// using the views of the exec Reconciler's S, K, EReq and EResp.
pub trait Reconciler<S, K, EReq, EResp> {
    // reconcile_init_state returns the initial local state that the reconciler starts
    // its reconcile function with.
    spec fn reconcile_init_state() -> S;

    // reconcile_core describes the logic of reconcile function and is the key logic we want to verify.
    // Each reconcile_core should take the local state and a response of the previous request (if any) as input
    // and outputs the next local state and the request to send to API server (if any).
    spec fn reconcile_core(cr: K, resp_o: Option<ResponseView<EResp>>, state: S) -> (S, Option<RequestView<EReq>>);

    // reconcile_done is used to tell the controller_runtime whether this reconcile round is done.
    // If it is true, controller_runtime will requeue the reconcile.
    spec fn reconcile_done(state: S) -> bool;

    // reconcile_error is used to tell the controller_runtime whether this reconcile round returns with error.
    // If it is true, controller_runtime will requeue the reconcile with a typically shorter waiting time.
    spec fn reconcile_error(state: S) -> bool;
}

}
