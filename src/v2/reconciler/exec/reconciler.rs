use crate::kubernetes_api_objects::spec::resource::{CustomResourceView, ResourceView};
use crate::reconciler::exec::io::*;
use crate::reconciler::spec::reconciler::Reconciler as ModelReconciler;
use crate::vstd_ext::option_lib::*;
use vstd::prelude::*;

verus! {

// Reconciler is used to implement the custom controller as a state machine
// that interacts with Kubernetes API server via the shim_layer::controller_runtime.
pub trait Reconciler
where
    Self::S: View,
    Self::K: View,
    <Self::K as View>::V: CustomResourceView,
    Self::EReq: View,
    Self::EResp: View,
    // The ModelReconciler is built using the view of S, K, EReq and EResp.
    // This is a workaround of missing type equality constraint in Rust.
    Self::M: ModelReconciler<<Self::S as View>::V, <Self::K as View>::V, <Self::EReq as View>::V, <Self::EResp as View>::V>,
{
    // S: type of the reconciler state of the reconciler.
    type S;
    // K: type of the custom resource.
    type K;
    // EReq: type of request the controller sends to the external systems (if any).
    type EReq;
    // EResp: type of response the controller receives from the external systems (if any).
    type EResp;
    // M: type of the ModelReconciler that this implementation should conform to.
    type M;

    // reconcile_init_state returns the initial local state that the reconciler starts
    // its reconcile function with.
    // It conforms to the model's reconcile_init_state.
    fn reconcile_init_state() -> (state: Self::S)
        ensures state@ == Self::M::reconcile_init_state();

    // reconcile_core describes the logic of reconcile function and is the key logic we want to verify.
    // Each reconcile_core should take the local state and a response of the previous request (if any) as input
    // and outputs the next local state and the request to send to API server (if any).
    // It conforms to the model's reconcile_core.
    fn reconcile_core(cr: &Self::K, resp_o: Option<Response<Self::EResp>>, state: Self::S) -> (res: (Self::S, Option<Request<Self::EReq>>))
        requires cr@.metadata().well_formed() && cr@.state_validation(),
        ensures (res.0@, option_view(res.1)) == Self::M::reconcile_core(cr@, option_view(resp_o), state@);

    // reconcile_done is used to tell the controller_runtime whether this reconcile round is done.
    // If it is true, controller_runtime will requeue the reconcile.
    // It conforms to the model's reconcile_done.
    fn reconcile_done(state: &Self::S) -> (res: bool)
        ensures res == Self::M::reconcile_done(state@);

    // reconcile_error is used to tell the controller_runtime whether this reconcile round returns with error.
    // If it is true, controller_runtime will requeue the reconcile with a typically shorter waiting time.
    // It conforms to the model's reconciler_error.
    fn reconcile_error(state: &Self::S) -> (res: bool)
        ensures res == Self::M::reconcile_error(state@);
}

}
