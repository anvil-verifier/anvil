use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vdeployment_controller::{
    trusted::{step::*, spec_types::*},
    model::{install::*, reconciler::*},
};
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    //cluster::*, 
    //message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_cluster::spec::cluster::*;
use vstd::prelude::*;

verus! {

// Represents a reconcile step (optionally with a predicate) for use in spec functions.
//
// Usage:
//
// Step-only case
// let step1 = StepCase::Plain(Step1);
//
// Step with an additional predicate over VDeploymentReconcileState
// let step2 = StepCase::WithPred(Step2, |vds: VDeploymentReconcileState| vds.some_field == 5);
//
// Convert into a predicate over ReconcileLocalState (used in Cluster::at_expected_reconcile_states)
// let pred_local: spec_fn(ReconcileLocalState) -> bool = step1.into_local_state_pred();
//
// Convert into a predicate over ClusterState
// let pred_cluster: spec_fn(ClusterState) -> bool = step2.into_cluster_state_pred(controller_id, vd);
//
// Convert into a temporal predicate over ClusterState (for use in TempPred context)
// let temp_pred: TempPred<ClusterState> = step1.into_temporal_pred(controller_id, vd);
pub enum StepCase {
    Plain(VDeploymentReconcileStepView),
    WithPred(VDeploymentReconcileStepView, spec_fn(VDeploymentReconcileState) -> bool),
}

pub trait IntoSpec: Sized {
    spec fn into_local_state_pred(self) -> spec_fn(ReconcileLocalState) -> bool;
    spec fn into_cluster_state_pred(self, controller_id: int, vd: VDeploymentView) -> spec_fn(ClusterState) -> bool;
    spec fn into_temporal_pred(self, controller_id: int, vd: VDeploymentView) -> TempPred<ClusterState>;
    broadcast proof fn lemma_cluster_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred());
    broadcast proof fn lemma_temporal_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(self.into_cluster_state_pred(controller_id, vd)),
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(
                Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
            );
}

pub broadcast group into_spec_all {
    IntoSpec::lemma_cluster_equiv,
    IntoSpec::lemma_temporal_equiv,
}

impl IntoSpec for StepCase {
    open spec fn into_local_state_pred(self) -> spec_fn(ReconcileLocalState) -> bool {
        |s: ReconcileLocalState| {
            // VDeploymentReconcileState::marshal_preserves_integrity() may be called to prove
            let st = VDeploymentReconcileState::unmarshal(s).unwrap();
            match self {
                StepCase::Plain(step) => st.reconcile_step == step,
                StepCase::WithPred(step, pred) => st.reconcile_step == step && pred(st),
            }
        }
    }
    open spec fn into_cluster_state_pred(self, controller_id: int, vd: VDeploymentView) -> spec_fn(ClusterState) -> bool {
        |s: ClusterState| {
            Cluster::at_expected_reconcile_states(
                controller_id,
                vd.object_ref(),
                self.into_local_state_pred(),
            )(s)
        }
    }
    open spec fn into_temporal_pred(self, controller_id: int, vd: VDeploymentView) -> TempPred<ClusterState> {
        lift_state(self.into_cluster_state_pred(controller_id, vd))
    }
    broadcast proof fn lemma_cluster_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
    {
        assert(self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred()));
    }
    broadcast proof fn lemma_temporal_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(self.into_cluster_state_pred(controller_id, vd)),
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(
                Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
            )
    {
        self.lemma_cluster_equiv(controller_id, vd);
    }
}

// TODO: add transitivity lemma
impl IntoSpec for (StepCase, StepCase) {
    open spec fn into_local_state_pred(self) -> spec_fn(ReconcileLocalState) -> bool {
        let (s1, s2) = self;
        let f1 = s1.into_local_state_pred();
        let f2 = s2.into_local_state_pred();
        |s| f1(s) || f2(s)
    }
    // compose s1 and s1 at ReconcileLocalState level
    open spec fn into_cluster_state_pred(self, controller_id: int, vd: VDeploymentView) -> spec_fn(ClusterState) -> bool {
        let (s1, s2) = self;
        let f1 = s1.into_local_state_pred();
        let f2 = s2.into_local_state_pred();
        |s: ClusterState| {
            Cluster::at_expected_reconcile_states(
                controller_id,
                vd.object_ref(),
                |ls: ReconcileLocalState| f1(ls) || f2(ls),
            )(s)
        }
    }
    open spec fn into_temporal_pred(self, controller_id: int, vd: VDeploymentView) -> TempPred<ClusterState> {
        lift_state(self.into_cluster_state_pred(controller_id, vd))
    }
    broadcast proof fn lemma_cluster_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
    {
        assert(self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred()));
    }
    broadcast proof fn lemma_temporal_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(self.into_cluster_state_pred(controller_id, vd)),
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(
                Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
            )
    {
        self.lemma_cluster_equiv(controller_id, vd);
    }
}

impl IntoSpec for (StepCase, StepCase, StepCase) {
    open spec fn into_local_state_pred(self) -> spec_fn(ReconcileLocalState) -> bool {
        let (s1, s2, s3) = self;
        let f1 = s1.into_local_state_pred();
        let f2 = s2.into_local_state_pred();
        let f3 = s3.into_local_state_pred();
        |s| f1(s) || f2(s) || f3(s)
    }
    open spec fn into_cluster_state_pred(self, controller_id: int, vd: VDeploymentView) -> spec_fn(ClusterState) -> bool {
        let (s1, s2, s3) = self;
        let f1 = s1.into_local_state_pred();
        let f2 = s2.into_local_state_pred();
        let f3 = s3.into_local_state_pred();
        |s: ClusterState| {
            Cluster::at_expected_reconcile_states(
                controller_id,
                vd.object_ref(),
                |ls: ReconcileLocalState| f1(ls) || f2(ls) || f3(ls),
            )(s)
        }
    }
    open spec fn into_temporal_pred(self, controller_id: int, vd: VDeploymentView) -> TempPred<ClusterState> {
        lift_state(self.into_cluster_state_pred(controller_id, vd))
    }
    broadcast proof fn lemma_cluster_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
    {
        assert(self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred()));
    }
    broadcast proof fn lemma_temporal_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(self.into_cluster_state_pred(controller_id, vd)),
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(
                Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
            )
    {
        self.lemma_cluster_equiv(controller_id, vd);
    }
}

impl IntoSpec for (StepCase, StepCase, StepCase, StepCase) {
    open spec fn into_local_state_pred(self) -> spec_fn(ReconcileLocalState) -> bool {
        let (s1, s2, s3, s4) = self;
        let f1 = s1.into_local_state_pred();
        let f2 = s2.into_local_state_pred();
        let f3 = s3.into_local_state_pred();
        let f4 = s4.into_local_state_pred();
        |s| f1(s) || f2(s) || f3(s) || f4(s)
    }
    open spec fn into_cluster_state_pred(self, controller_id: int, vd: VDeploymentView) -> spec_fn(ClusterState) -> bool {
        let (s1, s2, s3, s4) = self;
        let f1 = s1.into_local_state_pred();
        let f2 = s2.into_local_state_pred();
        let f3 = s3.into_local_state_pred();
        let f4 = s4.into_local_state_pred();
        |s: ClusterState| {
            Cluster::at_expected_reconcile_states(
                controller_id,
                vd.object_ref(),
                |ls: ReconcileLocalState| f1(ls) || f2(ls) || f3(ls) || f4(ls),
            )(s)
        }
    }
    open spec fn into_temporal_pred(self, controller_id: int, vd: VDeploymentView) -> TempPred<ClusterState> {
        lift_state(self.into_cluster_state_pred(controller_id, vd))
    }
    broadcast proof fn lemma_cluster_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
    {
        assert(self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred()));
    }
    broadcast proof fn lemma_temporal_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(self.into_cluster_state_pred(controller_id, vd)),
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(
                Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
            )
    {
        self.lemma_cluster_equiv(controller_id, vd);
    }
}

impl IntoSpec for (StepCase, StepCase, StepCase, StepCase, StepCase) {
    open spec fn into_local_state_pred(self) -> spec_fn(ReconcileLocalState) -> bool {
        let (s1, s2, s3, s4, s5) = self;
        let f1 = s1.into_local_state_pred();
        let f2 = s2.into_local_state_pred();
        let f3 = s3.into_local_state_pred();
        let f4 = s4.into_local_state_pred();
        let f5 = s5.into_local_state_pred();
        |s| f1(s) || f2(s) || f3(s) || f4(s) || f5(s)
    }
    open spec fn into_cluster_state_pred(self, controller_id: int, vd: VDeploymentView) -> spec_fn(ClusterState) -> bool {
        let (s1, s2, s3, s4, s5) = self;
        let f1 = s1.into_local_state_pred();
        let f2 = s2.into_local_state_pred();
        let f3 = s3.into_local_state_pred();
        let f4 = s4.into_local_state_pred();
        let f5 = s5.into_local_state_pred();
        |s: ClusterState| {
            Cluster::at_expected_reconcile_states(
                controller_id,
                vd.object_ref(),
                |ls: ReconcileLocalState| f1(ls) || f2(ls) || f3(ls) || f4(ls) || f5(ls),
            )(s)
        }
    }
    open spec fn into_temporal_pred(self, controller_id: int, vd: VDeploymentView) -> TempPred<ClusterState> {
        lift_state(self.into_cluster_state_pred(controller_id, vd))
    }
    broadcast proof fn lemma_cluster_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
    {
        assert(self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred()));
    }
    broadcast proof fn lemma_temporal_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(self.into_cluster_state_pred(controller_id, vd)),
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(
                Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
            )
    {
        self.lemma_cluster_equiv(controller_id, vd);
    }
}

impl IntoSpec for (StepCase, StepCase, StepCase, StepCase, StepCase, StepCase) {
    open spec fn into_local_state_pred(self) -> spec_fn(ReconcileLocalState) -> bool {
        let (s1, s2, s3, s4, s5, s6) = self;
        let f1 = s1.into_local_state_pred();
        let f2 = s2.into_local_state_pred();
        let f3 = s3.into_local_state_pred();
        let f4 = s4.into_local_state_pred();
        let f5 = s5.into_local_state_pred();
        let f6 = s6.into_local_state_pred();
        |s| f1(s) || f2(s) || f3(s) || f4(s) || f5(s) || f6(s)
    }
    open spec fn into_cluster_state_pred(self, controller_id: int, vd: VDeploymentView) -> spec_fn(ClusterState) -> bool {
        let (s1, s2, s3, s4, s5, s6) = self;
        let f1 = s1.into_local_state_pred();
        let f2 = s2.into_local_state_pred();
        let f3 = s3.into_local_state_pred();
        let f4 = s4.into_local_state_pred();
        let f5 = s5.into_local_state_pred();
        let f6 = s6.into_local_state_pred();
        |s: ClusterState| {
            Cluster::at_expected_reconcile_states(
                controller_id,
                vd.object_ref(),
                |ls: ReconcileLocalState| f1(ls) || f2(ls) || f3(ls) || f4(ls) || f5(ls) || f6(ls),
            )(s)
        }
    }
    open spec fn into_temporal_pred(self, controller_id: int, vd: VDeploymentView) -> TempPred<ClusterState> {
        lift_state(self.into_cluster_state_pred(controller_id, vd))
    }
    broadcast proof fn lemma_cluster_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
    {
        assert(self.into_cluster_state_pred(controller_id, vd) == 
            Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred()));
    }
    broadcast proof fn lemma_temporal_equiv(self, controller_id: int, vd: VDeploymentView)
        ensures
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(self.into_cluster_state_pred(controller_id, vd)),
            #[trigger] self.into_temporal_pred(controller_id, vd) == lift_state(
                Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), self.into_local_state_pred())
            )
    {
        self.lemma_cluster_equiv(controller_id, vd);
    }
}

// These macros are abandoned due to the bug in verus, see verus/discussions/1726
// If macros work better, we can switch back
// eq_step is the tricky workaround for error, see src/v2/controllers/vdeployment_controller/trusted/step.rs
//#[macro_export]
//macro_rules! at_step_internal {
//    ($vds:expr, ($step:expr, $pred:expr)) => {
//        $vds.reconcile_step.eq_step($step) && $pred($vds)
//    };
//
//    ($vds:expr, $step:expr) => {
//        $vds.reconcile_step.eq_step($step)
//    };
//
//    ($vds:expr, $head:tt, $($tail:tt)+) => {
//        at_step_internal!($vds, $head) || at_step_internal!($vds, $($tail)+)
//    };
//}
//
//// usage: at_step!(step,*)
//// step* = step | (step, pred)
//#[macro_export]
//macro_rules! at_step {
//    ( $($tokens:tt)+ ) => {
//        closure_to_fn_spec(|s: ReconcileLocalState| {
//            let vds = VDeploymentReconcileState::unmarshal(s).unwrap();
//            at_step_internal!(vds, $($tokens)+)
//        })
//    };
//}
//
//// usage: cluster_at_step!(step,*)
//#[macro_export]
//macro_rules! cluster_at_step {
//    ($controller_id:expr, $vd:expr, $($tokens:tt)+ ) => {
//        Cluster::at_expected_reconcile_states($controller_id, $vd.object_ref(), at_step!($($tokens)+))
//    }
//}
//
//// usage: temp_at_step!(step,*)
//#[macro_export]
//macro_rules! temp_at_step {
//    ($controller_id:expr, $vd:expr, $($tokens:tt)+ ) => {
//        lift_state(cluster_at_step!($controller_id, $vd, $($tokens)+))
//    }
//}
//
//// hacky workaround for type conversion bug: error[E0605]: non-primitive cast: `{integer}` as `builtin::nat`
//#[macro_export]
//macro_rules! nat0 {
//    () => {
//        spec_literal_nat("0")
//    };
//}
//
//#[macro_export]
//macro_rules! nat1 {
//    () => {
//        spec_literal_nat("1")
//    };
//}
//pub use nat0;
//pub use nat1;
//pub use at_step_internal;
//pub use at_step;
//pub use cluster_at_step;
//pub use temp_at_step;
}