use vstd::prelude::*;

verus! {

pub enum VStatefulSetReconcileStepView {
    Init,
    AfterListPod,
    AfterEnsurePod(nat),
    AfterCreatePod(nat),
    AfterCreatePVC(nat),
    AfterUpdatePod(nat),
    AfterDeletePod(nat),
    Done,
    Error,
}

}
