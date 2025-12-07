use vstd::prelude::*;

verus! {
    #[derive(Copy)]
    pub enum VStatefulSetReconcileStep {
        Init,
        AfterListPod,
        GetPVC,
        AfterGetPVC,
        CreatePVC,
        AfterCreatePVC,
        SkipPVC,
        CreateNeeded,
        AfterCreateNeeded,
        UpdateNeeded,
        AfterUpdateNeeded,
        DeleteCondemned,
        AfterDeleteCondemned,
        DeleteOutdated,
        AfterDeleteOutdated,
        Done,
        Error,
    }

    impl std::clone::Clone for VStatefulSetReconcileStep {
        fn clone(&self) -> (result: Self)
            ensures result == self
        { *self }
    }

    impl View for VStatefulSetReconcileStep {
        type V = VStatefulSetReconcileStepView;

        open spec fn view(&self) -> Self::V {
            match self {
                VStatefulSetReconcileStep::Init => VStatefulSetReconcileStepView::Init,
                VStatefulSetReconcileStep::AfterListPod => VStatefulSetReconcileStepView::AfterListPod,
                VStatefulSetReconcileStep::GetPVC => VStatefulSetReconcileStepView::GetPVC,
                VStatefulSetReconcileStep::AfterGetPVC => VStatefulSetReconcileStepView::AfterGetPVC,
                VStatefulSetReconcileStep::CreatePVC => VStatefulSetReconcileStepView::CreatePVC,
                VStatefulSetReconcileStep::AfterCreatePVC => VStatefulSetReconcileStepView::AfterCreatePVC,
                VStatefulSetReconcileStep::SkipPVC => VStatefulSetReconcileStepView::SkipPVC,
                VStatefulSetReconcileStep::CreateNeeded => VStatefulSetReconcileStepView::CreateNeeded,
                VStatefulSetReconcileStep::AfterCreateNeeded => VStatefulSetReconcileStepView::AfterCreateNeeded,
                VStatefulSetReconcileStep::UpdateNeeded => VStatefulSetReconcileStepView::UpdateNeeded,
                VStatefulSetReconcileStep::AfterUpdateNeeded => VStatefulSetReconcileStepView::AfterUpdateNeeded,
                VStatefulSetReconcileStep::DeleteCondemned => VStatefulSetReconcileStepView::DeleteCondemned,
                VStatefulSetReconcileStep::AfterDeleteCondemned => VStatefulSetReconcileStepView::AfterDeleteCondemned,
                VStatefulSetReconcileStep::DeleteOutdated => VStatefulSetReconcileStepView::DeleteOutdated,
                VStatefulSetReconcileStep::AfterDeleteOutdated => VStatefulSetReconcileStepView::AfterDeleteOutdated,
                VStatefulSetReconcileStep::Done => VStatefulSetReconcileStepView::Done,
                VStatefulSetReconcileStep::Error => VStatefulSetReconcileStepView::Error,
            }
        }
    }

    pub enum VStatefulSetReconcileStepView {
        Init,
        AfterListPod,
        GetPVC,
        AfterGetPVC,
        CreatePVC,
        AfterCreatePVC,
        SkipPVC,
        CreateNeeded,
        AfterCreateNeeded,
        UpdateNeeded,
        AfterUpdateNeeded,
        DeleteCondemned,
        AfterDeleteCondemned,
        DeleteOutdated,
        AfterDeleteOutdated,
        Done,
        Error,
    }
}