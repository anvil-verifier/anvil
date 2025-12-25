use crate::kubernetes_api_objects::spec::{prelude::*, pod_template_spec::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*, controller::types::ReconcileLocalState};
use crate::temporal_logic::defs::*;
use crate::vstatefulset_controller::{
    model::reconciler::*,
    trusted::{spec_types::*, step::VStatefulSetReconcileStepView::*},
    proof::predicate::*
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{

pub open spec fn current_state_matches(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // 1. managed pods exist
        let owned_objs = s.resources().values().filter(owned_selector_match_is(vsts));
        &&& forall |ord: nat| #![trigger pod_name(vsts.metadata.name->0, ord)] 0 <= ord < vsts.spec.replicas.unwrap_or(1) ==>
            exists |obj| #[trigger] owned_objs.contains(obj) && obj.metadata.name->0 == pod_name(vsts.metadata.name->0, ord)
        // 2. managed PVCs exist
    }
}

// filter_pods on dyn with additional filter on namespace
pub open spec fn owned_selector_match_is(vsts: VStatefulSetView) -> spec_fn(DynamicObjectView) -> bool {
    |obj: DynamicObjectView| {
        &&& obj.kind == PodView::kind()
        &&& obj.metadata.name is Some
        &&& obj.metadata.namespace is Some
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        &&& vsts.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
        &&& exists |ord| obj.metadata.name->0 == #[trigger] pod_name(vsts.metadata.name->0, ord)
    }
}

}