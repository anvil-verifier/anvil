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
        let owned_dyn_pods = s.resources().values().filter(owned_dyn_pods_filter(vsts));
        let pvc_template_cnt = if vsts.spec.volume_claim_templates is Some {
            vsts.spec.volume_claim_templates->0.len()
        } else {0};
        // 1. All needed pods exist and are up-to-date
        &&& forall |ord: nat| #![trigger pod_name(vsts.metadata.name->0, ord)] 0 <= ord < vsts.spec.replicas.unwrap_or(1) ==> {
            &&& exists |obj| {
                &&& #[trigger] owned_dyn_pods.contains(obj)
                &&& obj.metadata.name->0 == pod_name(vsts.metadata.name->0, ord)
                &&& PodView::unmarshal_spec(obj.spec) is Ok
                &&& PodView::unmarshal_spec(obj.spec)->Ok_0 == vsts.spec.template.spec
            }
            // 2. Bound PVCs exist
            &&& forall |i: int| #![trigger vsts.spec.volume_claim_templates->0[i]] 0 <= i < pvc_template_cnt ==> {
                let pvc_template_name = vsts.spec.volume_claim_templates->0[i].metadata.name->0;
                &&& exists |obj| #[trigger] s.resources().contains_value(obj)
                &&& bound_dyn_pvc_filter(pvc_template_name, vsts, ord)(obj)
            }
        }
        // 3. No condemned pod in etcd
        &&& forall |ord: nat| #![trigger pod_name(vsts.metadata.name->0, ord)] ord >= vsts.spec.replicas.unwrap_or(1) ==> {
            !exists |obj| #[trigger] owned_dyn_pods.contains(obj) && obj.metadata.name->0 == pod_name(vsts.metadata.name->0, ord)
        }
    }
}

// filter_pods on dyn with additional filter on namespace
pub open spec fn owned_dyn_pods_filter(vsts: VStatefulSetView) -> spec_fn(DynamicObjectView) -> bool {
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

pub open spec fn bound_dyn_pvc_filter(pvc_template_name: StringView, vsts: VStatefulSetView, ord: nat) -> spec_fn(DynamicObjectView) -> bool {
    |obj: DynamicObjectView| {
        &&& obj.kind == PersistentVolumeClaimView::kind()
        &&& obj.metadata.name is Some
        &&& obj.metadata.namespace is Some
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& obj.metadata.name->0 == pvc_name(pvc_template_name, vsts.metadata.name->0, ord)
    }
}

}