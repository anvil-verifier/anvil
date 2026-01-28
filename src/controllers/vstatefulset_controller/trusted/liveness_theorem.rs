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
        let pvc_template_cnt = if vsts.spec.volume_claim_templates is Some {
            vsts.spec.volume_claim_templates->0.len()
        } else {0};
        // 1. All needed pods exist and are up-to-date
        // TODO: cover updates to pod.spec.{volumes|hostname|subdomain} and pod.metadata.labels
        &&& forall |ord: nat| #![trigger pod_name(vsts.metadata.name->0, ord)] 0 <= ord < vsts.spec.replicas.unwrap_or(1) ==> {
            let key = ObjectRef {
                kind: PodView::kind(),
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s.resources()[key];
            &&& s.resources().contains_key(key)
            // spec is updated
            &&& PodView::unmarshal(obj) is Ok
            &&& pod_matches(vsts, PodView::unmarshal(obj)->Ok_0)
            // labels are updated
            // note: this can be easily proved with obj.metadata->0.labels == vsts.spec.template.metadata->0.labels
            &&& vsts.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
            // 2. Bound PVCs exist
            &&& forall |i: int| #![trigger vsts.spec.volume_claim_templates->0[i]] 0 <= i < pvc_template_cnt ==> {
                let pvc_template = vsts.spec.volume_claim_templates->0[i];
                let pvc_key = ObjectRef {
                    kind: PersistentVolumeClaimView::kind(),
                    name: pvc_name(pvc_template.metadata.name->0, vsts.metadata.name->0, ord),
                    namespace: vsts.metadata.namespace->0
                };
                &&& s.resources().contains_key(pvc_key)
            }
        }
        // 3. No condemned pod in etcd
        &&& !exists |ord: nat| #![trigger pod_name(vsts.metadata.name->0, ord)] ord >= vsts.spec.replicas.unwrap_or(1) ==> {
            let key = ObjectRef {
                kind: PodView::kind(),
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s.resources()[key];
            &&& s.resources().contains_key(key)
            // TODO: prove the invariant
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        }
    }
}

}