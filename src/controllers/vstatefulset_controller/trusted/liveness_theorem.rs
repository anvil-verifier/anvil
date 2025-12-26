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
        &&& forall |ord: nat| #![trigger pod_name(vsts.metadata.name->0, ord)] 0 <= ord < vsts.spec.replicas.unwrap_or(1) ==> {
            let key = ObjectRef {
                kind: PodView::kind(),
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s.resources()[key];
            &&& s.resources().contains_key(key)
            // spec is updated
            &&& PodView::unmarshal_spec(obj.spec) is Ok
            &&& PodView::unmarshal_spec(obj.spec)->Ok_0 == vsts.spec.template.spec
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
            // 2. Bound PVCs exist
            &&& forall |i: int| #![trigger vsts.spec.volume_claim_templates->0[i]] 0 <= i < pvc_template_cnt ==> {
                let pvc_key = ObjectRef {
                    kind: PersistentVolumeClaimView::kind(),
                    name: vsts.spec.volume_claim_templates->0[i].metadata.name->0,
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
            &&& s.resources().contains_key(key)
        }
    }
}

}