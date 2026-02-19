use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vstatefulset_controller::{
    model::reconciler::*,
    trusted::{spec_types::*, step::VStatefulSetReconcileStepView::*},
};
use vstd::prelude::*;

verus !{

pub open spec fn vsts_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vrs| current_state_matches(vsts))
}

pub open spec fn vsts_eventually_stable_reconciliation_per_cr(vrs: VStatefulSetView) -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation_per_cr(vrs, |vrs| current_state_matches(vsts))
}

pub open spec fn current_state_matches(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // 1. All needed pods exist and are up-to-date
        // TODO: cover updates to pod.spec.{volumes|hostname|subdomain} and pod.metadata.labels
        &&& forall |ord: nat| ord < replicas(vsts) ==> {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: #[trigger] pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s.resources()[key];
            &&& s.resources().contains_key(key)
            // spec is updated
            &&& PodView::unmarshal(obj) is Ok
            &&& pod_spec_matches(vsts, PodView::unmarshal(obj)->Ok_0)
            // labels are updated
            // note: this can be easily proved with obj.metadata->0.labels == vsts.spec.template.metadata->0.labels
            &&& vsts.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
        }
        // 2. Bound PVCs exist
        &&& forall |ord: nat, i: nat| ord < replicas(vsts) && i < pvc_cnt(vsts) ==> {
            let pvc_key = ObjectRef {
                kind: PersistentVolumeClaimView::kind(),
                name: #[trigger] pvc_name(
                    vsts.spec.volume_claim_templates->0[i as int].metadata.name->0,
                    vsts.metadata.name->0,
                    ord
                ),
                namespace: vsts.metadata.namespace->0
            };
            &&& s.resources().contains_key(pvc_key)
        }
        // 3. No condemned pod in etcd
        &&& !exists |ord: nat| ord >= replicas(vsts) && {
            let key = ObjectRef {
                kind: PodView::kind(),
                name: #[trigger] pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            &&& s.resources().contains_key(key)
        }
    }
}

pub open spec fn pvc_cnt(vsts: VStatefulSetView) -> nat {
    match vsts.spec.volume_claim_templates {
        Some(pvc_templates) => pvc_templates.len(),
        None => 0,
    }
}

pub open spec fn replicas(vsts: VStatefulSetView) -> nat {
    match vsts.spec.replicas {
        Some(r) => r as nat,
        None => 1,
    }
}

}