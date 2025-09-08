use crate::kubernetes_api_objects::spec::{prelude::*, pod_template_spec::*};
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::{spec_types::*, util::*};
use crate::vreplicaset_controller::trusted::liveness_theorem::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{

pub open spec fn vd_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vd| current_state_matches(vd))
}

pub open spec fn vd_eventually_stable_reconciliation_per_cr(vd: VDeploymentView) -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation_per_cr(vd, |vd| current_state_matches(vd))
}

// draft of ESR for VDeployment
// TODO: add another version which talks about pods and derives from VRS ESR and this ESR
// Also try using quantifiers to simplify the proofs
pub open spec fn current_state_matches(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj_keys = filter_obj_keys_managed_by_vd(vd, s);
        &&& exists |new_k: ObjectRef| {
            // owned by vd, match template and has desired replicas
            let new_obj = s.resources()[new_k];
            let new_vrs = VReplicaSetView::unmarshal(new_obj)->Ok_0;
            &&& s.resources().contains_key(new_k)
            &&& #[trigger] obj_keys.contains(new_k)
            &&& VReplicaSetView::unmarshal(new_obj) is Ok
            &&& new_vrs_filter(vd.spec.template)(new_vrs)
            &&& new_vrs.spec.replicas.unwrap_or(int1!()) == vd.spec.replicas.unwrap_or(int1!())
            // all old vrs have 0 replicas
            &&& new_vrs.metadata.uid is Some
            &&& forall |old_k: ObjectRef| !{
                let old_obj = s.resources()[old_k];
                let old_vrs = VReplicaSetView::unmarshal(old_obj)->Ok_0;
                &&& #[trigger] obj_keys.contains(old_k)
                &&& s.resources().contains_key(old_k)
                &&& VReplicaSetView::unmarshal(old_obj) is Ok
                &&& old_vrs_filter(new_vrs.metadata.uid)(old_vrs)
            }
        }
    }
}

// simulate API server list filter
pub open spec fn list_vrs_filter(namespace: StringView) -> spec_fn(DynamicObjectView) -> bool {
    |o: DynamicObjectView| {
        &&& o.object_ref().namespace == namespace
        &&& o.object_ref().kind == VReplicaSetView::kind()
    }
}

pub open spec fn new_vrs_filter(template: PodTemplateSpecView) -> spec_fn(VReplicaSetView) -> bool {
    |vrs: VReplicaSetView| match_template_without_hash(template, vrs)
}

// None -> no new vrs
pub open spec fn old_vrs_filter(new_vrs_uid: Option<Uid>) -> spec_fn(VReplicaSetView) -> bool {
    |vrs: VReplicaSetView| {
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas.unwrap_or(1) > 0
    }
}

// can be unmarshalled and unmarshalled vrs can pass valid_owned_vrs
pub open spec fn valid_owned_obj(vd: VDeploymentView) -> spec_fn(DynamicObjectView) -> bool {
    |o: DynamicObjectView| {
        &&& o.kind == VReplicaSetView::kind()
        &&& VReplicaSetView::unmarshal(o) is Ok
        &&& valid_owned_vrs(VReplicaSetView::unmarshal(o).unwrap(), vd)
    }
}

pub open spec fn filter_obj_keys_managed_by_vd(vd: VDeploymentView, s: ClusterState) -> Set<ObjectRef> {
    s.resources().dom().filter(|k: ObjectRef| valid_owned_obj(vd)(s.resources()[k]))
}

}