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
// *indeed simplified version of etcd_state_is
pub open spec fn current_state_matches(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // new vrs exists and only one exists
        // at most one exists is enforced by filter_old_vrs_keys
        exists |i: (Uid, ObjectRef)| {
            let etcd_obj = s.resources()[i.1];
            let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
            &&& #[trigger] s.resources().contains_key(i.1)
            &&& valid_owned_obj_key(vd, s)(i.1)
            &&& filter_new_vrs_keys(vd.spec.template, s)(i.1)
            &&& etcd_vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1)
            // no old vrs, including the 2nd new vrs (if any)
            &&& !exists |k: ObjectRef| {
                &&& #[trigger] s.resources().contains_key(k)
                &&& valid_owned_obj_key(vd, s)(k)
                &&& filter_old_vrs_keys(Some(i.0), s)(k)
            }
        }
    }
}

pub open spec fn filter_new_vrs_keys(template: PodTemplateSpecView, s: ClusterState) -> spec_fn(ObjectRef) -> bool {
    |k: ObjectRef| {
        let obj = s.resources()[k];
        let vrs = VReplicaSetView::unmarshal(obj)->Ok_0;
        // sanity check
        &&& obj.kind == VReplicaSetView::kind()
        &&& VReplicaSetView::unmarshal(obj) is Ok
        // be consistent with filter_old_and_new_vrs
        &&& match_template_without_hash(template, vrs)
        // replicas can be zero
        // &&& vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0
    }
}

// None -> no new vrs
pub open spec fn filter_old_vrs_keys(new_vrs_uid: Option<Uid>, s: ClusterState) -> spec_fn(ObjectRef) -> bool {
    |k: ObjectRef| {
        let obj = s.resources()[k];
        let vrs = VReplicaSetView::unmarshal(obj)->Ok_0;
        &&& obj.kind == VReplicaSetView::kind()
        &&& VReplicaSetView::unmarshal(obj) is Ok
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0
    }
}

// can be unmarshalled and unmarshalled vrs can pass valid_owned_vrs
pub open spec fn valid_owned_obj_key(vd: VDeploymentView, s: ClusterState) -> spec_fn(ObjectRef) -> bool {
    |k: ObjectRef| {
        let obj = s.resources()[k];
        &&& obj.kind == VReplicaSetView::kind()
        &&& VReplicaSetView::unmarshal(obj) is Ok
        &&& valid_owned_vrs(VReplicaSetView::unmarshal(obj).unwrap(), vd)
    }
}

pub open spec fn filter_obj_keys_managed_by_vd(vd: VDeploymentView, s: ClusterState) -> Set<ObjectRef> {
    s.resources().dom().filter(valid_owned_obj_key(vd, s))
}

}