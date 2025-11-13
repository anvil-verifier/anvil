use crate::kubernetes_api_objects::spec::{prelude::*, pod_template_spec::*};
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::{spec_types::*, util::*};
use crate::vreplicaset_controller::trusted::liveness_theorem::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{

// FLAKY: replace with Cluster::eventually_stable_reconciliation(|vd| current_state_matches(vd))
// breaks eventually_stable_reconciliation_holds
pub open spec fn vd_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    tla_forall(|vd: VDeploymentView| vd_eventually_stable_reconciliation_per_cr(vd))
}

pub open spec fn vd_eventually_stable_reconciliation_per_cr(vd: VDeploymentView) -> TempPred<ClusterState> {
    always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(current_state_matches(vd))))
}

pub open spec fn composed_vd_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    tla_forall(|crs: (VDeploymentView, VReplicaSetView)| composed_vd_eventually_stable_reconciliation_per_cr(crs.0, crs.1))
}

pub open spec fn composed_vd_eventually_stable_reconciliation_per_cr(vd: VDeploymentView, vrs: VReplicaSetView) -> TempPred<ClusterState> {
    always(lift_state(desired_state_is(vd)).and(lift_state(Cluster::desired_state_is(vrs)))).leads_to(always(lift_state(current_pods_match(vd))))
}

pub open spec fn desired_state_is(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::desired_state_is(vd)(s)
        // in addition to general desired_state_is, template in vd must has labels
        // as required by vd.spec.selector.matches
        &&& vd.spec.template.metadata is Some
        &&& vd.spec.template.metadata->0.labels is Some
    }
}

// exists and only exists one VRS that matches vd.spec.template and has desired replicas
pub open spec fn current_state_matches(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // new vrs exists and only one exists
        // at most one exists is enforced by filter_old_vrs_keys
        exists |k: ObjectRef| {
            let etcd_obj = s.resources()[k];
            let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
            &&& #[trigger] s.resources().contains_key(k)
            &&& valid_owned_obj_key(vd, s)(k)
            &&& filter_new_vrs_keys(vd.spec.template, s)(k)
            &&& etcd_vrs.metadata.uid is Some
            &&& etcd_vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1)
            // no old vrs, including the 2nd new vrs (if any)
            &&& !exists |k: ObjectRef| {
                &&& #[trigger] s.resources().contains_key(k)
                &&& valid_owned_obj_key(vd, s)(k)
                &&& filter_old_vrs_keys(Some(etcd_vrs.metadata.uid->0), s)(k)
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
        &&& match_template_without_hash(template)(vrs)
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

//* ESR composition *//
pub open spec fn current_pods_match(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.resources().values().filter(valid_owned_pods(vd)).len() == vd.spec.replicas.unwrap_or(0)
    }
}

pub open spec fn valid_owned_pods(vd: VDeploymentView) -> spec_fn(DynamicObjectView) -> bool {
    |obj: DynamicObjectView| {
        &&& obj.kind == PodView::kind()
        &&& obj.metadata.namespace is Some
        &&& obj.metadata.namespace == vd.metadata.namespace
        &&& obj.metadata.owner_references_contains(vd.controller_owner_ref())
        &&& vd.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
        &&& obj.metadata.deletion_timestamp is None
    }
}

}