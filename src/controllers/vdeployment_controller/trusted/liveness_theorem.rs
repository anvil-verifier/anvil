use crate::kubernetes_api_objects::spec::{prelude::*, pod_template_spec::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*, controller::types::ReconcileLocalState};
use crate::temporal_logic::defs::*;
use crate::vreplicaset_controller::trusted::{spec_types::*, liveness_theorem as vrs_liveness};
use crate::vdeployment_controller::{
    model::reconciler::VDeploymentReconcileState,
    trusted::{spec_types::*, util::*, step::VDeploymentReconcileStepView::*},
    proof::{predicate::*, liveness::rolling_update::predicate::*},
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{

// ESR composition
pub open spec fn composed_vd_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    tla_forall(composed_vd_eventually_stable_reconciliation_per_cr())
}

pub open spec fn composed_vd_eventually_stable_reconciliation_per_cr() -> spec_fn(VDeploymentView) -> TempPred<ClusterState> {
    |vd: VDeploymentView| always(lift_state(desired_state_is(vd))).leads_to(always(lift_state(composed_current_state_matches(vd))))
}

pub open spec fn vd_eventually_stable_reconciliation_per_cr(vd: VDeploymentView, controller_id: int) -> TempPred<ClusterState> {
    always(lift_state(desired_state_is(vd))).leads_to(tla_exists(|new_vrs_key: ObjectRef| always(lift_state(inductive_current_state_matches(vd, controller_id, new_vrs_key)))))
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

pub open spec fn current_state_matches(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // new vrs exists and only one exists
        // at most one exists is enforced by filter_old_vrs_keys
        exists |new_vrs_key: ObjectRef| {
            let etcd_obj = s.resources()[new_vrs_key];
            let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
            &&& #[trigger] s.resources().contains_key(new_vrs_key)
            &&& valid_owned_obj_key(vd, s)(new_vrs_key)
            &&& filter_new_vrs_keys(vd.spec.template, s)(new_vrs_key)
            &&& etcd_vrs.metadata.uid is Some
            &&& vd.spec.replicas.unwrap_or(1) > 0 ==> etcd_vrs.spec.replicas.unwrap_or(1) > 0
            // no old vrs, including the 2nd new vrs (if any)
            &&& !exists |old_k: ObjectRef| {
                &&& #[trigger] s.resources().contains_key(old_k)
                &&& valid_owned_obj_key(vd, s)(old_k)
                &&& filter_old_vrs_keys(Some(etcd_vrs.metadata.uid->0), s)(old_k)
            }
        }
    }
}

// ~> \E k [] current_state_matches(vd, k)
pub open spec fn current_state_matches_with_new_vrs_key(vd: VDeploymentView, new_vrs_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        // new vrs exists and only one exists
        // at most one exists is enforced by filter_old_vrs_keys
        let etcd_obj = s.resources()[new_vrs_key];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        &&& s.resources().contains_key(new_vrs_key)
        &&& valid_owned_obj_key(vd, s)(new_vrs_key)
        &&& filter_new_vrs_keys(vd.spec.template, s)(new_vrs_key)
        &&& etcd_vrs.metadata.uid is Some
        &&& vd.spec.replicas.unwrap_or(1) > 0 ==> etcd_vrs.spec.replicas.unwrap_or(1) > 0
        // no old vrs, including the 2nd new vrs (if any)
        &&& !exists |old_k: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(old_k)
            &&& valid_owned_obj_key(vd, s)(old_k)
            &&& filter_old_vrs_keys(Some(etcd_vrs.metadata.uid->0), s)(old_k)
        }
    }
}

pub open spec fn composed_current_state_matches(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.resources().values().filter(valid_owned_pods(vd, s)).len() == vd.spec.replicas.unwrap_or(1)
    }
}

pub open spec fn valid_owned_pods(vd: VDeploymentView, s: ClusterState) -> spec_fn(DynamicObjectView) -> bool {
    |obj: DynamicObjectView| {
        &&& s.resources().values().contains(obj)
        &&& exists |vrs: VReplicaSetView| {
            &&& #[trigger] vrs_liveness::owned_selector_match_is(vrs, obj)
            &&& valid_owned_vrs(vrs, vd)
            &&& s.resources().contains_key(vrs.object_ref())
            &&& VReplicaSetView::unmarshal(s.resources()[vrs.object_ref()])->Ok_0 == vrs
        }
    }
}

// TODO: next time, if possible, don't reason over keys, use CR directly.
// This work poorly with tla_forall(|cr| ESR(cr))
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

}