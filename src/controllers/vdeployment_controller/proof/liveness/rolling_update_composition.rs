use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_lemmas::*, liveness::{spec::*, terminate, resource_match::*, proof::*, api_actions::*}, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*, util::*}
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*; // shortcut for steps
use crate::vdeployment_controller::proof::helper_invariants;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::trusted::liveness_theorem as vrs_liveness;
use vstd::{prelude::*, set_lib::*, map_lib::*};
use crate::vstd_ext::{set_lib::*, map_lib::*};

verus! {

pub open spec fn desired_state_is_vrs_with_replicas(vrs: VReplicaSetView) -> spec_fn(int) -> StatePred<ClusterState> {
    |replicas| {
        &&& vrs_liveness::desired_state_is(vrs)
        &&& vrs.spec.replicas.unwrap_or(1) == replicas
    }
}

pub open spec fn current_state_matches_vrs_with_replicas(vrs: VReplicaSetView) -> spec_fn(int) -> StatePred<ClusterState> {
    |replicas| {
        &&& vrs_liveness::current_state_matches(vrs)
        &&& vrs.spec.replicas.unwrap_or(1) == replicas
    }
}

pub open spec fn conjuncted_desired_state_is_vrs_with_replicas(new_vrs: VReplicaSetView, old_vrs_set: Set<VReplicaSetView>) -> spec_fn(int) -> StatePred<ClusterState> {
    |replicas| |s: ClusterState| {
        &&& old_vrs_set.is_finite()
        &&& forall |vrs| #[trigger] old_vrs_set.contains(vrs) ==> desired_state_is_vrs_with_replicas(vrs)(0)(s)
        &&& desired_state_is_vrs_with_replicas(new_vrs)(replicas)(s)
    }
}

pub open spec fn conjuncted_current_state_matches_vrs_with_replicas(new_vrs: VReplicaSetView, old_vrs_set: Set<VReplicaSetView>) -> spec_fn(int) -> StatePred<ClusterState> {
    |replicas| |s: ClusterState| {
        &&& old_vrs_set.is_finite()
        &&& forall |vrs| #[trigger] old_vrs_set.contains(vrs) ==> current_state_matches_vrs_with_replicas(vrs)(0)(s)
        &&& current_state_matches_vrs_with_replicas(new_vrs)(replicas)(s)
    }
}

pub open spec fn current_state_match_vd_applied_to_vrs_set(new_vrs: VReplicaSetView, old_vrs_set: Set<VReplicaSetView>, vd: VDeploymentView, replicas: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& old_vrs_set.insert(new_vrs) == s.resources().values()
            .filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind())
            .map(|obj| VReplicaSetView::unmarshal(obj)->Ok_0)
            .filter(|vrs: VReplicaSetView| valid_owned_vrs(vrs, vd))
        &&& forall |vrs| #[trigger] old_vrs_set.contains(vrs) ==> vrs.spec.replicas.unwrap_or(1) == 0
        &&& old_vrs_set.finite()
        &&& new_vrs.spec.replicas.unwrap_or(1) == replicas 
        &&& match_template_with_hash(vd.spec.template)(new_vrs)
    }
}

#[verifier(external_body)]
pub proof fn current_state_match_vd_implies_exists_vrs_set_with_desired_state_is(vd: VDeploymentView, cluster: Cluster, controller_id: int, s: ClusterState, replicas: int) -> (new_vrs: VReplicaSetView, old_vrs_set: Set<VReplicaSetView>)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    inductive_current_state_matches(vd, controller_id)(s),
ensures
    current_state_match_vd_applied_to_vrs_set(new_vrs, old_vrs_set, vd, replicas)(s),
    conjuncted_desired_state_is_vrs_with_replicas(new_vrs, old_vrs_set)(replicas)(s),
    old_vrs_set.finite(),
    old_vrs_set.len() > 0,
{
    return (VReplicaSetView::default(), Set::empty());
}

#[verifier(external_body)]
pub proof fn conjuncted_current_state_matches_vrs_implies_composed_current_state_matches(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, new_vrs: VReplicaSetView, old_vrs_set: Set<VReplicaSetView>, replicas: int, s: ClusterState
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    conjuncted_current_state_matches_vrs_with_replicas(new_vrs, old_vrs_set)(replicas)(s),
    current_state_match_vd_applied_to_vrs_set(new_vrs, old_vrs_set, vd, replicas)(s),
    replicas == vd.spec.replicas.unwrap_or(1),
ensures
    composed_current_state_matches(vd)(s),
{}

#[verifier(external_body)]
pub proof fn composed_desired_state_preserves_from_s_to_s_prime(
    vd: VDeploymentView, controller_id: int, cluster: Cluster, new_vrs: VReplicaSetView, old_vrs_set: Set<VReplicaSetView>, s: ClusterState, s_prime: ClusterState
)
requires
    // environment invariants
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s_prime),
    Cluster::etcd_objects_have_unique_uids()(s),
    vd_reconcile_request_only_interferes_with_itself_condition(controller_id)(s),
    vd_rely_condition(cluster, controller_id)(s),
    // stable_vd_post
    cluster.next()(s, s_prime),
    inductive_current_state_matches(vd, controller_id)(s),
    inductive_current_state_matches(vd, controller_id)(s_prime),
    current_state_match_vd_applied_to_vrs_set(new_vrs, old_vrs_set, vd, replicas)(s),
    conjuncted_desired_state_is_vrs_with_replicas(new_vrs, old_vrs_set)(replicas)(s)
ensures
    current_state_match_vd_applied_to_vrs_set(new_vrs, old_vrs_set, vd, replicas)(s_prime),
    conjuncted_desired_state_is_vrs_with_replicas(new_vrs, old_vrs_set)(replicas)(s_prime),
{}
}