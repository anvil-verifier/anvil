use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::vreplicaset_controller::model::{install::*, reconciler::*};
use crate::vreplicaset_controller::proof::{
    guarantee::*,
    liveness::{proof::eventually_stable_reconciliation_holds, spec::*},
};
use crate::vreplicaset_controller::trusted::{
    liveness_theorem::*, rely_guarantee::*, spec_types::*,
};
use vstd::prelude::*;

verus! {

pub open spec fn vrs_controller_spec(id: int) -> ControllerSpec {
    ControllerSpec {
        esr: vrs_eventually_stable_reconciliation(),
        liveness_dependency: true_pred(),
        safety_guarantee: always(lift_state(vrs_guarantee(id))),
        environment_rely: true_pred(),
        safety_partial_rely: |other_id: int| always(lift_state(vrs_rely(other_id))),
        fairness: |cluster: Cluster| next_with_wf(cluster, id),
        membership: |cluster: Cluster, c_id: int| {
            &&& cluster.controller_models.contains_pair(c_id, vrs_controller_model())
            &&& cluster.type_is_installed_in_cluster::<VReplicaSetView>()
        },
    }
}

pub open spec fn vrs_core_set(id: int) -> CoreSet {
    CoreSet {
        members: Set::empty().insert(id),
        liveness_dependency: true_pred(),
    }
}

pub proof fn vrs_singleton_core_holds(cluster: CoreCluster, id: int)
    requires
        cluster.registry.contains_pair(id, vrs_controller_spec(id)),
        well_formed(cluster, vrs_core_set(id)),
    ensures
        core(cluster, vrs_core_set(id)),
{
    let s = vrs_core_set(id);
    let spec = cluster_model(cluster);
    let inner = cluster.cluster;

    // Unfold well_formed to get membership facts.
    assert(s.members.contains(id)); // trigger
    assert((cluster.registry[id].membership)(inner, id));

    // Extract spec.entails(next_with_wf(inner, id)) from the fairness tla_forall at i=id.
    let fairness_fn = |i: int| if cluster.registry.contains_key(i) {
        (cluster.registry[i].fairness)(inner)
    } else { true_pred::<ClusterState>() };
    assert(spec.entails(next_with_wf(inner, id))) by {
        tla_forall_apply(fairness_fn, id);
    }

    // Guarantee
    guarantee_condition_holds(spec, inner, id);

    let G_fn = |c: int| if s.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
    let R_fn = |pair: (int, int)| if s.members.contains(pair.0) && !s.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
    let ESR_fn = |c: int| if s.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
    let env_fn = |c: int| if s.members.contains(c) { cluster.registry[c].environment_rely } else { true_pred::<ClusterState>() };

    assert forall |c: int| spec.entails(#[trigger] G_fn(c)) by {
        if s.members.contains(c) {
            tla_forall_apply(G_fn, c);
        }
    }
    spec_entails_tla_forall(spec, G_fn);

    let spec_r = spec.and(tla_forall(R_fn));
    assert forall |c: int| spec_r.entails(#[trigger] ESR_fn(c)) by {
        if s.members.contains(c) {
            assert forall |other_id: int| #[trigger] inner.controller_models.remove(id).contains_key(other_id)
                implies spec_r.entails(always(lift_state(vrs_rely(other_id)))) by {
                tla_forall_apply(R_fn, (id, other_id));
                entails_trans(spec_r, tla_forall(R_fn), R_fn((id, other_id)));
            }
            entails_trans(spec_r, spec, next_with_wf(inner, id));
            eventually_stable_reconciliation_holds(spec_r, inner, id);
            assert(ESR_fn(c) == vrs_eventually_stable_reconciliation());
        }
    }
    spec_entails_tla_forall(spec_r, ESR_fn);
    entails_implies(spec, tla_forall(R_fn), tla_forall(ESR_fn));

    assert(spec.entails(tla_forall(G_fn).and(tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)).implies(tla_forall(ESR_fn))))) by {
        temp_pred_equality(tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)), tla_forall(R_fn));
        entails_and_temp(spec, tla_forall(G_fn), tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)).implies(tla_forall(ESR_fn)));
    }
}

}
