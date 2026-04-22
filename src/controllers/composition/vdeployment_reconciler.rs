use crate::composition::vreplicaset_reconciler::*;
use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::vdeployment_controller::model::{install::*, reconciler::*};
use crate::vdeployment_controller::proof::{
    guarantee::guarantee_condition_holds as vd_guarantee_condition_holds,
    liveness::{proof::lemma_vd_composed_eventually_stable_reconciliation, spec as vd_spec},
};
use crate::vdeployment_controller::trusted::{
    liveness_theorem::*, rely_guarantee::*, spec_types::*,
};
use crate::vreplicaset_controller::trusted::{
    liveness_theorem as vrs_liveness, rely_guarantee::{vrs_guarantee, vrs_rely},
    spec_types::*,
};
use vstd::prelude::*;

verus! {

pub open spec fn vd_controller_spec(id: int) -> ControllerSpec {
    ControllerSpec {
        esr: composed_vd_eventually_stable_reconciliation(),
        liveness_dependency: vrs_liveness::vrs_eventually_stable_reconciliation(),
        safety_guarantee: always(lift_state(vd_guarantee(id))),
        environment_rely: true_pred(),
        safety_partial_rely: |other_id: int| always(lift_state(vd_rely(other_id))),
        fairness: |cluster: Cluster| vd_spec::next_with_wf(cluster, id),
        membership: |cluster: Cluster, c_id: int| {
            &&& cluster.controller_models.contains_pair(c_id, vd_controller_model())
            &&& cluster.type_is_installed_in_cluster::<VDeploymentView>()
            &&& cluster.type_is_installed_in_cluster::<VReplicaSetView>()
        },
    }
}

pub open spec fn vd_core_set(id: int) -> CoreSet {
    CoreSet {
        members: Set::empty().insert(id),
        liveness_dependency: vrs_liveness::vrs_eventually_stable_reconciliation(),
    }
}

pub proof fn vd_singleton_core_holds(cluster: CoreCluster, id: int)
    requires
        cluster.registry.contains_pair(id, vd_controller_spec(id)),
        well_formed(cluster, vd_core_set(id)),
    ensures
        core(cluster, vd_core_set(id)),
{
    let s = vd_core_set(id);
    let spec = cluster_model(cluster);
    let inner = cluster.cluster;

    // Unfold well_formed to get membership facts.
    assert(s.members.contains(id)); // trigger
    assert((cluster.registry[id].membership)(inner, id));

    // Extract spec.entails(vd_spec::next_with_wf(inner, id)) from the fairness tla_forall at i=id.
    let fairness_fn = |i: int| if cluster.registry.contains_key(i) {
        (cluster.registry[i].fairness)(inner)
    } else { true_pred::<ClusterState>() };
    assert(spec.entails(vd_spec::next_with_wf(inner, id))) by {
        tla_forall_apply(fairness_fn, id);
    }

    // Guarantee
    vd_guarantee_condition_holds(spec, inner, id);

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

    // Group R with D (VD's liveness depends on VRS's ESR, so D is non-trivial).
    let assumption_rd = tla_forall(R_fn).and(s.liveness_dependency);
    let spec_rd = spec.and(assumption_rd);

    assert forall |c: int| spec_rd.entails(#[trigger] ESR_fn(c)) by {
        if s.members.contains(c) {
            assert forall |other_id: int| #[trigger] inner.controller_models.remove(id).contains_key(other_id)
                implies spec_rd.entails(always(lift_state(vd_rely(other_id)))) by {
                tla_forall_apply(R_fn, (id, other_id));
                entails_trans(spec_rd, tla_forall(R_fn), R_fn((id, other_id)));
            }
            entails_trans(spec_rd, spec, lift_state(inner.init()));
            entails_trans(spec_rd, spec, vd_spec::next_with_wf(inner, id));
            // spec_rd.entails(vrs_eventually_stable_reconciliation()) via s.liveness_dependency
            assert(s.liveness_dependency == vrs_liveness::vrs_eventually_stable_reconciliation());
            lemma_vd_composed_eventually_stable_reconciliation(spec_rd, inner, id);
            assert(ESR_fn(c) == composed_vd_eventually_stable_reconciliation());
        }
    }
    spec_entails_tla_forall(spec_rd, ESR_fn);
    entails_implies(spec, assumption_rd, tla_forall(ESR_fn));

    // Collapse the env factor (every env_fn(c) is true_pred for VD) so the full
    // assumption shape R.and(D).and(env) matches assumption_rd.
    assert(spec.entails(tla_forall(G_fn).and(tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)).implies(tla_forall(ESR_fn))))) by {
        temp_pred_equality(tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)), assumption_rd);
        entails_and_temp(spec, tla_forall(G_fn), tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)).implies(tla_forall(ESR_fn)));
    }
}

}
