use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::vstatefulset_controller::model::{install::*, reconciler::*};
use crate::vstatefulset_controller::proof::{
    guarantee::*,
    liveness::{proof::lemma_vsts_eventually_stable_reconciliation, spec as vsts_spec},
};
use crate::vstatefulset_controller::trusted::{
    liveness_theorem as vsts_liveness, rely_guarantee::*, spec_types::*,
};
use vstd::prelude::*;

verus! {

pub open spec fn vsts_controller_spec(id: int) -> ControllerSpec {
    ControllerSpec {
        esr: vsts_liveness::vsts_eventually_stable_reconciliation(),
        liveness_dependency: true_pred(),
        safety_guarantee: always(lift_state(vsts_guarantee(id))),
        environment_rely: always(lift_state(vsts_rely_conditions_pod_monkey())),
        safety_partial_rely: |other_id: int| always(lift_state(vsts_rely(other_id))),
        fairness: |cluster: Cluster| vsts_spec::next_with_wf(cluster, id),
        membership: |cluster: Cluster, c_id: int| {
            &&& cluster.controller_models.contains_pair(c_id, vsts_controller_model())
            &&& cluster.type_is_installed_in_cluster::<VStatefulSetView>()
        },
    }
}

pub open spec fn vsts_core_set(id: int) -> CoreSet {
    CoreSet {
        members: Set::empty().insert(id),
        liveness_dependency: true_pred(),
    }
}

pub proof fn vsts_singleton_core_holds(cluster: CoreCluster, id: int)
    requires
        cluster.registry.contains_pair(id, vsts_controller_spec(id)),
        well_formed(cluster, vsts_core_set(id)),
    ensures
        core(cluster, vsts_core_set(id)),
{
    let s = vsts_core_set(id);
    let spec = cluster_model(cluster);
    let inner = cluster.cluster;

    // Unfold well_formed to get membership facts.
    assert(s.members.contains(id)); // trigger
    assert((cluster.registry[id].membership)(inner, id));

    // Extract spec.entails(next_with_wf(inner, id)) from the fairness tla_forall at i=id.
    let fairness_fn = |i: int| if cluster.registry.contains_key(i) {
        (cluster.registry[i].fairness)(inner)
    } else { true_pred::<ClusterState>() };
    assert(spec.entails(vsts_spec::next_with_wf(inner, id))) by {
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

    // env_rely is non-trivial for VSTS (pod monkey constraint). Thread R and env
    // through to the lemma; D is true_pred and collapses via temp_pred_equality later.
    let assumption_re = tla_forall(R_fn).and(tla_forall(env_fn));
    let spec_re = spec.and(assumption_re);

    assert forall |c: int| spec_re.entails(#[trigger] ESR_fn(c)) by {
        if s.members.contains(c) {
            assert forall |other_id: int| #[trigger] inner.controller_models.remove(id).contains_key(other_id)
                implies spec_re.entails(always(lift_state(vsts_rely(other_id)))) by {
                tla_forall_apply(R_fn, (id, other_id));
                entails_trans(spec_re, tla_forall(R_fn), R_fn((id, other_id)));
            }
            // Derive spec_re.entails(always(lift_state(vsts_rely_conditions_pod_monkey()))) from env_fn at id.
            tla_forall_apply(env_fn, id);
            entails_trans(spec_re, tla_forall(env_fn), env_fn(id));
            assert(env_fn(id) == always(lift_state(vsts_rely_conditions_pod_monkey())));

            entails_trans(spec_re, spec, lift_state(inner.init()));
            entails_trans(spec_re, spec, vsts_spec::next_with_wf(inner, id));
            lemma_vsts_eventually_stable_reconciliation(spec_re, inner, id);
            assert(ESR_fn(c) == vsts_liveness::vsts_eventually_stable_reconciliation());
        }
    }
    spec_entails_tla_forall(spec_re, ESR_fn);
    entails_implies(spec, assumption_re, tla_forall(ESR_fn));

    // Collapse D (true_pred) so the full assumption shape R.and(D).and(env) matches assumption_re.
    assert(spec.entails(tla_forall(G_fn).and(tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)).implies(tla_forall(ESR_fn))))) by {
        temp_pred_equality(tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)), assumption_re);
        entails_and_temp(spec, tla_forall(G_fn), tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)).implies(tla_forall(ESR_fn)));
    }
}

}
