use crate::composition::rabbitmq_reconciler::*;
use crate::composition::vdeployment_reconciler::*;
use crate::composition::vreplicaset_reconciler::*;
use crate::composition::vstatefulset_reconciler::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::rabbitmq_controller::trusted::rely_guarantee::*;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::vdeployment_controller::model::install::vd_controller_model;
use crate::vdeployment_controller::trusted::rely_guarantee::*;
use crate::vdeployment_controller::trusted::spec_types::*;
use crate::vreplicaset_controller::model::install::vrs_controller_model;
use crate::vreplicaset_controller::model::reconciler::has_vrs_prefix;
use crate::vreplicaset_controller::trusted::rely_guarantee::*;
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vstatefulset_controller::model::install::vsts_controller_model;
use crate::vstatefulset_controller::proof::predicate::has_vsts_prefix;
use crate::vstatefulset_controller::trusted::rely_guarantee::{
    self as vsts_rg, vsts_guarantee, vsts_rely,
};
use crate::vstatefulset_controller::trusted::spec_types::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// ============================================================
// Concrete id assignment and cluster instantiation
// ============================================================

pub open spec fn vrs_id() -> int { 1 }
pub open spec fn vd_id() -> int { 2 }
pub open spec fn vsts_id() -> int { 3 }
pub open spec fn rmq_id() -> int { 4 }

pub open spec fn cluster_instance() -> Cluster {
    Cluster {
        installed_types: Map::empty()
            .insert(VReplicaSetView::kind()->CustomResourceKind_0, Cluster::installed_type::<VReplicaSetView>())
            .insert(VDeploymentView::kind()->CustomResourceKind_0, Cluster::installed_type::<VDeploymentView>())
            .insert(VStatefulSetView::kind()->CustomResourceKind_0, Cluster::installed_type::<VStatefulSetView>())
            .insert(RabbitmqClusterView::kind()->CustomResourceKind_0, Cluster::installed_type::<RabbitmqClusterView>()),
        controller_models: Map::empty()
            .insert(vrs_id(), vrs_controller_model())
            .insert(vd_id(), vd_controller_model())
            .insert(vsts_id(), vsts_controller_model())
            .insert(rmq_id(), rabbitmq_controller_model()),
    }
}

pub open spec fn core_cluster() -> CoreCluster {
    CoreCluster {
        cluster: cluster_instance(),
        registry: Map::empty()
            .insert(vrs_id(), vrs_controller_spec(vrs_id()))
            .insert(vd_id(), vd_controller_spec(vd_id()))
            .insert(vsts_id(), vsts_controller_spec(vsts_id()))
            .insert(rmq_id(), rmq_controller_spec(rmq_id())),
    }
}

// Helper: vsts and vrs name prefixes are disjoint (kind names differ).
proof fn vsts_prefix_not_vrs_prefix(name: StringView)
    ensures
        !(has_vsts_prefix(name) && has_vrs_prefix(name)),
{
    if has_vsts_prefix(name) && has_vrs_prefix(name) {
        let vsts_suffix = choose |suffix| name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + suffix;
        let vrs_suffix = choose |suffix| name == VReplicaSetView::kind()->CustomResourceKind_0 + "-"@ + suffix;
        assert(VStatefulSetView::kind()->CustomResourceKind_0 == "vstatefulset"@);
        assert(VReplicaSetView::kind()->CustomResourceKind_0 == "vreplicaset"@);
        assert(name.take(VStatefulSetView::kind()->CustomResourceKind_0.len() as int) == VStatefulSetView::kind()->CustomResourceKind_0);
        assert(name.take(VReplicaSetView::kind()->CustomResourceKind_0.len() as int) == VReplicaSetView::kind()->CustomResourceKind_0);
        vrs_vsts_str_neq();
        assert(VStatefulSetView::kind()->CustomResourceKind_0.len() > VReplicaSetView::kind()->CustomResourceKind_0.len());
        assert(VStatefulSetView::kind()->CustomResourceKind_0.take(VReplicaSetView::kind()->CustomResourceKind_0.len() as int) == VReplicaSetView::kind()->CustomResourceKind_0);
        assert(false);
    }
}

proof fn kind_strings_distinct()
    ensures
        "vreplicaset"@ != "vdeployment"@,
        "vreplicaset"@ != "vstatefulset"@,
        "vreplicaset"@ != "rabbitmq"@,
        "vdeployment"@ != "vstatefulset"@,
        "vdeployment"@ != "rabbitmq"@,
        "vstatefulset"@ != "rabbitmq"@,
{
    reveal_strlit("vreplicaset");
    reveal_strlit("vdeployment");
    reveal_strlit("vstatefulset");
    reveal_strlit("rabbitmq");

    // Same-length pair: differentiate at index 1 ('r' vs 'd').
    assert("vreplicaset"@ != "vdeployment"@) by {
        assert("vreplicaset"@[1] != "vdeployment"@[1]);
    };
    // Length-different pairs: length inequality alone suffices.
    assert("vreplicaset"@.len() != "vstatefulset"@.len());
    assert("vreplicaset"@.len() != "rabbitmq"@.len());
    assert("vdeployment"@.len() != "vstatefulset"@.len());
    assert("vdeployment"@.len() != "rabbitmq"@.len());
    assert("vstatefulset"@.len() != "rabbitmq"@.len());
}

// VRS↔VSTS both manage Pods — name-prefix disambiguation is required.
// The other 6 cross-group pairs have disjoint request types so Verus derives
// guarantee→rely automatically (same as in VRS/VD).

proof fn vrs_guarantee_implies_vsts_rely(id: int)
    ensures lift_state(vrs_guarantee(id)).entails(lift_state(vsts_rely(id))),
{
    assert forall |s: ClusterState| #[trigger] vrs_guarantee(id)(s) implies vsts_rely(id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => vsts_rg::rely_create_req(req),
                APIRequest::UpdateRequest(req) => vsts_rg::rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) => vsts_rg::rely_get_then_update_req(req),
                APIRequest::DeleteRequest(req) => vsts_rg::rely_delete_req(req)(s),
                APIRequest::GetThenDeleteRequest(req) => vsts_rg::rely_get_then_delete_req(req),
                _ => true,
            }) by {
            match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(r) => {
                    assert(vrs_guarantee_create_req(r)(s));
                    vsts_prefix_not_vrs_prefix(r.obj.metadata.generate_name->0);
                }
                APIRequest::GetThenDeleteRequest(r) => {
                    assert(vrs_guarantee_get_then_delete_req(r)(s));
                    vsts_prefix_not_vrs_prefix(r.key.name);
                }
                _ => {}
            }
        };
    };
}

proof fn vsts_guarantee_implies_vrs_rely(id: int)
    ensures lift_state(vsts_guarantee(id)).entails(lift_state(vrs_rely(id))),
{
    assert forall |s: ClusterState| #[trigger] vsts_guarantee(id)(s) implies vrs_rely(id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => vrs_rely_create_req(req)(s),
                APIRequest::UpdateRequest(req) => vrs_rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) => vrs_rely_get_then_update_req(req)(s),
                APIRequest::UpdateStatusRequest(req) => vrs_rely_update_status_req(req)(s),
                APIRequest::DeleteRequest(req) => vrs_rely_delete_req(req)(s),
                APIRequest::GetThenDeleteRequest(req) => vrs_rely_get_then_delete_req(req)(s),
                APIRequest::GetThenUpdateStatusRequest(req) => vrs_rely_get_then_update_status_req(req)(s),
                _ => true,
            }) by {
            match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(r) => {
                    assert(vsts_rg::vsts_guarantee_create_req(r));
                    vsts_prefix_not_vrs_prefix(r.obj.metadata.name->0);
                }
                APIRequest::GetThenUpdateRequest(r) => {
                    assert(vsts_rg::vsts_guarantee_get_then_update_req(r));
                    vsts_prefix_not_vrs_prefix(r.name);
                }
                APIRequest::GetThenDeleteRequest(r) => {
                    assert(vsts_rg::vsts_guarantee_get_then_delete_req(r));
                    vsts_prefix_not_vrs_prefix(r.key.name);
                }
                _ => {}
            }
        };
    };
}

// ============================================================
// Pairwise CORE proofs: {VRS,VD} and {VSTS,RMQ}
// ============================================================

pub proof fn vrs_vd_core_holds(cluster: CoreCluster)
    requires
        cluster.registry.contains_pair(vrs_id(), vrs_controller_spec(vrs_id())),
        cluster.registry.contains_pair(vd_id(), vd_controller_spec(vd_id())),
        well_formed(cluster, vrs_core_set(vrs_id())),
        well_formed(cluster, vd_core_set(vd_id())),
    ensures
        well_formed(cluster, union_coreset(vrs_core_set(vrs_id()), vd_core_set(vd_id()), true_pred())),
        core(cluster, union_coreset(vrs_core_set(vrs_id()), vd_core_set(vd_id()), true_pred())),
{
    let s1 = vrs_core_set(vrs_id());
    let s2 = vd_core_set(vd_id());
    let spec = cluster_model(cluster);

    vrs_singleton_core_holds(cluster, vrs_id());
    vd_singleton_core_holds(cluster, vd_id());

    assert(satisfies_dependency(cluster, s1, s2)) by {
        let esr_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
        let esr_s1 = tla_forall(esr_fn_s1);
        assert(s1.members.contains(vrs_id()));
        tla_forall_apply(esr_fn_s1, vrs_id());
        entails_trans(spec.and(esr_s1), esr_s1, s2.liveness_dependency);
        entails_implies(spec, esr_s1, s2.liveness_dependency);
    }

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        entails_preserved_by_always(lift_state(vrs_guarantee(vrs_id())), lift_state(vd_rely(vrs_id())));
        entails_preserved_by_always(lift_state(vd_guarantee(vd_id())), lift_state(vrs_rely(vd_id())));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                tla_forall_apply(g_fn_s1, vrs_id());
                entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(vrs_guarantee(vrs_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vrs_guarantee(vrs_id()))), always(lift_state(vd_rely(vrs_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                tla_forall_apply(g_fn_s2, vd_id());
                entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(vd_guarantee(vd_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(vd_guarantee(vd_id()))), always(lift_state(vrs_rely(vd_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));

        entails_and_temp(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose_dep(cluster, s1, s2);
}

pub proof fn vsts_rmq_core_holds(cluster: CoreCluster)
    requires
        cluster.registry.contains_pair(vsts_id(), vsts_controller_spec(vsts_id())),
        cluster.registry.contains_pair(rmq_id(), rmq_controller_spec(rmq_id())),
        well_formed(cluster, vsts_core_set(vsts_id())),
        well_formed(cluster, rmq_core_set(rmq_id())),
    ensures
        well_formed(cluster, union_coreset(vsts_core_set(vsts_id()), rmq_core_set(rmq_id()), true_pred())),
        core(cluster, union_coreset(vsts_core_set(vsts_id()), rmq_core_set(rmq_id()), true_pred())),
{
    let s1 = vsts_core_set(vsts_id());
    let s2 = rmq_core_set(rmq_id());
    let spec = cluster_model(cluster);

    vsts_singleton_core_holds(cluster, vsts_id());
    rmq_singleton_core_holds(cluster, rmq_id());

    assert(satisfies_dependency(cluster, s1, s2)) by {
        let esr_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
        let esr_s1 = tla_forall(esr_fn_s1);
        assert(s1.members.contains(vsts_id()));
        tla_forall_apply(esr_fn_s1, vsts_id());
        entails_trans(spec.and(esr_s1), esr_s1, s2.liveness_dependency);
        entails_implies(spec, esr_s1, s2.liveness_dependency);
    }

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        entails_preserved_by_always(lift_state(vsts_guarantee(vsts_id())), lift_state(rmq_rely(vsts_id())));
        entails_preserved_by_always(lift_state(rmq_guarantee(rmq_id())), lift_state(vsts_rely(rmq_id())));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                tla_forall_apply(g_fn_s1, vsts_id());
                entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(vsts_guarantee(vsts_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vsts_guarantee(vsts_id()))), always(lift_state(rmq_rely(vsts_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                tla_forall_apply(g_fn_s2, rmq_id());
                entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(rmq_guarantee(rmq_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(rmq_guarantee(rmq_id()))), always(lift_state(vsts_rely(rmq_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));

        entails_and_temp(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose_dep(cluster, s1, s2);
}

// ============================================================
// Joint CORE proof: compose {VRS, VD} with {VSTS, RMQ}
// ============================================================

pub open spec fn vrs_vd_set() -> CoreSet {
    union_coreset(vrs_core_set(vrs_id()), vd_core_set(vd_id()), true_pred())
}

pub open spec fn vsts_rmq_set() -> CoreSet {
    union_coreset(vsts_core_set(vsts_id()), rmq_core_set(rmq_id()), true_pred())
}

pub open spec fn all_core_set() -> CoreSet {
    union_coreset(vrs_vd_set(), vsts_rmq_set(), true_pred())
}

proof fn all_core_holds(cluster: CoreCluster)
    requires
        cluster.registry.contains_pair(vrs_id(), vrs_controller_spec(vrs_id())),
        cluster.registry.contains_pair(vd_id(), vd_controller_spec(vd_id())),
        cluster.registry.contains_pair(vsts_id(), vsts_controller_spec(vsts_id())),
        cluster.registry.contains_pair(rmq_id(), rmq_controller_spec(rmq_id())),
        well_formed(cluster, vrs_core_set(vrs_id())),
        well_formed(cluster, vd_core_set(vd_id())),
        well_formed(cluster, vsts_core_set(vsts_id())),
        well_formed(cluster, rmq_core_set(rmq_id())),
    ensures
        well_formed(cluster, all_core_set()),
        core(cluster, all_core_set()),
{
    let s1 = vrs_vd_set();
    let s2 = vsts_rmq_set();
    let spec = cluster_model(cluster);

    vrs_vd_core_holds(cluster);
    vsts_rmq_core_holds(cluster);

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        assert(s1.members =~= set![vrs_id(), vd_id()]);
        assert(s2.members =~= set![vsts_id(), rmq_id()]);

        // VRS↔VSTS needs explicit prefix reasoning.
        vrs_guarantee_implies_vsts_rely(vrs_id());
        vsts_guarantee_implies_vrs_rely(vsts_id());

        // Ambient fact for kinds used across is_rmq_managed_kind checks.
        kind_strings_distinct();

        // Lift pointwise implications through always(...). Verus derives the
        // 6 cross-kind implications directly (same pattern as VRS/VD).
        entails_preserved_by_always(lift_state(vrs_guarantee(vrs_id())), lift_state(vsts_rely(vrs_id())));
        entails_preserved_by_always(lift_state(vrs_guarantee(vrs_id())), lift_state(rmq_rely(vrs_id())));
        entails_preserved_by_always(lift_state(vd_guarantee(vd_id())), lift_state(vsts_rely(vd_id())));
        entails_preserved_by_always(lift_state(vd_guarantee(vd_id())), lift_state(rmq_rely(vd_id())));
        entails_preserved_by_always(lift_state(vsts_guarantee(vsts_id())), lift_state(vrs_rely(vsts_id())));
        entails_preserved_by_always(lift_state(vsts_guarantee(vsts_id())), lift_state(vd_rely(vsts_id())));
        entails_preserved_by_always(lift_state(rmq_guarantee(rmq_id())), lift_state(vrs_rely(rmq_id())));
        entails_preserved_by_always(lift_state(rmq_guarantee(rmq_id())), lift_state(vd_rely(rmq_id())));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                let src = pair.0;
                let tgt = pair.1;
                if tgt == vrs_id() {
                    tla_forall_apply(g_fn_s1, vrs_id());
                    entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(vrs_guarantee(vrs_id()))));
                    if src == vsts_id() {
                        entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vrs_guarantee(vrs_id()))), always(lift_state(vsts_rely(vrs_id()))));
                    } else {
                        assert(src == rmq_id());
                        entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vrs_guarantee(vrs_id()))), always(lift_state(rmq_rely(vrs_id()))));
                    }
                } else {
                    assert(tgt == vd_id());
                    tla_forall_apply(g_fn_s1, vd_id());
                    entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(vd_guarantee(vd_id()))));
                    if src == vsts_id() {
                        entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vd_guarantee(vd_id()))), always(lift_state(vsts_rely(vd_id()))));
                    } else {
                        assert(src == rmq_id());
                        entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vd_guarantee(vd_id()))), always(lift_state(rmq_rely(vd_id()))));
                    }
                }
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                let src = pair.0;
                let tgt = pair.1;
                if tgt == vsts_id() {
                    tla_forall_apply(g_fn_s2, vsts_id());
                    entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(vsts_guarantee(vsts_id()))));
                    if src == vrs_id() {
                        entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(vsts_guarantee(vsts_id()))), always(lift_state(vrs_rely(vsts_id()))));
                    } else {
                        assert(src == vd_id());
                        entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(vsts_guarantee(vsts_id()))), always(lift_state(vd_rely(vsts_id()))));
                    }
                } else {
                    assert(tgt == rmq_id());
                    tla_forall_apply(g_fn_s2, rmq_id());
                    entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(rmq_guarantee(rmq_id()))));
                    if src == vrs_id() {
                        entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(rmq_guarantee(rmq_id()))), always(lift_state(vrs_rely(rmq_id()))));
                    } else {
                        assert(src == vd_id());
                        entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(rmq_guarantee(rmq_id()))), always(lift_state(vd_rely(rmq_id()))));
                    }
                }
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));

        entails_and_temp(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose(cluster, s1, s2);
}

pub proof fn core_holds()
    ensures
        well_formed(core_cluster(), all_core_set()),
        core(core_cluster(), all_core_set()),
{
    kind_strings_distinct();
    all_core_holds(core_cluster());
}

}
