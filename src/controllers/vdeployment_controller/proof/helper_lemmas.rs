#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_invariants, predicate::*},
    trusted::{rely_guarantee::*, spec_types::*, util::*, liveness_theorem::*, step::VDeploymentReconcileStepView::*},
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*, string_view::*};
use vstd::{seq_lib::*, map_lib::*, set_lib::*};
use vstd::prelude::*;

verus! {

pub proof fn vd_rely_condition_equivalent_to_lifted_vd_rely_condition(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    ensures
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))))
        <==>
            spec.entails(always(lifted_vd_rely_condition(cluster, controller_id))),
{
    let lhs = 
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))));
    let rhs = spec.entails(always(lifted_vd_rely_condition(cluster, controller_id)));

    assert_by(
        lhs ==> rhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
                lhs
                && spec.satisfied_by(ex)
                && cluster.controller_models.remove(controller_id).contains_key(other_id)
                implies vd_rely(other_id)(ex.suffix(n).head()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lift_state(vd_rely(other_id))))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lift_state(vd_rely(other_id))))));
                assert(spec.implies(always(lift_state(vd_rely(other_id)))).satisfied_by(ex));
                assert(always(lift_state(vd_rely(other_id))).satisfied_by(ex));
                assert(lift_state(vd_rely(other_id)).satisfied_by(ex.suffix(n)));
            }
        }
    );
    
    assert_by(
        rhs ==> lhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
                rhs
                && spec.satisfied_by(ex)
                && cluster.controller_models.remove(controller_id).contains_key(other_id)
                implies vd_rely(other_id)(ex.suffix(n).head()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lifted_vd_rely_condition(cluster, controller_id)))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lifted_vd_rely_condition(cluster, controller_id)))));
                assert(spec.implies(always(lifted_vd_rely_condition(cluster, controller_id))).satisfied_by(ex));
                assert(always(lifted_vd_rely_condition(cluster, controller_id)).satisfied_by(ex));
                assert(lifted_vd_rely_condition(cluster, controller_id).satisfied_by(ex.suffix(n)));
            }
        }
    );
}

pub proof fn vd_rely_condition_equivalent_to_lifted_vd_rely_condition_action(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    ensures
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))))
        <==>
            spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id))),
{
    let lhs = 
        (forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))));
    let rhs = spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id)));

    assert_by(
        lhs ==> rhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
                lhs
                && spec.satisfied_by(ex)
                && cluster.controller_models.remove(controller_id).contains_key(other_id)
                implies 
                vd_rely(other_id)(ex.suffix(n).head())
                && vd_rely(other_id)(ex.suffix(n).head_next()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lift_state(vd_rely(other_id))))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lift_state(vd_rely(other_id))))));
                assert(spec.implies(always(lift_state(vd_rely(other_id)))).satisfied_by(ex));
                assert(always(lift_state(vd_rely(other_id))).satisfied_by(ex));
                assert(lift_state(vd_rely(other_id)).satisfied_by(ex.suffix(n)));
                assert(lift_state(vd_rely(other_id)).satisfied_by(ex.suffix(n + 1)));
            }
        }
    );
    
    assert_by(
        rhs ==> lhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
                rhs
                && spec.satisfied_by(ex)
                && cluster.controller_models.remove(controller_id).contains_key(other_id)
                implies 
                vd_rely(other_id)(ex.suffix(n).head())
                && vd_rely(other_id)(ex.suffix(n).head_next()) by {
                // Gradually unwrap the semantics of `spec.entails(always(lifted_vd_rely_condition_action(cluster, controller_id)))`
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lifted_vd_rely_condition_action(cluster, controller_id)))));
                assert(spec.implies(always(lifted_vd_rely_condition_action(cluster, controller_id))).satisfied_by(ex));
                assert(always(lifted_vd_rely_condition_action(cluster, controller_id)).satisfied_by(ex));
                assert(lifted_vd_rely_condition_action(cluster, controller_id).satisfied_by(ex.suffix(n)));
                assert(lifted_vd_rely_condition_action(cluster, controller_id).satisfied_by(ex.suffix(n + 1)));
            }
        }
    );
}

pub proof fn only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself_action(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    ensures
        spec.entails(always(tla_forall(|vd: VDeploymentView| 
            lift_state(helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)))))
        <==>
            spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id)))
{
    let lhs = 
        spec.entails(always(tla_forall(|vd: VDeploymentView| 
            lift_state(helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)))));
    let rhs = spec.entails(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id)));

    assert_by(
        lhs ==> rhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, vd: VDeploymentView| #![auto]
                lhs
                && spec.satisfied_by(ex)
                implies 
                helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(ex.suffix(n).head())
                && helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(ex.suffix(n).head_next()) by {
                // Gradually unwrap the semantics of lhs
                // until Verus can show the consequent.
                let tla_forall_body = |vd: VDeploymentView| 
                    lift_state(helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd));

                assert(valid(spec.implies(always(tla_forall(tla_forall_body)))));
                assert(spec.implies(always(tla_forall(tla_forall_body))).satisfied_by(ex));
                assert(always(tla_forall(tla_forall_body)).satisfied_by(ex));

                assert(tla_forall(tla_forall_body).satisfied_by(ex.suffix(n)));
                assert(tla_forall(tla_forall_body).satisfied_by(ex.suffix(n + 1)));

                assert(tla_forall_body(vd).satisfied_by(ex.suffix(n)));
                assert(tla_forall_body(vd).satisfied_by(ex.suffix(n + 1)));
            }
        }
    );
    
    assert_by(
        rhs ==> lhs,
        {
            assert forall |ex: Execution<ClusterState>, n: nat, vd: VDeploymentView| #![auto]
                rhs
                && spec.satisfied_by(ex)
                implies 
                helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(ex.suffix(n).head())
                && helper_invariants::vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(ex.suffix(n).head_next()) by {
                // Gradually unwrap the semantics of rhs
                // until Verus can show the consequent.
                assert(valid(spec.implies(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id)))));
                assert(spec.implies(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id))).satisfied_by(ex));
                assert(always(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id)).satisfied_by(ex));
                
                assert(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id).satisfied_by(ex.suffix(n)));
                assert(lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id).satisfied_by(ex.suffix(n + 1)));

            }
        }
    );
}

pub proof fn owner_references_contains_ignoring_uid_is_invariant_if_owner_references_unchanged(
    meta: ObjectMetaView,
    other_meta: ObjectMetaView,
    owner_ref: OwnerReferenceView
)
    requires
        meta.owner_references == other_meta.owner_references,
    ensures
        owner_references_contains_ignoring_uid(meta, owner_ref) == owner_references_contains_ignoring_uid(other_meta, owner_ref),
{
    assert_by(
        owner_references_contains_ignoring_uid(meta, owner_ref) ==> owner_references_contains_ignoring_uid(other_meta, owner_ref),
        {
            if owner_references_contains_ignoring_uid(meta, owner_ref) {
                let or = choose |or: OwnerReferenceView| {
                    &&& #[trigger] meta.owner_references_contains(or)
                    &&& or.block_owner_deletion == owner_ref.block_owner_deletion
                    &&& or.controller == owner_ref.controller
                    &&& or.kind == owner_ref.kind
                    &&& or.name == owner_ref.name
                };
                assert({
                    &&& other_meta.owner_references_contains(or)
                    &&& or.block_owner_deletion == owner_ref.block_owner_deletion
                    &&& or.controller == owner_ref.controller
                    &&& or.kind == owner_ref.kind
                    &&& or.name == owner_ref.name
                });
            }
        }
    );
    assert_by(
        owner_references_contains_ignoring_uid(other_meta, owner_ref) ==> owner_references_contains_ignoring_uid(meta, owner_ref),
        {
            if owner_references_contains_ignoring_uid(other_meta, owner_ref) {
                let or = choose |or: OwnerReferenceView| {
                    &&& #[trigger] other_meta.owner_references_contains(or)
                    &&& or.block_owner_deletion == owner_ref.block_owner_deletion
                    &&& or.controller == owner_ref.controller
                    &&& or.kind == owner_ref.kind
                    &&& or.name == owner_ref.name
                };
                assert({
                    &&& meta.owner_references_contains(or)
                    &&& or.block_owner_deletion == owner_ref.block_owner_deletion
                    &&& or.controller == owner_ref.controller
                    &&& or.kind == owner_ref.kind
                    &&& or.name == owner_ref.name
                });
            }
        }
    );
}

pub proof fn lemma_esr_equiv_to_instantiated_etcd_state_is(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, s: ClusterState
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
ensures
    current_state_matches(vd)(s) == instantiated_etcd_state_is_with_zero_old_vrs(vd, controller_id)(s),
{
    // ==>
    if current_state_matches(vd)(s) {
        let nv_key = choose |k: ObjectRef| {
            let etcd_obj = s.resources()[k];
            let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[k])->Ok_0;
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
        };
        let nv_uid = VReplicaSetView::unmarshal(s.resources()[nv_key])->Ok_0.metadata.uid->0;
        assert(etcd_state_is(vd, controller_id, Some((nv_uid, nv_key, vd.spec.replicas.unwrap_or(1))), 0)(s)) by {
            let filtered_old_vrs_keys = filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid), s));
            if exists |k: ObjectRef| filtered_old_vrs_keys.contains(k) {
                let k = choose |k: ObjectRef| filtered_old_vrs_keys.contains(k);
                assert(filter_old_vrs_keys(Some(nv_uid), s)(k));
                assert(filter_obj_keys_managed_by_vd(vd, s).contains(k));
                assert(false);
            } else {
                if filtered_old_vrs_keys.len() != 0 {
                    lemma_set_empty_equivalency_len(filtered_old_vrs_keys);
                }
            }
        }
        assert(exists |nv_uid_key: (Uid, ObjectRef)| #[trigger] etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), 0)(s)) by {
            assert((|nv_uid_key: (Uid, ObjectRef)| etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), 0)(s))((nv_uid, nv_key)));
        }
    }
    // <==
    if exists |nv_uid_key: (Uid, ObjectRef)|
        etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(1))), 0)(s) {
        let nv_uid_key = choose |nv_uid_key: (Uid, ObjectRef)|
            etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(1))), 0)(s);
        let etcd_new_vrs = VReplicaSetView::unmarshal(s.resources()[nv_uid_key.1])->Ok_0;
        assert forall |k: ObjectRef| #[trigger] s.resources().contains_key(k) implies
        !({
            &&& valid_owned_obj_key(vd, s)(k)
            &&& filter_old_vrs_keys(Some(nv_uid_key.0), s)(k)
        }) by {
            if valid_owned_obj_key(vd, s)(k) && filter_old_vrs_keys(Some(nv_uid_key.0), s)(k) {
                assert(filter_obj_keys_managed_by_vd(vd, s).contains(k));
                assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s)).contains(k));
                assert(false);
            }
        }
        let esr_pred = |k: ObjectRef| {
            let etcd_obj = s.resources()[k];
            let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
            &&& s.resources().contains_key(k)
            &&& valid_owned_obj_key(vd, s)(k)
            &&& filter_new_vrs_keys(vd.spec.template, s)(k)
            &&& etcd_vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1)
            &&& !exists |k: ObjectRef| {
                &&& s.resources().contains_key(k)
                &&& valid_owned_obj_key(vd, s)(k)
                &&& filter_old_vrs_keys(Some(etcd_vrs.metadata.uid->0), s)(k)
            }
        };
        assert(exists |k: ObjectRef| #[trigger] esr_pred(k)) by {
            assert(esr_pred(nv_uid_key.1));
        }
    }
}

pub proof fn lemma_old_vrs_filter_on_objs_eq_filter_on_keys(
    vd: VDeploymentView, managed_vrs_list: Seq<VReplicaSetView>, new_vrs_uid: Option<Uid>, s: ClusterState
)
requires
    // required as precondition of commutativity_of_seq_map_and_filter
    forall |vrs: VReplicaSetView| #[trigger] managed_vrs_list.contains(vrs) ==> {
        let key = vrs.object_ref();
        let etcd_obj = s.resources()[key];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        &&& s.resources().contains_key(key)
        &&& etcd_obj.kind == VReplicaSetView::kind()
        &&& VReplicaSetView::unmarshal(etcd_obj) is Ok
        &&& vrs_weakly_eq(etcd_vrs, vrs)
        &&& etcd_vrs.spec == vrs.spec
    },
    managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).to_set()
        == filter_obj_keys_managed_by_vd(vd, s),
ensures
    managed_vrs_list.filter(|vrs: VReplicaSetView| {
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    }).map_values(|vrs: VReplicaSetView| vrs.object_ref()).to_set()
        == filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s)),
{
    let new_vrs_filter = |vrs: VReplicaSetView| {
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    let managed_vrs_keys = managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref());
    // precondition of commutativity_of_seq_map_and_filter
    assert forall |i: int| 0 <= i && i < managed_vrs_list.len() implies
        new_vrs_filter(managed_vrs_list[i]) == filter_old_vrs_keys(new_vrs_uid, s)(managed_vrs_keys[i]) by {
        assert(managed_vrs_list.contains(managed_vrs_list[i])); // trigger
        assert(managed_vrs_keys[i] == managed_vrs_list[i].object_ref());
    }
    commutativity_of_seq_map_and_filter(managed_vrs_list, new_vrs_filter, filter_old_vrs_keys(new_vrs_uid, s), |vrs: VReplicaSetView| vrs.object_ref());
    lemma_filter_to_set_eq_to_set_filter(managed_vrs_keys, filter_old_vrs_keys(new_vrs_uid, s));
}

pub proof fn lemma_make_replica_set_passes_match_template_without_hash(vd: VDeploymentView) -> (vrs: VReplicaSetView)
requires
    vd.well_formed(),
ensures
    match_template_without_hash(vd.spec.template)(vrs),
    vrs == make_replica_set(vd),
{
    let vrs = make_replica_set(vd);
    assert(match_template_without_hash(vd.spec.template)(vrs)) by {
        assert(vrs.spec.template->0.metadata->0.labels->0 == 
            vd.spec.template.metadata->0.labels->0.insert("pod-template-hash"@, int_to_string_view(vd.metadata.resource_version->0)));
        assert(vrs.spec.template->0.metadata->0.labels->0.remove("pod-template-hash"@)
            == vd.spec.template.metadata->0.labels->0.remove("pod-template-hash"@));
    }
    return vrs;
}

pub proof fn lemma_no_duplication_in_resp_objs_implies_no_duplication_in_down_stream(
    vd: VDeploymentView, resp_objs: Seq<DynamicObjectView>
)
requires
    vd.spec.template.metadata is Some,
    vd.spec.template.metadata->0.labels is Some,
    resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates(),
    forall |obj: DynamicObjectView| #[trigger] resp_objs.contains(obj) ==> {
        &&& VReplicaSetView::unmarshal(obj) is Ok
        &&& obj.metadata.namespace is Some
        &&& obj.metadata.name is Some
        &&& obj.metadata.uid is Some
    },
    objects_to_vrs_list(resp_objs) is Some,
ensures
    ({
        let vrs_list = objects_to_vrs_list(resp_objs)->0;
        let managed_vrs_list = objects_to_vrs_list(resp_objs)->0.filter(|vrs| valid_owned_vrs(vrs, vd));
        let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
        &&& old_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).no_duplicates()
    }),
{
    let vrs_list = objects_to_vrs_list(resp_objs)->0;
    let managed_vrs_list = objects_to_vrs_list(resp_objs)->0.filter(|vrs| valid_owned_vrs(vrs, vd));
    let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
    let map_key = |vrs: VReplicaSetView| vrs.object_ref();
    let valid_owned_vrs_filter = |vrs: VReplicaSetView| valid_owned_vrs(vrs, vd);
    let old_vrs_list_filter_with_new_vrs = |vrs: VReplicaSetView| {
        &&& new_vrs is None || vrs.metadata.uid != new_vrs->0.metadata.uid
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    VReplicaSetView::marshal_preserves_integrity();
    assert(old_vrs_list.map_values(map_key).no_duplicates()) by {
        assert(resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()) == vrs_list.map_values(map_key)) by {
            assert forall |i| 0 <= i < resp_objs.len() implies vrs_list[i].object_ref() == #[trigger] resp_objs[i].object_ref() by {
                assert(resp_objs.contains(resp_objs[i])); // trigger
            }
        }
        map_values_weakens_no_duplicates(vrs_list, map_key);
        seq_filter_preserves_no_duplicates(vrs_list, valid_owned_vrs_filter);
        seq_filter_preserves_no_duplicates(managed_vrs_list, old_vrs_list_filter_with_new_vrs);
        assert(old_vrs_list.no_duplicates());
        assert forall |vrs| #[trigger] old_vrs_list.contains(vrs) implies vrs_list.contains(vrs) by {
            seq_filter_contains_implies_seq_contains(managed_vrs_list, old_vrs_list_filter_with_new_vrs, vrs);
            seq_filter_contains_implies_seq_contains(vrs_list, valid_owned_vrs_filter, vrs);
        }
        assert forall |i, j| 0 <= i < old_vrs_list.len() && 0 <= j < old_vrs_list.len() && i != j && old_vrs_list.no_duplicates() implies
            #[trigger] old_vrs_list[i].object_ref() != #[trigger] old_vrs_list[j].object_ref() by {
            assert(old_vrs_list.contains(old_vrs_list[i])); // trigger of vrs_list.contains
            assert(old_vrs_list.contains(old_vrs_list[j]));
            let m = choose |m| 0 <= m < vrs_list.len() && vrs_list[m] == old_vrs_list[i];
            let n = choose |n| 0 <= n < vrs_list.len() && vrs_list[n] == old_vrs_list[j];
            assert(old_vrs_list[i].object_ref() != old_vrs_list[j].object_ref()) by {
                if m == n {
                    assert(old_vrs_list[i] == old_vrs_list[j]);
                    assert(false);
                } else {
                    assert(vrs_list[m].object_ref() != vrs_list[n].object_ref()) by {
                        assert(vrs_list.map_values(map_key)[m] == vrs_list[m].object_ref());
                        assert(vrs_list.map_values(map_key)[n] == vrs_list[n].object_ref());
                        assert(vrs_list.map_values(map_key).no_duplicates());
                    }
                }
            }
        }
    }
}

// inverse of lemma_filter_old_and_new_vrs_from_resp_objs_implies_etcd_state_is
// if vd has zero replicas, the new vrs picked by controller may differ from the one in etcd_state_is
// so we can only prove the weakened form with quantifier, and that is still strong enough to prove the stability of ESR
pub proof fn lemma_etcd_state_is_implies_filter_old_and_new_vrs_from_resp_objs(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, nv_uid_key: (Uid, ObjectRef), msg: Message, s: ClusterState
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    // can use ESR instead, so if the witness matches or not doesn't matter
    etcd_state_is(vd, controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(1))), nat0!())(s),
    resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, msg)(s),
    s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    Cluster::etcd_objects_have_unique_uids()(s),
ensures
    exists |nv_uid_key: (Uid, ObjectRef)| #[trigger] new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), nat0!())(s),
{
    let resp_objs = msg.content.get_list_response().res.unwrap();
    let vrs_list = objects_to_vrs_list(resp_objs)->0;
    let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
    let (new_vrs_or_none, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
    let nonempty_vrs_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
    let key_map = |vrs: VReplicaSetView| vrs.object_ref();
    VReplicaSetView::marshal_preserves_integrity();
    assert forall |vrs| #[trigger] managed_vrs_list.contains(vrs) implies {
        &&& vrs.metadata.name is Some
        &&& vrs.metadata.uid is Some
        &&& vrs.metadata.namespace is Some
    } by {
        seq_filter_is_a_subset_of_original_seq(vrs_list, |vrs| valid_owned_vrs(vrs, vd));
        assert(exists |i| 0 <= i < vrs_list.len() && #[trigger] vrs_list[i] == vrs);
        let i = choose |i| 0 <= i < vrs_list.len() && #[trigger] vrs_list[i] == vrs;
        assert(resp_objs.contains(resp_objs[i])); // trigger
        assert(vrs_list == resp_objs.map_values(|o| VReplicaSetView::unmarshal(o)->Ok_0));
        assert(vrs_list[i] == VReplicaSetView::unmarshal(resp_objs[i])->Ok_0);
        VReplicaSetView::marshal_preserves_metadata();
    }
    if new_vrs_or_none is None { // prove contradiction
        assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).len() == 0);
        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(managed_vrs_list, match_template_without_hash(vd.spec.template));
        if exists |k: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(k)
            &&& valid_owned_obj_key(vd, s)(k)
            &&& filter_new_vrs_keys(vd.spec.template, s)(k)
        }{
            let k = choose |k: ObjectRef| {
                &&& #[trigger] s.resources().contains_key(k)
                &&& valid_owned_obj_key(vd, s)(k)
                &&& filter_new_vrs_keys(vd.spec.template, s)(k)
            };
            assert(filter_obj_keys_managed_by_vd(vd, s).contains(k));
            assert(managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).contains(k));
            let i = choose |i: int| 0 <= i < managed_vrs_list.len() && #[trigger] managed_vrs_list.map_values(key_map)[i] == k;
            let vrs = managed_vrs_list[i];
            assert(vrs.object_ref() == k);
            assert(managed_vrs_list.contains(vrs)); // trigger
            assert(false) by {
                assert(!match_template_without_hash(vd.spec.template)(vrs));
                assert(match_template_without_hash(vd.spec.template)(vrs)) by {
                    let etcd_obj = s.resources()[k];
                    let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
                    assert(match_template_without_hash(vd.spec.template)(etcd_vrs));
                    assert(etcd_vrs.spec == vrs.spec);
                }
            }
        }
    }
    assert(new_vrs_or_none is Some);
    let new_vrs = new_vrs_or_none->0;
    let new_vrs_uid = Some(new_vrs.metadata.uid->0);
    let old_vrs_filter = |vrs: VReplicaSetView| {
        &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
        &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
    };
    assert(managed_vrs_list.contains(new_vrs)) by { // trigger
        seq_filter_is_a_subset_of_original_seq(managed_vrs_list, match_template_without_hash(vd.spec.template));
        if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).len() > 0 {
            seq_filter_is_a_subset_of_original_seq(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)), nonempty_vrs_filter); 
        }
    }
    assert(old_vrs_list == managed_vrs_list.filter(old_vrs_filter)) by {
        same_filter_implies_same_result(managed_vrs_list, old_vrs_filter, |vrs: VReplicaSetView| {
            &&& new_vrs_or_none is None || vrs.metadata.uid != new_vrs_or_none->0.metadata.uid
            &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
        });
    }
    // assert(new_vrs.spec.replicas.unwrap_or(int1!()) == vd.spec.replicas.unwrap_or(int1!())
    //     && old_vrs_list.len() == 0) by
    if vd.spec.replicas != Some(int0!()) {
        if new_vrs.object_ref() != nv_uid_key.1 {
            let other_key = new_vrs.object_ref();
            assert(new_vrs.metadata.uid->0 != nv_uid_key.0);
            assert(valid_owned_obj_key(vd, s)(other_key));
            if new_vrs.spec.replicas == Some(int0!()) {
                // vrs with nv_uid_key can pass the nonempty_vrs_filter, it's impossible for new_vrs to be selected here
                assert(false) by {
                    let k = nv_uid_key.1;
                    assert(filter_obj_keys_managed_by_vd(vd, s).contains(k));
                    assert(managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).contains(k));
                    let i = choose |i: int| 0 <= i < managed_vrs_list.len() && #[trigger] managed_vrs_list.map_values(key_map)[i] == k;
                    let vrs = managed_vrs_list[i];
                    assert(vrs.object_ref() == k);
                    assert(managed_vrs_list.contains(vrs)); // trigger
                    assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).contains(vrs)) by {
                        assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).contains(vrs)); // trigger
                    }
                    assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).len() > 0);
                    assert(!managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).contains(new_vrs));
                }
            }
            assert(filter_old_vrs_keys(Some(nv_uid_key.0), s)(other_key));
            assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s)).contains(other_key));
            assert(false);
        } else {
            assert(new_vrs.metadata.uid->0 == nv_uid_key.0);
            assert(new_vrs.spec.replicas.unwrap_or(int1!()) == vd.spec.replicas.unwrap_or(int1!()));
            assert(old_vrs_list.len() == 0) by {
                let map_key = |vrs: VReplicaSetView| vrs.object_ref();
                assert(old_vrs_list.len() == old_vrs_list.map_values(map_key).len());
                // this part can be deduped if we move this condition to resp_msg_is_ok_list_resp_containing_matched_vrs
                assert(old_vrs_list.map_values(map_key).no_duplicates()) by {
                    lemma_no_duplication_in_resp_objs_implies_no_duplication_in_down_stream(vd, resp_objs);
                }
                old_vrs_list.map_values(map_key).unique_seq_to_set();
                lemma_old_vrs_filter_on_objs_eq_filter_on_keys(vd, managed_vrs_list, new_vrs_uid, s);
                assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s)).len() == 0);
            }
        }
    } else { // vd.spec.replicas == Some(0)
        if new_vrs.spec.replicas != Some(int0!()) { // new_vrs can pass nonempty_vrs_filter and old_vrs_filter
            assert(new_vrs.object_ref() != nv_uid_key.1);
            assert(new_vrs.metadata.uid->0 != nv_uid_key.0);
            assert(false) by {
                assert(managed_vrs_list.contains(new_vrs)); // trigger
                assert(managed_vrs_list.filter(|vrs: VReplicaSetView| {
                    &&& Some(nv_uid_key.0) is None || vrs.metadata.uid->0 != Some(nv_uid_key.0)->0
                    &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
                }).contains(new_vrs));
                lemma_old_vrs_filter_on_objs_eq_filter_on_keys(vd, managed_vrs_list, Some(nv_uid_key.0), s);
                assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s)).len() == 0);
                // thus contradict with etcd_state_is(.., 0)
                assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s)).contains(new_vrs.object_ref()));
            }
        } else {
            // all vrs in managed_vrs_list that match template has 0 replicas
            assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).len() == 0);
            if(old_vrs_list.len() != 0) {
                let havoc_vrs = old_vrs_list[0];
                assert(havoc_vrs != new_vrs);
                broadcast use group_filter_ensures;
                if havoc_vrs.object_ref() == nv_uid_key.1 {
                    let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[nv_uid_key.1])->Ok_0;
                    assert(etcd_vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1));
                    seq_filter_contains_implies_seq_contains(managed_vrs_list, old_vrs_filter, havoc_vrs);
                    assert(etcd_vrs.spec == havoc_vrs.spec);
                    assert(havoc_vrs.spec.replicas == Some(int0!()));
                    assert(false);
                } else {
                    seq_filter_contains_implies_seq_contains(managed_vrs_list, old_vrs_filter, havoc_vrs);
                    assert(managed_vrs_list.contains(havoc_vrs)); // trigger
                    lemma_old_vrs_filter_on_objs_eq_filter_on_keys(vd, managed_vrs_list, Some(nv_uid_key.0), s);
                    assert(false) by {
                        assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s)).len() == 0);
                        assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s)).contains(havoc_vrs.object_ref()));
                    }
                }
            }
        }
    }
    assert(new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd, controller_id, msg, Some((new_vrs.metadata.uid->0, new_vrs.object_ref(), get_replicas(vd.spec.replicas))), nat0!())(s));
    assert((|nv_uid_key: (Uid, ObjectRef)| new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd, controller_id, msg, Some((nv_uid_key.0, nv_uid_key.1, get_replicas(vd.spec.replicas))), nat0!())(s))(
        (new_vrs.metadata.uid->0, new_vrs.object_ref())
    ));
}

pub proof fn lemma_filter_old_and_new_vrs_from_resp_objs_implies_etcd_state_is(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, n: nat, msg: Message, s: ClusterState
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs(vd, controller_id, msg, nv_uid_key_replicas, n)(s),
    resp_msg_is_pending_list_resp_in_flight_and_match_req(vd, controller_id, msg)(s),
    s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
ensures
    etcd_state_is(vd, controller_id, nv_uid_key_replicas, n)(s),
{
    let resp_objs = msg.content.get_list_response().res.unwrap();
    let vrs_list = objects_to_vrs_list(resp_objs)->0;
    let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
    let (new_vrs_or_none, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
    if let Some(new_vrs) = new_vrs_or_none {
        let nonempty_vrs_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
        seq_filter_is_a_subset_of_original_seq(managed_vrs_list, match_template_without_hash(vd.spec.template));
        if managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).filter(nonempty_vrs_filter).len() > 0 {
            seq_filter_is_a_subset_of_original_seq(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)), nonempty_vrs_filter); 
        }
    } else {
        assert(nv_uid_key_replicas is None);
        assert(managed_vrs_list.filter(match_template_without_hash(vd.spec.template)).len() == 0);
        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
            managed_vrs_list, match_template_without_hash(vd.spec.template)
        );
        if exists |k: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(k)
            &&& valid_owned_obj_key(vd, s)(k)
            &&& filter_new_vrs_keys(vd.spec.template, s)(k)
        }{
            let k = choose |k: ObjectRef| {
                &&& #[trigger] s.resources().contains_key(k)
                &&& valid_owned_obj_key(vd, s)(k)
                &&& filter_new_vrs_keys(vd.spec.template, s)(k)
            };
            let etcd_obj = s.resources()[k];
            let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
            assert(filter_obj_keys_managed_by_vd(vd, s).contains(k));
            assert(managed_vrs_list.map_values(|vrs: VReplicaSetView| vrs.object_ref()).contains(k));
            let i = choose |i: int| 0 <= i && i < managed_vrs_list.len() && #[trigger] managed_vrs_list[i].object_ref() == k;
            assert(match_template_without_hash(vd.spec.template)(managed_vrs_list[i])) by {
                assert(managed_vrs_list.contains(managed_vrs_list[i])); // trigger
                assert(managed_vrs_list[i].spec == etcd_vrs.spec);
            }
            assert(false);
        }
    }
    let new_vrs_uid = if new_vrs_or_none is Some {
        Some(new_vrs_or_none->0.metadata.uid->0)
    } else {
        None
    };
    assert(filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(new_vrs_uid, s)).len() == n) by {
        let old_vrs_filter = |vrs: VReplicaSetView| {
            &&& new_vrs_uid is None || vrs.metadata.uid->0 != new_vrs_uid->0
            &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
        };
        let map_key = |vrs: VReplicaSetView| vrs.object_ref();
        assert(old_vrs_list == managed_vrs_list.filter(old_vrs_filter)) by {
            same_filter_implies_same_result(managed_vrs_list, old_vrs_filter, |vrs: VReplicaSetView| {
                &&& new_vrs_or_none is None || vrs.metadata.uid != new_vrs_or_none->0.metadata.uid
                &&& vrs.spec.replicas is None || vrs.spec.replicas->0 > 0
            });
        }
        assert(old_vrs_list.len() == old_vrs_list.map_values(map_key).len());
        // this part can be deduped if we move this condition to resp_msg_is_ok_list_resp_containing_matched_vr
        assert(old_vrs_list.map_values(map_key).no_duplicates()) by {
            lemma_no_duplication_in_resp_objs_implies_no_duplication_in_down_stream(vd, resp_objs);
        }
        old_vrs_list.map_values(map_key).unique_seq_to_set();
        lemma_old_vrs_filter_on_objs_eq_filter_on_keys(vd, managed_vrs_list, new_vrs_uid, s);
        assert(old_vrs_list.len() == n);
    }
}

// this one is flaky
pub proof fn lemma_instantiate_exists_create_resp_msg_containing_new_vrs_uid_key(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, n: nat, s: ClusterState
) -> (res: (Message, (Uid, ObjectRef)))
requires
    exists_create_resp_msg_containing_new_vrs_uid_key(vd, controller_id, n)(s),
    s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
ensures
    resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, res.0, res.1)(s),
    etcd_state_is(vd, controller_id, Some(((res.1).0, (res.1).1, vd.spec.replicas.unwrap_or(int1!()))), n)(s),
{
    let req_msg = s.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg->0;
    assert(exists |j: (Message, (Uid, ObjectRef))| {
        &&& s.in_flight().contains(j.0)
        &&& resp_msg_matches_req_msg(j.0, req_msg)
        &&& #[trigger] resp_msg_is_ok_create_resp_containing_new_vrs(vd, controller_id, j.0, j.1, s)
        &&& etcd_state_is(vd, controller_id, Some(((j.1).0, (j.1).1, vd.spec.replicas.unwrap_or(int1!()))), n)(s)
    }) by {
        assert(exists_create_resp_msg_containing_new_vrs_uid_key(vd, controller_id, n)(s));
    }

    let (resp_msg, nv_uid_key) = choose |j: (Message, (Uid, ObjectRef))| {
        &&& s.in_flight().contains(j.0)
        &&& resp_msg_matches_req_msg(j.0, req_msg)
        &&& #[trigger] resp_msg_is_ok_create_resp_containing_new_vrs(vd, controller_id, j.0, j.1, s)
        &&& etcd_state_is(vd, controller_id, Some(((j.1).0, (j.1).1, vd.spec.replicas.unwrap_or(int1!()))), n)(s)
    };
    return (resp_msg, nv_uid_key);
}

pub proof fn lemma_cr_fields_eq_to_cr_predicates_eq(vd: VDeploymentView, controller_id: int, s: ClusterState)
requires
    helper_invariants::vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)(s),
    s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()),
ensures
    ({
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
        &&& triggering_cr.controller_owner_ref() == vd.controller_owner_ref()
        &&& (|vrs| valid_owned_vrs(vrs, triggering_cr)) == (|vrs| valid_owned_vrs(vrs, vd))
        &&& (|vrs_list| filter_old_and_new_vrs(vd, vrs_list)) == (|vrs_list| filter_old_and_new_vrs(triggering_cr, vrs_list))
        &&& (|s| valid_owned_obj_key(vd, s)) == (|s| valid_owned_obj_key(triggering_cr, s))
        &&& (|s| filter_obj_keys_managed_by_vd(vd, s)) == (|s| filter_obj_keys_managed_by_vd(triggering_cr, s))
    }),
{}
}