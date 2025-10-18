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
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*};
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

pub proof fn lemma_esr_equiv_to_and_etcd_state_is(
    vd: VDeploymentView, cluster: Cluster, controller_id: int, s: ClusterState
)
requires
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()),
ensures
    current_state_matches(vd)(s) == exists |nv_uid_key: (Uid, ObjectRef)|
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(1))), 0)(s),
{
    // ==>
    if current_state_matches(vd)(s) {
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
        assert(valid_owned_obj_key(vd, s) == valid_owned_obj_key(triggering_cr, s));
        let nv_uid_key = choose |i: (Uid, ObjectRef)| {
            let etcd_obj = s.resources()[i.1];
            let etcd_vrs = VReplicaSetView::unmarshal(s.resources()[i.1])->Ok_0;
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
        };
        assert(etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(1))), 0)(s)) by {
            let filtered_old_vrs_keys = filter_obj_keys_managed_by_vd(vd, s).filter(filter_old_vrs_keys(Some(nv_uid_key.0), s));
            if exists |k: ObjectRef| filtered_old_vrs_keys.contains(k) {
                let k = choose |k: ObjectRef| filtered_old_vrs_keys.contains(k);
                assert(filter_old_vrs_keys(Some(nv_uid_key.0), s)(k));
                assert(filter_obj_keys_managed_by_vd(vd, s).contains(k));
                assert(false);
            } else {
                if filtered_old_vrs_keys.len() != 0 {
                    lemma_set_empty_equivalency_len(filtered_old_vrs_keys);
                }
            }
        }
    }
    // <==
    if exists |nv_uid_key: (Uid, ObjectRef)|
        etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(1))), 0)(s) {
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
        assert(valid_owned_obj_key(vd, s) == valid_owned_obj_key(triggering_cr, s));
        let nv_uid_key = choose |nv_uid_key: (Uid, ObjectRef)|
            etcd_state_is(vd.object_ref(), controller_id, Some((nv_uid_key.0, nv_uid_key.1, vd.spec.replicas.unwrap_or(1))), 0)(s);
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
        let esr_pred = |i: (Uid, ObjectRef)| {
            let etcd_obj = s.resources()[i.1];
            let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
            &&& s.resources().contains_key(i.1)
            &&& valid_owned_obj_key(vd, s)(i.1)
            &&& filter_new_vrs_keys(vd.spec.template, s)(i.1)
            &&& etcd_vrs.spec.replicas.unwrap_or(1) == vd.spec.replicas.unwrap_or(1)
            &&& !exists |k: ObjectRef| {
                &&& s.resources().contains_key(k)
                &&& valid_owned_obj_key(vd, s)(k)
                &&& filter_old_vrs_keys(Some(i.0), s)(k)
            }
        };
        assert(exists |i: (Uid, ObjectRef)| #[trigger] esr_pred(i)) by {
            assert(esr_pred((nv_uid_key.0, nv_uid_key.1)));
        }
    }
}

pub proof fn old_vrs_filter_on_objs_eq_filter_on_keys(
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
}