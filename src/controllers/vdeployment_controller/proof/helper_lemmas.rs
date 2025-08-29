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
use vstd::{seq_lib::*, map_lib::*};
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

pub proof fn make_replica_set_makes_valid_owned_object(vd: VDeploymentView)
requires vd.well_formed(),
ensures
    valid_owned_object(make_replica_set(vd), vd),
{
    assert(make_replica_set(vd).metadata.owner_references->0[0] == vd.controller_owner_ref());
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

pub proof fn final_state_to_esr(vd: VDeploymentView, controller_id: int, nv_uid_key_replicas: Option<(Uid, ObjectRef, int)>, ov_len: nat, s: ClusterState)
requires
    nv_uid_key_replicas is Some,
    (nv_uid_key_replicas->0).2 == vd.spec.replicas.unwrap_or(int1!()),
    ov_len == 0,
    etcd_state_is(vd, controller_id, nv_uid_key_replicas, ov_len)(s),
    at_vd_step_with_vd(vd, controller_id, at_step![Done])(s), // provide cr.spec == vd.spec
ensures
    current_state_matches(vd)(s),
{
    let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap();
    let etcd_new_vrs = VReplicaSetView::unmarshal(s.resources()[(nv_uid_key_replicas->0).1])->Ok_0;
    let filtered_vrs_list = filter_vrs_managed_by_vd(vd, s.resources());
    assert(filtered_vrs_list == filter_vrs_managed_by_vd(triggering_cr, s.resources())) by {
        assert(vd.controller_owner_ref() == triggering_cr.controller_owner_ref());
        assert(vd.metadata.namespace->0 == triggering_cr.metadata.namespace->0);
        assert((|vrs| valid_owned_object(vrs, vd)) == (|vrs| valid_owned_object(vrs, triggering_cr)));
    }
}
}