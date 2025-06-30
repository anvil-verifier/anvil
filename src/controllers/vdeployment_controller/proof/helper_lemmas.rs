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
    proof::predicate::*,
    trusted::rely_guarantee::*,
};
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

}