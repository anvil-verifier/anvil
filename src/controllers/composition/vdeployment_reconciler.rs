use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::trusted::liveness_theorem as vrs_liveness;
use crate::vdeployment_controller::trusted::liveness_theorem as vd_liveness;
use crate::vreplicaset_controller::trusted::{
    spec_types::*, rely_guarantee::*
};
use crate::vreplicaset_controller::model::reconciler::VReplicaSetReconciler;
use crate::composition::vreplicaset_reconciler::*;
use crate::vdeployment_controller::trusted::{
    spec_types::*, rely_guarantee::*, util::*
};
use crate::vdeployment_controller::model::{
    reconciler::*, install::*
};
use crate::vdeployment_controller::proof::{
    guarantee::*, liveness::{spec::*, proof::*}, predicate::*
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{


impl Composition for VDeploymentReconciler {
    open spec fn c() -> ControllerSpec {
        ControllerSpec{
            liveness_guarantee: vd_liveness::composed_vd_eventually_stable_reconciliation(),
            liveness_rely: vrs_liveness::vrs_eventually_stable_reconciliation(),
            safety_guarantee: always(lift_state(vd_guarantee(Self::id()))),
            safety_partial_rely: |other_id: int| always(lift_state(vd_rely(other_id))),
            fairness: |cluster: Cluster| next_with_wf(cluster, Self::id()),
            membership: |cluster: Cluster, id: int| {
                &&& cluster.controller_models.contains_pair(id, vd_controller_model())
                &&& cluster.type_is_installed_in_cluster::<VDeploymentView>()
                &&& cluster.type_is_installed_in_cluster::<VReplicaSetView>()
            },
        }
    }

    uninterp spec fn id() -> int;

    open spec fn composed() -> Map<int, ControllerSpec> {
        Map::<int, ControllerSpec>::empty().insert(VReplicaSetReconciler::id(), VReplicaSetReconciler::c())
    }

    // for trait proof implementation, requires conditions are already included here
    proof fn safety_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().safety_guarantee),
    {
        guarantee_condition_holds(spec, cluster, Self::id());
    }

    // vrs_guarantee to vd_rely & vrs_rely, trivial
    proof fn safety_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures forall |i| #[trigger] Self::composed().contains_key(i) ==>
            spec.entails((Self::c().safety_partial_rely)(i))
            && spec.entails((Self::composed()[i].safety_partial_rely)(Self::id()))
    {
        let vd_guarantee = vd_guarantee(Self::id());
        let vd_rely = vd_rely(VReplicaSetReconciler::id());
        let vrs_guarantee = vrs_guarantee(VReplicaSetReconciler::id());
        let vrs_rely = vrs_rely(Self::id());
        assert(Self::composed().contains_key(VReplicaSetReconciler::id())); // trigger
        assert(lift_state(vd_guarantee).and(lift_state(vrs_guarantee)).entails(lift_state(vd_rely).and(lift_state(vrs_rely))));
        // spec |= always(p & q)
        entails_and_temp(spec,
            always(lift_state(vd_guarantee)),
            always(lift_state(vrs_guarantee)));
        // always(p) & always(q) == always(p & q)
        always_and_equality(lift_state(vd_guarantee), lift_state(vrs_guarantee));
        // spec |= always(p & q) && p & q |= r & s ==> spec |= always(r & s)
        always_weaken(spec, lift_state(vd_guarantee).and(lift_state(vrs_guarantee)), lift_state(vd_rely).and(lift_state(vrs_rely)));
        // always(r) & always(s) == always(r & s)
        always_and_equality(lift_state(vd_rely), lift_state(vrs_rely));
        entails_trans(spec, // spec |= always(r & s) |= always(r)
            always(lift_state(vd_rely)).and(always(lift_state(vrs_rely))),
            always(lift_state(vd_rely))
        );
        entails_trans(spec, // spec |= always(r & s) |= always(s)
            always(lift_state(vd_rely)).and(always(lift_state(vrs_rely))),
            always(lift_state(vrs_rely))
        );
    }
}

impl VerticalComposition for VDeploymentReconciler {
    proof fn liveness_guarantee_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_guarantee),
    {
        eventually_stable_reconciliation_holds(spec, cluster, Self::id());
        composed_eventually_stable_reconciliation_holds(spec);
    }

    proof fn liveness_rely_holds(spec: TempPred<ClusterState>, cluster: Cluster)
        ensures spec.entails(Self::c().liveness_rely),
    {
        assert(Self::composed().contains_key(VReplicaSetReconciler::id())); // trigger
    }
}

// interface for different CRs

pub open spec fn valid_owned_vrs_p(vrs: VReplicaSetView, vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[vrs.object_ref()];
        let etcd_vrs = VReplicaSetView::unmarshal(etcd_obj)->Ok_0;
        &&& s.resources().contains_key(vrs.object_ref())
        &&& VReplicaSetView::unmarshal(etcd_obj) is Ok
        &&& valid_owned_vrs(etcd_vrs, vd)
    }
}

#[verifier(external_body)]
pub proof fn current_state_match_vd_implies_desired_state_is_vrs(vd: VDeploymentView, s: ClusterState)
requires
	vd_liveness::current_state_matches(vd)(s),
ensures
	forall |vrs: VReplicaSetView| #[trigger] valid_owned_vrs_p(vrs, vd)(s) ==> Cluster::desired_state_is(vrs)(s),
{}

#[verifier(external_body)]
pub proof fn current_state_match_combining_vrs_vd(vd: VDeploymentView, s: ClusterState)
requires
	vd_liveness::current_state_matches(vd)(s),
    forall |vrs: VReplicaSetView| #[trigger] valid_owned_vrs_p(vrs, vd)(s) ==> vrs_liveness::current_state_matches(vrs)(s),
ensures
    vd_liveness::current_pods_match(vd)(s),
{}

// generic proof
proof fn eventually_current_state_matches_with_p(spec: TempPred<ClusterState>, vd: VDeploymentView)
requires
    forall |vrs: VReplicaSetView| lift_state(valid_owned_vrs_p(vrs, vd)).entails(lift_state(#[trigger] Cluster::desired_state_is(vrs))),
    spec.entails(tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))))),
ensures
    spec.entails(tla_forall(|vrs: VReplicaSetView| always(lift_state(valid_owned_vrs_p(vrs, vd))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))))),
{
    assert forall |vrs: VReplicaSetView| #[trigger] spec.entails(always(lift_state(valid_owned_vrs_p(vrs, vd)))
        .leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))) by {
        // []valid_owned_vrs_p(vrs, vd) |= []desired_state_is(vrs)
        entails_preserved_by_always(lift_state(valid_owned_vrs_p(vrs, vd)), lift_state(Cluster::desired_state_is(vrs)));
        entails_implies_leads_to(spec, always(lift_state(valid_owned_vrs_p(vrs, vd))), always(lift_state(Cluster::desired_state_is(vrs))));
        use_tla_forall(spec, |vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))), vrs);
        leads_to_trans(spec,
            always(lift_state(valid_owned_vrs_p(vrs, vd))),
            always(lift_state(Cluster::desired_state_is(vrs))),
            always(lift_state(vrs_liveness::current_state_matches(vrs)))
        );
    }
    spec_entails_tla_forall(spec, |vrs: VReplicaSetView| always(lift_state(valid_owned_vrs_p(vrs, vd)))
        .leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))));
}

pub proof fn composed_eventually_stable_reconciliation_holds(spec: TempPred<ClusterState>)
requires
    spec.entails(vrs_liveness::vrs_eventually_stable_reconciliation()),
    spec.entails(vd_liveness::vd_eventually_stable_reconciliation()),
ensures
    spec.entails(vd_liveness::composed_vd_eventually_stable_reconciliation()),
{
    assert forall |crs: (VDeploymentView, VReplicaSetView)| true implies #[trigger] spec.entails(vd_liveness::composed_vd_eventually_stable_reconciliation_per_cr(crs.0, crs.1)) by {
        let vd = crs.0;
        let vrs = crs.1;
        // current_state_matches(vd) & current_state_matches(vrs) |= current_pods_match(vd)
        assert(lift_state(vd_liveness::current_state_matches(vd)).and(lift_state(vrs_liveness::current_state_matches(vrs))).entails(lift_state(vd_liveness::current_pods_match(vd)))) by {
            assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(vd_liveness::current_state_matches(vd)).and(lift_state(vrs_liveness::current_state_matches(vrs))).satisfied_by(ex)
                implies lift_state(vd_liveness::current_pods_match(vd)).satisfied_by(ex) by {
                assume(false);
            };
        }
        // []current_state_matches(vd) & []current_state_matches(vrs) |= []current_pods_match(vd)
        entails_preserved_by_always(lift_state(vd_liveness::current_state_matches(vd)).and(lift_state(vrs_liveness::current_state_matches(vrs))), lift_state(vd_liveness::current_pods_match(vd)));
        always_and_equality(lift_state(vd_liveness::current_state_matches(vd)), lift_state(vrs_liveness::current_state_matches(vrs)));
        // []desired_state_is(vd) ~> []current_state_matches(vd)
        use_tla_forall(spec, |vd| vd_liveness::vd_eventually_stable_reconciliation_per_cr(vd), vd);
        // []desired_state_is(vrs) ~> []current_state_matches(vrs)
        // this is super flaky
        assume(vrs_liveness::vrs_eventually_stable_reconciliation().entails(
            tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))))));
        assume(tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))).entails(
            vrs_liveness::vrs_eventually_stable_reconciliation()));
        temp_pred_equality(vrs_liveness::vrs_eventually_stable_reconciliation(),
            tla_forall(|vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs))))));
        use_tla_forall(spec, |vrs: VReplicaSetView| always(lift_state(Cluster::desired_state_is(vrs))).leads_to(always(lift_state(vrs_liveness::current_state_matches(vrs)))), vrs);
        // []desired_state_is(vd) & []desired_state_is(vrs) ~> [](current_state_matches(vd) & current_state_matches(vrs))
        always_leads_to_always_combine(spec,
            lift_state(vd_liveness::desired_state_is(vd)),
            lift_state(Cluster::desired_state_is(vrs)),
            lift_state(vd_liveness::current_state_matches(vd)),
            lift_state(vrs_liveness::current_state_matches(vrs))
        );
        temp_pred_equality(
            vd_liveness::composed_vd_eventually_stable_reconciliation_per_cr(vd, vrs),
            always(lift_state(vd_liveness::desired_state_is(vd)).and(lift_state(Cluster::desired_state_is(vrs)))).leads_to(
                always(lift_state(vd_liveness::current_pods_match(vd)))));
        // [](current_state_matches(vd) & current_state_matches(vrs)) ~> []current_pods_match(vd)
        entails_implies_leads_to(spec,
            always(lift_state(vd_liveness::current_state_matches(vd)).and(lift_state(vrs_liveness::current_state_matches(vrs)))),
            always(lift_state(vd_liveness::current_pods_match(vd)))
        );
        // [](desired_state_is(vd) & desired_state_is(vrs)) ~> []current_pods_match(vd)
        leads_to_trans(spec,
            always(lift_state(vd_liveness::desired_state_is(vd)).and(lift_state(Cluster::desired_state_is(vrs)))),
            always(lift_state(vd_liveness::current_state_matches(vd)).and(lift_state(vrs_liveness::current_state_matches(vrs)))),
            always(lift_state(vd_liveness::current_pods_match(vd)))
        );
    };
    spec_entails_tla_forall(spec, |cr: (VDeploymentView, VReplicaSetView)| vd_liveness::composed_vd_eventually_stable_reconciliation_per_cr(cr.0, cr.1));
}

}