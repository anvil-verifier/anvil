use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::api_server::other_objects_are_unaffected_if_request_fails_to_be_applied;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::defs::*;
use crate::rabbitmq_controller::trusted::{
    spec_types::*, rely_guarantee::*, liveness_theorem::*, step::*
};
use crate::rabbitmq_controller::model::{
    reconciler::*, install::*, resource::stateful_set::*
};
use crate::rabbitmq_controller::proof::{
    guarantee::guarantee_condition_holds, predicate::*,
    helper_invariants, helper_lemmas::*, resource::*, liveness::{spec:: *,proof::*},
};
use crate::vstatefulset_controller::trusted::{
    spec_types::VStatefulSetView,
    liveness_theorem as vsts_liveness_theorem,
    rely_guarantee as vsts_rely_mod,
};
use crate::vstatefulset_controller::trusted::rely_guarantee::{vsts_rely, vsts_guarantee, vsts_guarantee_create_req, vsts_guarantee_get_then_update_req, vsts_guarantee_get_then_delete_req};
use crate::vstatefulset_controller::model::{
    reconciler::VStatefulSetReconciler, install::vsts_controller_model
};
use crate::vstatefulset_controller::proof::liveness::spec as vsts_spec;
use crate::temporal_logic::rules::*;

use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{

pub open spec fn vsts_owned_by_rmq(vsts: VStatefulSetView, rabbitmq: RabbitmqClusterView) -> bool {
    &&& vsts.spec.template.spec == Some(make_rabbitmq_pod_spec(rabbitmq))
    &&& vsts.spec.replicas == Some(rabbitmq.spec.replicas)
    &&& vsts.metadata.name == Some(make_stateful_set_name(rabbitmq))
    &&& vsts.metadata.namespace == rabbitmq.metadata.namespace
}

// Helper: the predicate on vsts that we want to extract from current_state_matches(rabbitmq)
// and show stable using entails_exists_stable.
// Includes all the "static" properties of the chosen vsts that we carry through the chain.
pub open spec fn vsts_pre(rabbitmq: RabbitmqClusterView) -> spec_fn(VStatefulSetView) -> StatePred<ClusterState> {
    |vsts: VStatefulSetView| {
        |s: ClusterState| {
            &&& Cluster::desired_state_is(vsts)(s)
            &&& vsts_owned_by_rmq(vsts, rabbitmq)
        }
    }
}

#[verifier(spinoff_prover)]
pub proof fn composed_rmq_eventually_stable_reconciliation_per_cr(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, rabbitmq: RabbitmqClusterView)
requires
    spec.entails(lift_state(cluster.init())),
    // The cluster always takes an action, and the relevant actions satisfy weak fairness.
    spec.entails(next_with_wf(cluster, controller_id)),
    // The rabbitmq type is installed in the cluster.
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    // The vrs type is installed in the cluster.
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    // The rabbitmq controller runs in the cluster.
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    // No other controllers interfere with the rabbitmq controller.
    spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    // VSTS ESR
    spec.entails(vsts_liveness_theorem::vsts_eventually_stable_reconciliation()),
ensures
    spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(always(lift_state(composed_current_state_matches(rabbitmq)))))
{
    assert(spec.entails(vsts_spec::next_with_wf(cluster, controller_id))) by {
        entails_trans(spec, next_with_wf(cluster, controller_id), vsts_spec::next_with_wf(cluster, controller_id));
    }

    // Define the "lifted invariant" = [] (next ∧ rely ∧ vsts_spec_inv)
    let lifted_inv = lift_action(cluster.next())
        .and(lift_state(rmq_rely_conditions(cluster, controller_id)));
    eventually_stable_reconciliation_holds_per_cr(spec, cluster, controller_id, rabbitmq);
    assert(spec.entails(rmq_eventually_stable_reconciliation_per_cr(rabbitmq)));

    let stable_rmq_post =
        lift_state(current_state_matches(rabbitmq))
        .and(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::VStatefulSetView)))
        .and(lifted_inv);

    assert(spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(always(stable_rmq_post)))) by {
        // Step 1: spec |= □desired ~> assumption_and_invariants_of_all_phases
        spec_entails_always_desired_state_is_leads_to_assumption_and_invariants_of_all_phases(
            spec, controller_id, cluster, rabbitmq
        );
        // Step 2: assumption_and_invariants_of_all_phases |= □cluster_invariants
        assumptions_and_invariants_of_all_phases_entails_cluster_invariants_since_reconciliation(
            controller_id, cluster, SubResource::VStatefulSetView, rabbitmq
        );
        // Step 3: spec |= □desired ~> □cluster_invariants
        entails_implies_leads_to(
            spec,
            assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq),
            always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::VStatefulSetView)))
        );
        leads_to_trans(
            spec,
            always(lift_state(Cluster::desired_state_is(rabbitmq))),
            assumption_and_invariants_of_all_phases(controller_id, cluster, rabbitmq),
            always(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::VStatefulSetView)))
        );
        // Step 4: Combine: spec |= □desired ~> □(current_state_matches ∧ cluster_invariants)
        leads_to_always_combine(
            spec,
            always(lift_state(Cluster::desired_state_is(rabbitmq))),
            lift_state(current_state_matches(rabbitmq)),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::VStatefulSetView))
        );
        // Step 5: Establish spec |= □lifted_inv
        entails_trans(
            spec,
            next_with_wf(cluster, controller_id),
            always(lift_action(cluster.next()))
        );
        entails_always_and_n!(
            spec,
            lift_action(cluster.next()),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );
        // Step 6: Enhance with lifted_inv: spec |= □desired ~> □stable_rmq_post
        leads_to_always_enhance(
            spec,
            lifted_inv,
            always(lift_state(Cluster::desired_state_is(rabbitmq))),
            lift_state(current_state_matches(rabbitmq))
                .and(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::VStatefulSetView))),
            stable_rmq_post
        );
    }

    let lifted_always_vsts_pre = |vsts: VStatefulSetView| always(lift_state(vsts_pre(rabbitmq)(vsts)));

    // (a) Show: stable_rmq_post(s) ==> ∃ vsts. vsts_pre(rabbitmq)(vsts)(s)
    assert(always(stable_rmq_post).entails(tla_exists(lifted_always_vsts_pre))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] always(stable_rmq_post).satisfied_by(ex)
            implies tla_exists(|vsts: VStatefulSetView| lift_state(vsts_pre(rabbitmq)(vsts))).satisfied_by(ex) by {
            always_to_current(ex, stable_rmq_post);
            VStatefulSetView::marshal_preserves_integrity();
            let s = ex.head();
            let sts_key = make_stateful_set_key(rabbitmq);
            let etcd_sts = VStatefulSetView::unmarshal(s.resources()[sts_key])->Ok_0;
            assert(resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s));
            assert(vsts_pre(rabbitmq)(etcd_sts)(s));
            assert((|vsts: VStatefulSetView| lift_state(vsts_pre(rabbitmq)(vsts)))(etcd_sts).satisfied_by(ex));
        }
        // (b) Stability: vsts_pre(rabbitmq)(vsts)(s) ∧ stronger_next(s, s') ==> vsts_pre(rabbitmq)(vsts)(s')
        let stronger_next = |s: ClusterState, s_prime: ClusterState| {
            &&& cluster.next()(s, s_prime)
            &&& current_state_matches(rabbitmq)(s)
            &&& cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::VStatefulSetView)(s)
            &&& rmq_rely_conditions(cluster, controller_id)(s)
        };

        // Show spec entails always(stronger_next)
        entails_preserved_by_always(stable_rmq_post, lift_state(current_state_matches(rabbitmq)));
        entails_preserved_by_always(stable_rmq_post, lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::VStatefulSetView)));
        entails_preserved_by_always(stable_rmq_post, lift_action(cluster.next()));
        entails_preserved_by_always(stable_rmq_post, lift_state(rmq_rely_conditions(cluster, controller_id)));
        combine_spec_entails_always_n!(
            always(stable_rmq_post),
            lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(current_state_matches(rabbitmq)),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::VStatefulSetView)),
            lift_state(rmq_rely_conditions(cluster, controller_id))
        );

        // Prove the stability condition for vsts_pre
        assert forall |s: ClusterState, s_prime: ClusterState|
            #![trigger stronger_next(s, s_prime)]
            forall |vsts: VStatefulSetView| #[trigger] vsts_pre(rabbitmq)(vsts)(s) && stronger_next(s, s_prime)
                ==> vsts_pre(rabbitmq)(vsts)(s_prime) by {
            assert forall |vsts: VStatefulSetView| #[trigger] vsts_pre(rabbitmq)(vsts)(s) && stronger_next(s, s_prime)
                implies vsts_pre(rabbitmq)(vsts)(s_prime) by {
                // desired_state_is_vsts_preserves takes care of desired_state_is(vsts)
                // The static properties (template.spec, replicas, name, namespace) are properties of the vsts object,
                // not of the state, so they are trivially preserved.
                let returned_vsts = desired_state_is_vsts_preserves_from_s_to_s_prime(
                    controller_id, cluster, rabbitmq, s, s_prime
                );
            }
        }

        // Apply entails_exists_stable
        assert(tla_exists(lifted_always_vsts_pre) == tla_exists(|vsts: VStatefulSetView| always(lift_state(vsts_pre(rabbitmq)(vsts)))));
        entails_exists_stable(always(stable_rmq_post), stronger_next, vsts_pre(rabbitmq));
    }

    assert(spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(
        tla_exists(lifted_always_vsts_pre).and(always(stable_rmq_post))
    ))) by {
        entails_and_temp(
            always(stable_rmq_post),
            tla_exists(lifted_always_vsts_pre),
            always(stable_rmq_post)
        );
        entails_implies_leads_to(
            spec,
            always(stable_rmq_post),
            tla_exists(lifted_always_vsts_pre).and(always(stable_rmq_post))
        );
        leads_to_trans_n!(
            spec,
            always(lift_state(Cluster::desired_state_is(rabbitmq))),
            always(stable_rmq_post),
            tla_exists(lifted_always_vsts_pre).and(always(stable_rmq_post))
        );
    }

    let lifted_always_vsts_post = |vsts: VStatefulSetView| always(lift_state(vsts_liveness_theorem::current_state_matches(vsts))
        .and(lift_state(|s: ClusterState| vsts_owned_by_rmq(vsts, rabbitmq))));
    let lifted_always_composed_post = always(lift_state(composed_current_state_matches(rabbitmq)));

    // VSTS ESR: for each vsts, [] desired_state_is(vsts) ~> [] current_state_matches(vsts)
    assert forall |vsts: VStatefulSetView| spec.entails(always(lift_state(#[trigger] Cluster::desired_state_is(vsts)))
        .leads_to(always(lift_state(vsts_liveness_theorem::current_state_matches(vsts))))) by {
        tla_forall_p_tla_forall_q_equality(
            |vsts: VStatefulSetView| vsts_liveness_theorem::vsts_eventually_stable_reconciliation_per_cr(vsts),
            |vsts: VStatefulSetView| always(lift_state(Cluster::desired_state_is(vsts))).leads_to(always(lift_state(vsts_liveness_theorem::current_state_matches(vsts))))
        );
        tla_forall_apply(|vsts: VStatefulSetView| always(lift_state(Cluster::desired_state_is(vsts))).leads_to(always(lift_state(vsts_liveness_theorem::current_state_matches(vsts)))), vsts);
        entails_trans(spec,
            tla_forall(|vsts: VStatefulSetView| vsts_liveness_theorem::vsts_eventually_stable_reconciliation_per_cr(vsts)),
            vsts_liveness_theorem::vsts_eventually_stable_reconciliation_per_cr(vsts)
        );
    }

    // spec |= ∃ vsts. [] vsts_pre ~> ∃ vsts. [] vsts_post
    assert(spec.entails(tla_exists(lifted_always_vsts_pre).leads_to(tla_exists(lifted_always_vsts_post)))) by {
        assert forall |vsts: VStatefulSetView| spec.entails(#[trigger] lifted_always_vsts_pre(vsts).leads_to(lifted_always_vsts_post(vsts))) by {
            temp_pred_equality(lift_state(vsts_pre(rabbitmq)(vsts)), lift_state(Cluster::desired_state_is(vsts)).and(lift_state(|s: ClusterState| vsts_owned_by_rmq(vsts, rabbitmq))));
            always_and_equality(lift_state(Cluster::desired_state_is(vsts)), lift_state(|s: ClusterState| vsts_owned_by_rmq(vsts, rabbitmq)));
            always_and_equality(lift_state(vsts_liveness_theorem::current_state_matches(vsts)), lift_state(|s: ClusterState| vsts_owned_by_rmq(vsts, rabbitmq)));
            if vsts_owned_by_rmq(vsts, rabbitmq) {
                temp_pred_equality(lift_state(|s: ClusterState| vsts_owned_by_rmq(vsts, rabbitmq)), true_pred::<ClusterState>());
                temp_pred_equality(lifted_always_vsts_pre(vsts), always(lift_state(Cluster::desired_state_is(vsts))));
                temp_pred_equality(lifted_always_vsts_post(vsts), always(lift_state(vsts_liveness_theorem::current_state_matches(vsts))));
            } else {
                temp_pred_equality(lift_state(|s: ClusterState| vsts_owned_by_rmq(vsts, rabbitmq)), false_pred::<ClusterState>());
                false_is_stable::<ClusterState>();
                stable_to_always(false_pred::<ClusterState>()); // false == [] false
                temp_pred_equality(lifted_always_vsts_pre(vsts), false_pred::<ClusterState>());
                false_leads_to_anything(spec, lifted_always_vsts_post(vsts));
            }
        }
        leads_to_exists_intro2(spec, lifted_always_vsts_pre, lifted_always_vsts_post);
    }

    assert forall |vsts: VStatefulSetView|
        always(stable_rmq_post).entails(#[trigger] lifted_always_vsts_post(vsts).leads_to(lifted_always_composed_post)) by {
        // current_state_matches(vsts) ∧ static_props ==> composed_current_state_matches(rabbitmq)
        assert forall |ex: Execution<ClusterState>| lift_state(vsts_liveness_theorem::current_state_matches(vsts)).and(lift_state(|s: ClusterState| vsts_owned_by_rmq(vsts, rabbitmq))).satisfied_by(ex)
            implies #[trigger] lift_state(composed_current_state_matches(rabbitmq)).satisfied_by(ex) by {
            current_state_matches_vsts_implies_composed_current_state_matches(rabbitmq, vsts, ex.head());
        }
        entails_preserved_by_always(
            lift_state(vsts_liveness_theorem::current_state_matches(vsts))
                .and(lift_state(|s: ClusterState| vsts_owned_by_rmq(vsts, rabbitmq))),
            lift_state(composed_current_state_matches(rabbitmq))
        );
        entails_implies_leads_to(always(stable_rmq_post), lifted_always_vsts_post(vsts), lifted_always_composed_post);
    }
    leads_to_exists_intro(always(stable_rmq_post), lifted_always_vsts_post, lifted_always_composed_post);
    temp_pred_equality(
        true_pred::<ClusterState>().and(always(stable_rmq_post)),
        always(stable_rmq_post)
    );
    unpack_conditions_from_spec(true_pred(), always(stable_rmq_post), tla_exists(lifted_always_vsts_post), lifted_always_composed_post);
    temp_pred_equality(
        always(stable_rmq_post).and(tla_exists(lifted_always_vsts_post)),
        tla_exists(lifted_always_vsts_post).and(always(stable_rmq_post))
    );
    entails_and_different_temp(
        true_pred(),
        spec,
        always(stable_rmq_post).and(tla_exists(lifted_always_vsts_post)).leads_to(lifted_always_composed_post),
        spec
    );
    temp_pred_equality(
        true_pred::<ClusterState>().and(spec),
        spec
    );
    entails_trans(
        spec,
        always(stable_rmq_post).and(tla_exists(lifted_always_vsts_post)).leads_to(lifted_always_composed_post).and(spec),
        always(stable_rmq_post).and(tla_exists(lifted_always_vsts_post)).leads_to(lifted_always_composed_post)
    );

    // Final chain:
    //   [] desired_state_is(rabbitmq)
    //   ~> ∃ vsts. [] vsts_pre ∧ [] stable_rmq_post                [Steps 1-3]
    //   ~> ∃ vsts. [] vsts_post ∧ [] stable_rmq_post               [Step 4]
    //   ~> [] composed_current_state_matches                        [Step 5]
    assert(spec.entails(
        tla_exists(lifted_always_vsts_pre).and(always(stable_rmq_post))
            .leads_to(tla_exists(lifted_always_vsts_post).and(always(stable_rmq_post)))
    )) by {
        leads_to_with_always(
            spec,
            tla_exists(lifted_always_vsts_pre),
            tla_exists(lifted_always_vsts_post),
            stable_rmq_post
        );
    }

    leads_to_trans_n!(
        spec,
        always(lift_state(Cluster::desired_state_is(rabbitmq))),
        tla_exists(lifted_always_vsts_pre).and(always(stable_rmq_post)),
        tla_exists(lifted_always_vsts_post).and(always(stable_rmq_post)),
        lifted_always_composed_post
    );
}

// Wrapper: universally quantify over rabbitmq to get the full ESR theorem.
pub proof fn composed_rmq_eventually_stable_reconciliation(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(next_with_wf(cluster, controller_id)),
    forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
        ==> spec.entails(always(lift_state(#[trigger] rmq_rely(other_id)))),
    spec.entails(vsts_liveness_theorem::vsts_eventually_stable_reconciliation()),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
ensures
    spec.entails(rmq_composed_eventually_stable_reconciliation()),
{
    // Convert forall-quantified rely to the conjuncted form
    rmq_rely_condition_equivalent_to_lifted_rmq_rely_condition(spec, cluster, controller_id);
    // next_with_wf is stable, so spec |= next_with_wf ==> spec |= always(next_with_wf)
    next_with_wf_is_stable(cluster, controller_id);
    stable_to_always(next_with_wf(cluster, controller_id));
    assert forall |rabbitmq: RabbitmqClusterView| spec.entails(
        always(lift_state(#[trigger] Cluster::desired_state_is(rabbitmq))).leads_to(
            always(lift_state(composed_current_state_matches(rabbitmq))))
    ) by {
        composed_rmq_eventually_stable_reconciliation_per_cr(spec, cluster, controller_id, rabbitmq);
    }
    let composed_csm = |rabbitmq: RabbitmqClusterView| composed_current_state_matches(rabbitmq);
    spec_entails_tla_forall(spec, |rabbitmq: RabbitmqClusterView|
        always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(
            always(lift_state(composed_csm(rabbitmq)))));
    assert(spec.entails(rmq_composed_eventually_stable_reconciliation()));
}

// Proves that Cluster::desired_state_is(vsts) is preserved from s to s_prime,
// where vsts is the VStatefulSet object in etcd that matches the rabbitmq spec.
pub proof fn desired_state_is_vsts_preserves_from_s_to_s_prime(
    controller_id: int, cluster: Cluster, rabbitmq: RabbitmqClusterView,
    s: ClusterState, s_prime: ClusterState
) -> (vsts: VStatefulSetView)
requires
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    cluster_invariants_since_reconciliation(cluster, controller_id, rabbitmq, SubResource::VStatefulSetView)(s),
    rmq_rely_conditions(cluster, controller_id)(s),
    cluster.next()(s, s_prime),
    resource_state_matches(SubResource::VStatefulSetView, rabbitmq)(s),
ensures
    Cluster::desired_state_is(vsts)(s),
    Cluster::desired_state_is(vsts)(s_prime),
    vsts_owned_by_rmq(vsts, rabbitmq),
{
    VStatefulSetView::marshal_preserves_integrity();
    let sts_key = make_stateful_set_key(rabbitmq);
    let etcd_sts = VStatefulSetView::unmarshal(s.resources()[sts_key])->Ok_0;

    assert(etcd_sts.spec.replicas == Some(rabbitmq.spec.replicas));
    assert(etcd_sts.metadata.name == Some(make_stateful_set_name(rabbitmq)));
    assert(etcd_sts.metadata.namespace == rabbitmq.metadata.namespace);
    assert(etcd_sts.spec.template.spec == Some(make_rabbitmq_pod_spec(rabbitmq)));
    assert(Cluster::desired_state_is(etcd_sts)(s));

    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(!resource_delete_request_msg(sts_key)(msg));
            assert(!resource_get_then_update_request_msg(sts_key)(msg));
            assert(!resource_get_then_update_status_request_msg(sts_key)(msg));
            assert(!resource_get_then_delete_request_msg(sts_key)(msg));
            assert(!resource_update_status_request_msg(sts_key)(msg));

            assert(s.in_flight().contains(msg));
            if resource_get_then_update_request_msg(sts_key)(msg) {
                if s.resources().contains_key(sts_key)
                    && msg.content.get_get_then_update_request().owner_ref == rabbitmq.controller_owner_ref() {
                    RabbitmqReconcileState::marshal_preserves_integrity();
                    VStatefulSetView::marshal_preserves_integrity();
                } else {
                    assert(s_prime.resources() == s.resources());
                }
            } else if resource_create_request_msg(sts_key)(msg) {
            } else {
                other_objects_are_unaffected_if_request_fails_to_be_applied(cluster, s, s_prime, msg, sts_key);
            }
        },
        _ => {
            assert(s_prime.resources() == s.resources());
        },
    }

    etcd_sts
}

// Analogous to conjuncted_current_state_matches_vrs_implies_composed_current_state_matches
// Given current_state_matches(vsts) and the template/replicas/name match,
// we conclude composed_current_state_matches(rabbitmq).
pub proof fn current_state_matches_vsts_implies_composed_current_state_matches(
    rabbitmq: RabbitmqClusterView,
    vsts: VStatefulSetView,
    s: ClusterState
)
requires
    vsts_liveness_theorem::current_state_matches(vsts)(s),
    vsts_owned_by_rmq(vsts, rabbitmq),
ensures
    composed_current_state_matches(rabbitmq)(s),
{
    assert forall |ord: nat| ord < rabbitmq.spec.replicas implies {
        let key = ObjectRef {
            kind: Kind::PodKind,
            name: #[trigger] vsts_liveness_theorem::pod_name(make_stateful_set_name(rabbitmq), ord),
            namespace: rabbitmq.metadata.namespace->0
        };
        let obj = s.resources()[key];
        &&& s.resources().contains_key(key)
        &&& PodView::unmarshal(obj) is Ok
        &&& pod_spec_matches_rmq(rabbitmq, PodView::unmarshal(obj)->Ok_0)
    } by {
        assert(vsts_liveness_theorem::replicas(vsts) == rabbitmq.spec.replicas as nat);
        let vsts_key = ObjectRef {
            kind: Kind::PodKind,
            name: vsts_liveness_theorem::pod_name(vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        let rmq_key = ObjectRef {
            kind: Kind::PodKind,
            name: vsts_liveness_theorem::pod_name(make_stateful_set_name(rabbitmq), ord),
            namespace: rabbitmq.metadata.namespace->0
        };
        assert(vsts_key == rmq_key);
        assert(s.resources().contains_key(vsts_key));
        let obj = s.resources()[vsts_key];
        assert(PodView::unmarshal(obj) is Ok);
        let pod = PodView::unmarshal(obj)->Ok_0;
        assert(vsts_liveness_theorem::pod_spec_matches(vsts, pod));
        assert(vsts.spec.template.spec->0 == make_rabbitmq_pod_spec(rabbitmq));
        assert(pod_spec_matches_rmq(rabbitmq, pod));
    }
}

}