use crate::kubernetes_cluster::proof::composition::*;
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
    guarantee::guarantee_condition_holds, liveness::spec::{next_with_wf, next_with_wf_is_stable}, predicate::*,
    helper_invariants, helper_lemmas::*,
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

// Helper: the predicate on vsts that we want to extract from current_state_matches(rmq)
// and show stable using entails_exists_stable.
// Includes all the "static" properties of the chosen vsts that we carry through the chain.
pub open spec fn vsts_pre(rmq: RabbitmqClusterView) -> spec_fn(VStatefulSetView) -> StatePred<ClusterState> {
    |vsts: VStatefulSetView| {
        |s: ClusterState| {
            &&& Cluster::desired_state_is(vsts)(s)
            &&& vsts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq))
            &&& vsts.spec.replicas == Some(rmq.spec.replicas)
            &&& vsts.metadata.name == Some(make_stateful_set_name(rmq))
            &&& vsts.metadata.namespace == rmq.metadata.namespace
        }
    }
}

#[verifier(external_body)]
pub proof fn composed_rmq_eventually_stable_reconciliation(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, rmq: RabbitmqClusterView)
requires
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    spec.entails(always(next_with_wf(cluster, controller_id))),
ensures
    spec.entails(always(lift_state(Cluster::desired_state_is(rmq))).leads_to(always(lift_state(composed_current_state_matches(rmq)))))
{
    assert(spec.entails(vsts_spec::next_with_wf(cluster, controller_id))) by {
        entails_trans(spec, next_with_wf(cluster, controller_id), vsts_spec::next_with_wf(cluster, controller_id));
    }

    // Define the "lifted invariant" = [] (next ∧ rely ∧ vsts_spec_inv)
    let lifted_inv = lift_action(cluster.next())
        .and(lift_state(rmq_rely_conditions(cluster, controller_id)))
        .and(lift_state(helper_invariants::vsts_spec_in_update_request_is_the_same_as_etcd_server(controller_id, rmq)));
    assert(spec.entails(rmq_eventually_stable_reconciliation_per_cr(rmq)));
    helper_invariants::lemma_eventually_always_vsts_spec_in_update_request_is_the_same_as_etcd_server(
        controller_id, cluster, spec, rmq
    );

    let stable_rmq_post =
        lift_state(current_state_matches(rmq))
        .and(lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rmq, SubResource::VStatefulSetView)))
        .and(lifted_inv);
    let lifted_always_vsts_pre = |vsts: VStatefulSetView| always(lift_state(vsts_pre(rmq)(vsts)));

    // (a) Show: stable_rmq_post(s) ==> ∃ vsts. vsts_pre(rmq)(vsts)(s)
    assert(always(stable_rmq_post).entails(tla_exists(lifted_always_vsts_pre))) by {
        // Extraction: in any state satisfying stable_rmq_post, we can find vsts
        assert forall |ex: Execution<ClusterState>| #[trigger] always(stable_rmq_post).satisfied_by(ex)
            implies tla_exists(|vsts: VStatefulSetView| lift_state(vsts_pre(rmq)(vsts))).satisfied_by(ex) by {
            always_to_current(ex, stable_rmq_post);
            // resource_state_matches(VStatefulSetView, rmq)(ex.head()) gives us the etcd_sts
            let sts_key = make_stateful_set_key(rmq);
            let etcd_sts = VStatefulSetView::unmarshal(ex.head().resources()[sts_key])->Ok_0;
            // From resource_state_matches: desired_state_is(etcd_sts), template matches, replicas matches, etc.
            assert(vsts_pre(rmq)(etcd_sts)(ex.head()));
            assert((|vsts: VStatefulSetView| lift_state(vsts_pre(rmq)(vsts)))(etcd_sts).satisfied_by(ex));
        }

        // (b) Stability: vsts_pre(rmq)(vsts)(s) ∧ stronger_next(s, s') ==> vsts_pre(rmq)(vsts)(s')
        let stronger_next = |s: ClusterState, s_prime: ClusterState| {
            &&& cluster.next()(s, s_prime)
            &&& current_state_matches(rmq)(s)
            &&& cluster_invariants_since_reconciliation(cluster, controller_id, rmq, SubResource::VStatefulSetView)(s)
            &&& rmq_rely_conditions(cluster, controller_id)(s)
            &&& helper_invariants::vsts_spec_in_update_request_is_the_same_as_etcd_server(controller_id, rmq)(s)
        };

        // Show spec entails always(stronger_next)
        entails_preserved_by_always(stable_rmq_post, lift_state(current_state_matches(rmq)));
        entails_preserved_by_always(stable_rmq_post, lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rmq, SubResource::VStatefulSetView)));
        entails_preserved_by_always(stable_rmq_post, lift_action(cluster.next()));
        entails_preserved_by_always(stable_rmq_post, lift_state(rmq_rely_conditions(cluster, controller_id)));
        entails_preserved_by_always(stable_rmq_post, lift_state(helper_invariants::vsts_spec_in_update_request_is_the_same_as_etcd_server(controller_id, rmq)));
        combine_spec_entails_always_n!(
            always(stable_rmq_post),
            lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(current_state_matches(rmq)),
            lift_state(cluster_invariants_since_reconciliation(cluster, controller_id, rmq, SubResource::VStatefulSetView)),
            lift_state(rmq_rely_conditions(cluster, controller_id)),
            lift_state(helper_invariants::vsts_spec_in_update_request_is_the_same_as_etcd_server(controller_id, rmq))
        );

        // Prove the stability condition for vsts_pre
        assert forall |s: ClusterState, s_prime: ClusterState|
            #![trigger stronger_next(s, s_prime)]
            forall |vsts: VStatefulSetView| #[trigger] vsts_pre(rmq)(vsts)(s) && stronger_next(s, s_prime)
                ==> vsts_pre(rmq)(vsts)(s_prime) by {
            assert forall |vsts: VStatefulSetView| #[trigger] vsts_pre(rmq)(vsts)(s) && stronger_next(s, s_prime)
                implies vsts_pre(rmq)(vsts)(s_prime) by {
                // desired_state_is_vsts_preserves takes care of desired_state_is(vsts)
                // The static properties (template.spec, replicas, name, namespace) are properties of the vsts object,
                // not of the state, so they are trivially preserved.
                let returned_vsts = desired_state_is_vsts_preserves_from_s_to_s_prime(
                    controller_id, cluster, rmq, s, s_prime
                );
            }
        }

        // Apply entails_exists_stable
        assert(tla_exists(lifted_always_vsts_pre) == tla_exists(|vsts: VStatefulSetView| always(lift_state(vsts_pre(rmq)(vsts)))));
        entails_exists_stable(always(stable_rmq_post), stronger_next, vsts_pre(rmq));
    }

    assert(spec.entails(always(lift_state(Cluster::desired_state_is(rmq))).leads_to(
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
            always(lift_state(Cluster::desired_state_is(rmq))),
            always(stable_rmq_post),
            tla_exists(lifted_always_vsts_pre).and(always(stable_rmq_post))
        );
    }

    let lifted_always_vsts_post = |vsts: VStatefulSetView| always(
        lift_state(vsts_liveness_theorem::current_state_matches(vsts))
            .and(lift_state(|s: ClusterState| {
                &&& vsts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq))
                &&& vsts.spec.replicas == Some(rmq.spec.replicas)
                &&& vsts.metadata.name == Some(make_stateful_set_name(rmq))
                &&& vsts.metadata.namespace == rmq.metadata.namespace
            }))
    );
    let lifted_always_composed_post = always(lift_state(composed_current_state_matches(rmq)));

    // VSTS ESR: for each vsts, [] desired_state_is(vsts) ~> [] current_state_matches(vsts)
    assert(spec.entails(tla_forall(|vsts: VStatefulSetView|
        always(lift_state(Cluster::desired_state_is(vsts))).leads_to(
            always(lift_state(vsts_liveness_theorem::current_state_matches(vsts)))))));

    // spec |= ∃ vsts. [] vsts_pre ~> ∃ vsts. [] vsts_post
    assert(spec.entails(tla_exists(lifted_always_vsts_pre).leads_to(tla_exists(lifted_always_vsts_post)))) by {
        assert forall |vsts: VStatefulSetView|
            spec.entails(#[trigger] lifted_always_vsts_pre(vsts).leads_to(tla_exists(lifted_always_vsts_post))) by {
            use_tla_forall(spec, |vsts: VStatefulSetView|
                always(lift_state(Cluster::desired_state_is(vsts))).leads_to(
                    always(lift_state(vsts_liveness_theorem::current_state_matches(vsts)))), vsts);

            entails_exists_intro(lifted_always_vsts_post, vsts);
            entails_implies_leads_to(
                spec,
                lifted_always_vsts_post(vsts),
                tla_exists(lifted_always_vsts_post)
            );
        }
        leads_to_exists_intro(spec, lifted_always_vsts_pre, tla_exists(lifted_always_vsts_post));
    }

    assert forall |vsts: VStatefulSetView|
        always(stable_rmq_post).entails(#[trigger] lifted_always_vsts_post(vsts).leads_to(lifted_always_composed_post)) by {
        // current_state_matches(vsts) ∧ static_props ==> composed_current_state_matches(rmq)
        assert forall |ex: Execution<ClusterState>|
            #[trigger] lift_state(vsts_liveness_theorem::current_state_matches(vsts))
                .and(lift_state(|s: ClusterState| {
                    &&& vsts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq))
                    &&& vsts.spec.replicas == Some(rmq.spec.replicas)
                    &&& vsts.metadata.name == Some(make_stateful_set_name(rmq))
                    &&& vsts.metadata.namespace == rmq.metadata.namespace
                })).satisfied_by(ex)
            implies lift_state(composed_current_state_matches(rmq)).satisfied_by(ex) by {
            current_state_matches_vsts_implies_composed_current_state_matches(rmq, vsts, ex.head());
        }
        entails_preserved_by_always(
            lift_state(vsts_liveness_theorem::current_state_matches(vsts))
                .and(lift_state(|s: ClusterState| {
                    &&& vsts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq))
                    &&& vsts.spec.replicas == Some(rmq.spec.replicas)
                    &&& vsts.metadata.name == Some(make_stateful_set_name(rmq))
                    &&& vsts.metadata.namespace == rmq.metadata.namespace
                })),
            lift_state(composed_current_state_matches(rmq))
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
    //   [] desired_state_is(rmq)
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
        always(lift_state(Cluster::desired_state_is(rmq))),
        tla_exists(lifted_always_vsts_pre).and(always(stable_rmq_post)),
        tla_exists(lifted_always_vsts_post).and(always(stable_rmq_post)),
        lifted_always_composed_post
    );
}

// Wrapper: universally quantify over rmq to get the full ESR theorem.
pub proof fn lemma_rmq_composed_eventually_stable_reconciliation(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
requires
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    spec.entails(next_with_wf(cluster, controller_id)),
ensures
    spec.entails(rmq_composed_eventually_stable_reconciliation()),
{
    // next_with_wf is stable, so spec |= next_with_wf ==> spec |= always(next_with_wf)
    next_with_wf_is_stable(cluster, controller_id);
    stable_to_always(next_with_wf(cluster, controller_id));
    assert forall |rmq: RabbitmqClusterView| spec.entails(
        always(lift_state(#[trigger] Cluster::desired_state_is(rmq))).leads_to(
            always(lift_state(composed_current_state_matches(rmq))))
    ) by {
        composed_rmq_eventually_stable_reconciliation(spec, cluster, controller_id, rmq);
    }
    let composed_csm = |rmq: RabbitmqClusterView| composed_current_state_matches(rmq);
    spec_entails_tla_forall(spec, |rmq: RabbitmqClusterView|
        always(lift_state(Cluster::desired_state_is(rmq))).leads_to(
            always(lift_state(composed_csm(rmq)))));
    assert(spec.entails(rmq_composed_eventually_stable_reconciliation()));
}

// Proves that Cluster::desired_state_is(vsts) is preserved from s to s_prime,
// where vsts is the VStatefulSet object in etcd that matches the rmq spec.
pub proof fn desired_state_is_vsts_preserves_from_s_to_s_prime(
    controller_id: int, cluster: Cluster, rmq: RabbitmqClusterView,
    s: ClusterState, s_prime: ClusterState
) -> (vsts: VStatefulSetView)
requires
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    cluster_invariants_since_reconciliation(cluster, controller_id, rmq, SubResource::VStatefulSetView)(s),
    rmq_rely_conditions(cluster, controller_id)(s),
    cluster.next()(s, s_prime),
    resource_state_matches(SubResource::VStatefulSetView, rmq)(s),
    helper_invariants::vsts_spec_in_update_request_is_the_same_as_etcd_server(controller_id, rmq)(s),
ensures
    Cluster::desired_state_is(vsts)(s),
    Cluster::desired_state_is(vsts)(s_prime),
    vsts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq)),
{
    let sts_key = make_stateful_set_key(rmq);
    let etcd_sts = VStatefulSetView::unmarshal(s.resources()[sts_key])->Ok_0;

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

            if resource_update_request_msg(sts_key)(msg)
            && s.resources().contains_key(sts_key)
            && msg.content.get_update_request().obj.metadata.resource_version == s.resources()[sts_key].metadata.resource_version {
                assert(helper_invariants::vsts_spec_in_update_request_is_the_same_as_etcd_server(controller_id, rmq)(s));
            } else if resource_update_request_msg(sts_key)(msg) {
                // rv mismatch => API server rejects
            } else {
                lemma_api_request_not_made_by_field_matches_maintains_resource(s, s_prime, cluster, msg, sts_key);
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
// we conclude composed_current_state_matches(rmq).
pub proof fn current_state_matches_vsts_implies_composed_current_state_matches(
    rmq: RabbitmqClusterView,
    vsts: VStatefulSetView,
    s: ClusterState
)
requires
    vsts_liveness_theorem::current_state_matches(vsts)(s),
    vsts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq)),
    vsts.spec.replicas == Some(rmq.spec.replicas),
    vsts.metadata.name == Some(make_stateful_set_name(rmq)),
    vsts.metadata.namespace == rmq.metadata.namespace,
ensures
    composed_current_state_matches(rmq)(s),
{
    assert forall |ord: nat| ord < rmq.spec.replicas implies {
        let key = ObjectRef {
            kind: Kind::PodKind,
            name: #[trigger] vsts_liveness_theorem::pod_name(make_stateful_set_name(rmq), ord),
            namespace: rmq.metadata.namespace->0
        };
        let obj = s.resources()[key];
        &&& s.resources().contains_key(key)
        &&& PodView::unmarshal(obj) is Ok
        &&& pod_spec_matches_rmq(rmq, PodView::unmarshal(obj)->Ok_0)
    } by {
        assert(vsts_liveness_theorem::replicas(vsts) == rmq.spec.replicas as nat);
        let vsts_key = ObjectRef {
            kind: Kind::PodKind,
            name: vsts_liveness_theorem::pod_name(vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        let rmq_key = ObjectRef {
            kind: Kind::PodKind,
            name: vsts_liveness_theorem::pod_name(make_stateful_set_name(rmq), ord),
            namespace: rmq.metadata.namespace->0
        };
        assert(vsts_key == rmq_key);
        assert(s.resources().contains_key(vsts_key));
        let obj = s.resources()[vsts_key];
        assert(PodView::unmarshal(obj) is Ok);
        let pod = PodView::unmarshal(obj)->Ok_0;
        assert(vsts_liveness_theorem::pod_spec_matches(vsts, pod));
        assert(vsts.spec.template.spec->0 == make_rabbitmq_pod_spec(rmq));
        assert(pod_spec_matches_rmq(rmq, pod));
    }
}

}