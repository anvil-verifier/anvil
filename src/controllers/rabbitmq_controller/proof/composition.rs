use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::defs::*;
use crate::rabbitmq_controller::trusted::{
    spec_types::*, rely_guarantee::*, liveness_theorem::*, step::*
};
use crate::rabbitmq_controller::model::{
    reconciler::*, install::*, resource::stateful_set::{make_stateful_set, make_stateful_set_key, make_stateful_set_name}
};
use crate::rabbitmq_controller::proof::{
    guarantee::guarantee_condition_holds, liveness::spec::next_with_wf, predicate::*,
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
pub open spec fn vsts_pre(rmq: RabbitmqClusterView) -> spec_fn(VStatefulSetView) -> StatePred<ClusterState> {
    |vsts: VStatefulSetView| {
        |s: ClusterState| {
            &&& Cluster::desired_state_is(vsts)(s)
            &&& vsts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq))
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
    // ================================================================
    // Step 0: Setup — extract sub-controller spec entailment
    // ================================================================
    assert(spec.entails(vsts_spec::next_with_wf(cluster, controller_id))) by {
        entails_trans(spec, next_with_wf(cluster, controller_id), vsts_spec::next_with_wf(cluster, controller_id));
    }

    assert forall |rmq: RabbitmqClusterView| spec.entails(always(lift_state(#[trigger] Cluster::desired_state_is(rmq))).leads_to(always(lift_state(composed_current_state_matches(rmq))))) by {
        // ================================================================
        // Step 1: spec |= [] desired_state_is(rmq) ~> [] current_state_matches(rmq)
        // From rmq ESR (rmq_eventually_stable_reconciliation_per_cr)
        // ================================================================
        assert(spec.entails(rmq_eventually_stable_reconciliation_per_cr(rmq)));

        // ================================================================
        // Step 2: Establish additional invariants
        //
        // We need cluster_invariants_since_reconciliation, rmq_rely_conditions,
        // vsts_spec_in_update_request_is_the_same_as_etcd_server to hold
        // alongside current_state_matches(rmq).
        // ================================================================

        // TODO: Combine:
        //   spec |= [] desired_state_is(rmq) ~> [] cluster_invariants_since_reconciliation(...)
        //   (from existing phased invariant chain, phases I-VIII)
        //
        //   spec |= true ~> [] vsts_spec_in_update_request_is_the_same_as_etcd_server
        //   (from helper_invariants::proof.rs)
        helper_invariants::lemma_eventually_always_vsts_spec_in_update_request_is_the_same_as_etcd_server(
            controller_id, cluster, spec, rmq
        );

        // Define:
        //   stable_rmq_post = current_state_matches(rmq)
        //                   ∧ cluster_invariants_since_reconciliation(...)
        //                   ∧ rmq_rely_conditions(...)
        //                   ∧ vsts_spec_in_update_request_is_the_same_as_etcd_server(...)
        //                   ∧ next(...)
        //
        // TODO: Use leads_to_always_combine/enhance to get:
        //   spec |= [] desired_state_is(rmq) ~> [] stable_rmq_post

        // ================================================================
        // Step 3: [] stable_rmq_post |= ∃ vsts. [] vsts_pre(rmq)(vsts)
        //
        // (a) Extraction: From current_state_matches(rmq)(s),
        //     resource_state_matches(VStatefulSetView, rmq)(s) gives us an etcd_sts with:
        //       - Cluster::desired_state_is(etcd_sts)(s)
        //       - etcd_sts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq))
        //     So ∃ vsts. vsts_pre(rmq)(vsts)(s) holds.
        //
        // (b) Stability: vsts_pre(rmq)(vsts)(s) ∧ stronger_next(s, s') ==> vsts_pre(rmq)(vsts)(s')
        //     Using desired_state_is_vsts_preserves_from_s_to_s_prime:
        //       Cluster::desired_state_is(vsts)(s) is preserved from s to s_prime
        //       because resource_state_matches(VStatefulSetView, rmq)(s) +
        //       cluster_invariants + rely + vsts_spec_inv are all in stronger_next.
        //     template_matches is about vsts.spec (not about state), so trivially preserved.
        //
        // Apply entails_exists_stable to get:
        //   [] stable_rmq_post |= ∃ vsts. [] vsts_pre(rmq)(vsts)
        // ================================================================

        // ================================================================
        // Step 4: For each vsts with vsts_pre, get current_state_matches(vsts)
        //
        // VSTS ESR: ∀ vsts. spec |= [] desired_state_is(vsts) ~> [] current_state_matches(vsts)
        // ================================================================
        let current_state_matches_vsts = |vsts: VStatefulSetView| vsts_liveness_theorem::current_state_matches(vsts);
        assert(spec.entails(Cluster::eventually_stable_reconciliation(current_state_matches_vsts)));
        assert(spec.entails(tla_forall(|vsts: VStatefulSetView| always(lift_state(Cluster::desired_state_is(vsts))).leads_to(always(lift_state(current_state_matches_vsts(vsts)))))));

        // For the specific vsts from step 3:
        //   [] vsts_pre(rmq)(vsts)
        //   |= [] desired_state_is(vsts)          (extracting first conjunct)
        //   ~> [] current_state_matches(vsts)      (VSTS ESR)

        // ================================================================
        // Step 5: Combine into composed_current_state_matches(rmq)
        //
        // current_state_matches(vsts)(s) ∧ vsts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq))
        // ==> composed_current_state_matches(rmq)(s)
        //
        // Key observations:
        //   - vsts.spec.replicas == Some(rmq.spec.replicas)  (from resource_state_matches in current_state_matches(rmq))
        //   - vsts.metadata.name starts with make_stateful_set_key(rmq).name
        //   - pod_name(vsts.name, ord) == vsts_liveness_theorem::pod_name(rmq.metadata.name, ord)
        //   - From current_state_matches(vsts), for each ord < replicas(vsts):
        //       pod at pod_name(vsts.name, ord) has spec matching vsts.spec.template.spec
        //       i.e., pod_spec_matches(vsts, pod) holds
        //   - pod_spec_matches(vsts, pod) ==> pod_spec_matches_rmq(rmq, pod)
        //     since both compare pod.spec (sans volumes/hostname/subdomain)
        //     to the same make_rabbitmq_pod_spec(rmq) (sans volumes/hostname/subdomain)
        // ================================================================

        // Final chain:
        //   spec |= [] desired_state_is(rmq)
        //       ~> [] stable_rmq_post                                                                      [Steps 1-2]
        //       |= ∃ vsts. [] vsts_pre(rmq)(vsts) ∧ [] stable_rmq_post                                    [Step 3]
        //       ~> ∃ vsts. [] (current_state_matches(vsts) ∧ template_matches) ∧ [] stable_rmq_post        [Step 4]
        //       ~> [] composed_current_state_matches(rmq)                                                  [Step 5]
        assume(false); // TODO: fill in the detailed proof steps
    }
    let composed_current_state_matches = |rmq: RabbitmqClusterView| composed_current_state_matches(rmq);
    spec_entails_tla_forall(spec, |rmq: RabbitmqClusterView| always(lift_state(Cluster::desired_state_is(rmq))).leads_to(always(lift_state(composed_current_state_matches(rmq)))));
    assert(spec.entails(rmq_composed_eventually_stable_reconciliation()));
}

// Proves that Cluster::desired_state_is(vsts) is preserved from s to s_prime,
// where vsts is the VStatefulSet object in etcd that matches the rmq spec.
// This is needed to show that once we establish desired_state_is for the VStatefulSet,
// it remains stable so the VStatefulSet controller's ESR can be applied.
//
// Key insights:
// 1. Non-API steps: resources unchanged, trivially preserved.
// 2. API step with a non-sts_key request: lemma_api_request_not_made_by_field_matches_maintains_resource
// 3. API step with update to sts_key, rv matches:
//    vsts_spec_in_update_request_is_the_same_as_etcd_server ensures req.obj.spec == etcd.spec,
//    so the update preserves the spec.
// 4. API step with update to sts_key, rv doesn't match: API server rejects, etcd unchanged.
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
    // The key invariant: any in-flight update with matching rv has the same spec as etcd
    helper_invariants::vsts_spec_in_update_request_is_the_same_as_etcd_server(controller_id, rmq)(s),
ensures
    Cluster::desired_state_is(vsts)(s),
    Cluster::desired_state_is(vsts)(s_prime),
    vsts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq)),
{
    let sts_key = make_stateful_set_key(rmq);
    let etcd_sts = VStatefulSetView::unmarshal(s.resources()[sts_key])->Ok_0;

    // From resource_state_matches(VStatefulSetView, rmq)(s), we know:
    //   - desired_state_is(etcd_sts)(s) holds
    //   - etcd_sts.spec.template == make_stateful_set(rmq, cm_rv).spec.template
    //   - which means etcd_sts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq))
    assert(Cluster::desired_state_is(etcd_sts)(s));

    // Now show desired_state_is(etcd_sts)(s_prime) by case-splitting on the step
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            // We need to show s_prime.resources()[sts_key] preserves the spec

            // From rely conditions + no_delete + no_get_then, the only way sts_key can change
            // is via a plain UpdateRequest to sts_key from this controller.
            assert(!resource_delete_request_msg(sts_key)(msg));
            assert(!resource_get_then_update_request_msg(sts_key)(msg));
            assert(!resource_get_then_update_status_request_msg(sts_key)(msg));
            assert(!resource_get_then_delete_request_msg(sts_key)(msg));
            assert(!resource_update_status_request_msg(sts_key)(msg));

            if resource_update_request_msg(sts_key)(msg)
            && s.resources().contains_key(sts_key)
            && msg.content.get_update_request().obj.metadata.resource_version == s.resources()[sts_key].metadata.resource_version {
                // The update succeeds (rv matches).
                // From vsts_spec_in_update_request_is_the_same_as_etcd_server:
                //   msg.content.get_update_request().obj.spec == s.resources()[sts_key].spec
                // So after the update, the new etcd object has the same spec.
                assert(helper_invariants::vsts_spec_in_update_request_is_the_same_as_etcd_server(controller_id, rmq)(s));
            } else if resource_update_request_msg(sts_key)(msg) {
                // Update targets sts_key but rv doesn't match => API server rejects, etcd unchanged.
            } else {
                // msg doesn't update sts_key.
                // sts_key is unchanged: s_prime.resources()[sts_key] == s.resources()[sts_key].
                lemma_api_request_not_made_by_field_matches_maintains_resource(s, s_prime, cluster, msg, sts_key);
            }
        },
        _ => {
            // Non-API steps don't change resources.
            assert(s_prime.resources() == s.resources());
        },
    }

    // Return the etcd_sts which satisfies all three ensures clauses.
    etcd_sts
}

// Analogous to conjuncted_current_state_matches_vrs_implies_composed_current_state_matches
// in the VDeployment composition proof.
//
// Given:
//   - current_state_matches(vsts): all pods of this VSTS exist and have matching spec
//   - vsts.spec.template.spec == Some(make_rabbitmq_pod_spec(rmq)): the VSTS template matches rmq
//   - vsts.spec.replicas == Some(rmq.spec.replicas): the replica count matches
//   - vsts.metadata.name->0 == make_stateful_set_name(rmq): the VSTS naming matches
// We conclude composed_current_state_matches(rmq).
#[verifier(external_body)]
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
    // From current_state_matches(vsts)(s):
    //   forall |ord: nat| ord < replicas(vsts) ==>
    //     pod at pod_name(vsts.metadata.name->0, ord) exists w/ pod_spec_matches(vsts, pod)
    //
    // vsts.metadata.name->0 == make_stateful_set_name(rmq), so
    //   pod_name(vsts.metadata.name->0, ord) == pod_name(make_stateful_set_name(rmq), ord)
    //   which is what composed_current_state_matches(rmq) uses
    //
    // replicas(vsts) == rmq.spec.replicas  (from vsts.spec.replicas == Some(rmq.spec.replicas))
    //
    // pod_spec_matches(vsts, pod) means:
    //   pod.spec->0.without_volumes().without_hostname().without_subdomain()
    //   == vsts.spec.template.spec->0.without_volumes().without_hostname().without_subdomain()
    //   == make_rabbitmq_pod_spec(rmq).without_volumes().without_hostname().without_subdomain()
    // which is exactly pod_spec_matches_rmq(rmq, pod).

    assert forall |ord: nat| ord < rmq.spec.replicas implies {
        let key = ObjectRef {
            kind: Kind::PodKind,
            name: vsts_liveness_theorem::pod_name(make_stateful_set_name(rmq), ord),
            namespace: rmq.metadata.namespace->0
        };
        let obj = s.resources()[key];
        &&& s.resources().contains_key(key)
        &&& PodView::unmarshal(obj) is Ok
        &&& pod_spec_matches_rmq(rmq, PodView::unmarshal(obj)->Ok_0)
    } by {
        assert(vsts_liveness_theorem::replicas(vsts) == rmq.spec.replicas as nat);
        // pod_name(vsts.metadata.name->0, ord) == pod_name(make_stateful_set_name(rmq), ord)
        // current_state_matches(vsts) gives pod at this key w/ pod_spec_matches
        // pod_spec_matches(vsts, pod) + template.spec == Some(make_rabbitmq_pod_spec(rmq))
        //   ==> pod_spec_matches_rmq(rmq, pod)
    }
}

}