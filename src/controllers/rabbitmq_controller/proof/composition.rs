use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::defs::*;
use crate::rabbitmq_controller::trusted::{
    spec_types::*, rely_guarantee::*, liveness_theorem::*, step::*
};
use crate::rabbitmq_controller::model::{
    reconciler::*, install::*, resource::stateful_set::{make_stateful_set, make_stateful_set_key}
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

    assert forall |rmq: RabbitmqClusterView| spec.entails(always(lift_state(#[trigger] Cluster::desired_state_is(rmq))).leads_to(always(lift_state(composed_current_state_matches(rmq))))) by {
        assert(spec.entails(rmq_eventually_stable_reconciliation_per_cr(rmq)));

        let rv = choose |rv: ResourceVersion| rmq_eventually_stable_cm_rv(spec, rmq, rv);
        assert(rmq_eventually_stable_cm_rv(spec, rmq, rv));

        let desired_sts = make_stateful_set(rmq, int_to_string_view(rv));

        leads_to_always_combine(
            spec,
            always(lift_state(Cluster::desired_state_is(rmq))),
            lift_state(current_state_matches(rmq)),
            lift_state(config_map_rv_match(rmq, rv))
        );

        assert(lift_state(current_state_matches(rmq)).and(lift_state(config_map_rv_match(rmq, rv))).entails(lift_state(Cluster::desired_state_is(desired_sts)))) by {
            assert forall |ex: Execution<ClusterState>|
                lift_state(current_state_matches(rmq)).and(lift_state(config_map_rv_match(rmq, rv))).satisfied_by(ex)
                implies #[trigger] lift_state(Cluster::desired_state_is(desired_sts)).satisfied_by(ex) by {
                let s = ex.head();
                assert(resource_state_matches(SubResource::VStatefulSetView, rmq)(s));
                assert(config_map_rv_match(rmq, rv)(s));
            };
        };

        entails_preserved_by_always(
            lift_state(current_state_matches(rmq)).and(lift_state(config_map_rv_match(rmq, rv))),
            lift_state(Cluster::desired_state_is(desired_sts))
        );
        entails_implies_leads_to(
            spec,
            always(lift_state(current_state_matches(rmq)).and(lift_state(config_map_rv_match(rmq, rv)))),
            always(lift_state(Cluster::desired_state_is(desired_sts)))
        );
        leads_to_trans(
            spec,
            always(lift_state(Cluster::desired_state_is(rmq))),
            always(lift_state(current_state_matches(rmq)).and(lift_state(config_map_rv_match(rmq, rv)))),
            always(lift_state(Cluster::desired_state_is(desired_sts)))
        );

        let current_state_matches_vsts = |vsts: VStatefulSetView| vsts_liveness_theorem::current_state_matches(vsts);
        assert(spec.entails(Cluster::eventually_stable_reconciliation(current_state_matches_vsts)));
        assert(spec.entails(tla_forall(|vsts: VStatefulSetView| always(lift_state(Cluster::desired_state_is(vsts))).leads_to(always(lift_state(current_state_matches_vsts(vsts)))))));
        use_tla_forall(spec, |vsts: VStatefulSetView| always(lift_state(Cluster::desired_state_is(vsts))).leads_to(always(lift_state(current_state_matches_vsts(vsts)))), desired_sts);

        leads_to_trans(
            spec,
            always(lift_state(Cluster::desired_state_is(rmq))),
            always(lift_state(Cluster::desired_state_is(desired_sts))),
            always(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))
        );

        leads_to_always_combine(
            spec,
            always(lift_state(Cluster::desired_state_is(rmq))),
            lift_state(current_state_matches(rmq)).and(lift_state(config_map_rv_match(rmq, rv))),
            lift_state(vsts_liveness_theorem::current_state_matches(desired_sts))
        );

        assert(
            lift_state(current_state_matches(rmq)).and(lift_state(config_map_rv_match(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))
            .entails(lift_state(composed_current_state_matches(rmq)))
        ) by {
            assert forall |ex: Execution<ClusterState>|
                lift_state(current_state_matches(rmq)).and(lift_state(config_map_rv_match(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts))).satisfied_by(ex)
                implies #[trigger] lift_state(composed_current_state_matches(rmq)).satisfied_by(ex) by {
                let s = ex.head();
                assert(config_map_rv_match(rmq, rv)(s));
                // TODO: assert(composed_vsts_match(rmq)(s));
            };
        };

        entails_preserved_by_always(
            lift_state(current_state_matches(rmq)).and(lift_state(config_map_rv_match(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts))),
            lift_state(composed_current_state_matches(rmq))
        );
        entails_implies_leads_to(
            spec,
            always(lift_state(current_state_matches(rmq)).and(lift_state(config_map_rv_match(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))),
            always(lift_state(composed_current_state_matches(rmq)))
        );
        leads_to_trans(
            spec,
            always(lift_state(Cluster::desired_state_is(rmq))),
            always(lift_state(current_state_matches(rmq)).and(lift_state(config_map_rv_match(rmq, rv))).and(lift_state(vsts_liveness_theorem::current_state_matches(desired_sts)))),
            always(lift_state(composed_current_state_matches(rmq)))
        );
    }
    let composed_current_state_matches = |rmq: RabbitmqClusterView| composed_current_state_matches(rmq);
    spec_entails_tla_forall(spec, |rmq: RabbitmqClusterView| always(lift_state(Cluster::desired_state_is(rmq))).leads_to(always(lift_state(composed_current_state_matches(rmq)))));
    assert(spec.entails(rmq_composed_eventually_stable_reconciliation()));
}

// Proves that Cluster::desired_state_is(etcd_sts) is preserved from s to s_prime,
// where etcd_sts is the VStatefulSet object in etcd that matches the rmq spec.
// This is needed to show that once we establish desired_state_is for the VStatefulSet,
// it remains stable so the VStatefulSet controller's ESR can be applied.
//
// Key insights:
// 1. Non-API steps: resources unchanged, trivially preserved.
// 2. API step from other controller: rmq_rely blocks writes to rmq-managed kinds.
// 3. API step from same controller for same rmq:
//    - every_resource_update_request_implies_at_after_update_resource_step tells us
//      the update obj matches `update(VStatefulSetView, rmq, state, etcd_obj)`.
//    - Since resource_state_matches already holds, the update is idempotent:
//      updated_object(req, old_obj) == old_obj, so spec is unchanged.
// 4. API step from same controller for different rmq':
//    - rmq_with_different_key_implies_request_with_different_key shows keys differ.
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
    //   - etcd_sts.spec.template == make_stateful_set(rmq, int_to_string_view(cm_rv)).spec.template
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
                // The API server sets s_prime.resources()[sts_key].spec = msg.obj.spec = s.resources()[sts_key].spec
                // Therefore VStatefulSetView::unmarshal(s_prime.resources()[sts_key])->Ok_0.spec() == etcd_sts.spec()
                // And desired_state_is(etcd_sts)(s_prime) holds.
                assert(helper_invariants::vsts_spec_in_update_request_is_the_same_as_etcd_server(controller_id, rmq)(s));
            } else if resource_update_request_msg(sts_key)(msg) {
                // Update targets sts_key but rv doesn't match => API server rejects, etcd unchanged.
                // desired_state_is(etcd_sts)(s_prime) trivially holds.
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

}