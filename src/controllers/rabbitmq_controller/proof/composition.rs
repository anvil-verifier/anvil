use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::kubernetes_cluster::spec::message::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::defs::*;
use crate::rabbitmq_controller::trusted::{
    spec_types::*, rely_guarantee::*, liveness_theorem::*, step::*
};
use crate::rabbitmq_controller::model::{
    reconciler::*, install::*, resource::stateful_set::make_stateful_set
};
use crate::rabbitmq_controller::proof::{
    guarantee::guarantee_condition_holds, predicate::*
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
use crate::composition::vstatefulset_controller;
use crate::temporal_logic::rules::*;

use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

use crate::vdeployment_controller::model::reconciler::VDeploymentReconciler;
use crate::vdeployment_controller::trusted::rely_guarantee::*;
use crate::vreplicaset_controller::model::reconciler::VReplicaSetReconciler;
use crate::vreplicaset_controller::trusted::spec_types::VReplicaSetView;
use crate::vreplicaset_controller::trusted::rely_guarantee::*;

verus !{

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
                assert(composed_vsts_match(rmq)(s));
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

}