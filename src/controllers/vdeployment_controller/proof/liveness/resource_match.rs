use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::{
    trusted::{spec_types::*, step::*, util::*, liveness_theorem::current_state_matches},
    model::{install::*, reconciler::*},
    proof::predicate::*,
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use vstd::prelude::*;

verus !{

pub proof fn lemma_from_init_step_to_send_list_vrs_req(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
ensures
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(Init)), no_pending_req_in_cluster(vd, controller_id)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)), pending_list_req_in_flight(vd, controller_id))))),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(Init)),
        no_pending_req_in_cluster(vd, controller_id)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
        pending_list_req_in_flight(vd, controller_id)
    );
    assert(spec.entails(lift_state(pre).leads_to(lift_state(post)))) by {
        let input = (None::<Message>, Some(vd.object_ref()));
        let stronger_next = |s, s_prime: ClusterState| {
            &&& cluster.next()(s, s_prime)
            &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        };
        combine_spec_entails_always_n!(spec,
            lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
        );
        // this assertion makes proof 86% faster
        assert(forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) ==> pre(s_prime) || post(s_prime));
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
        );
    }
}

pub proof fn lemma_from_receive_list_resp_and_no_updated_vrs_in_etcd_to_send_create_vrs_req(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, resp_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
ensures
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)), list_resp_in_flight(vd, controller_id, resp_msg), etcd_new_vrs_does_not_exist(vd)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterCreateNewVRS)), pending_create_req_in_flight(vd, controller_id))))),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
        list_resp_in_flight(vd, controller_id, resp_msg),
        etcd_new_vrs_does_not_exist(vd)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterCreateNewVRS)),
        pending_create_req_in_flight(vd, controller_id)
    );
    assert(spec.entails(lift_state(pre).leads_to(lift_state(post)))) by {
        let input = (Some(resp_msg), Some(vd.object_ref()));
        let stronger_next = |s, s_prime: ClusterState| {
            &&& cluster.next()(s, s_prime)
            &&& cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s)
        };
        combine_spec_entails_always_n!(spec,
            lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id))
        );
        assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    assume(false);
                },
                Step::ControllerStep(input) => {
                    assert(post(s_prime)) by {
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        let vrs_list_or_none = objects_to_vrs_list(resp_objs);
                        assert(vrs_list_or_none.is_Some());
                        let (new_vrs_list, old_vrs_list) = filter_old_and_new_vrs(filter_vrs_list(vrs_list_or_none.unwrap(), vd), vd);
                        assert(new_vrs_list.len() == 0) by {
                            // need additional reliance lemma on other controller will not create vrs that matches these filters
                        }
                    }
                },
                _ => {}
            }
        }
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
        );
    }
}

}