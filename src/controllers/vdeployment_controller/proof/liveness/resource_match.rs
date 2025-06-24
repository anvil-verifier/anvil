use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::{
    trusted::{spec_types::*, step::*, util::*, liveness_theorem::*},
    model::{install::*, reconciler::*},
    proof::{predicate::*, helper_lemmas::*},
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
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
    spec.entails(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)), list_resp_in_flight(vd, controller_id, resp_msg), new_vrs_does_not_exists_in_etcd(vd)))
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterCreateNewVRS)), pending_create_req_in_flight(vd, controller_id), new_vrs_does_not_exists_in_etcd(vd))))),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    let pre = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
        list_resp_in_flight(vd, controller_id, resp_msg),
        new_vrs_does_not_exists_in_etcd(vd)
    );
    let post = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterCreateNewVRS)),
        pending_create_req_in_flight(vd, controller_id),
        new_vrs_does_not_exists_in_etcd(vd)
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
                    let msg = input.get_Some_0();
                    lemma_api_request_other_than_pending_req_msg_maintains_filter_old_and_new_vrs(
                        s, s_prime, vd, cluster, controller_id, msg
                    );
                    assume(false);
                },
                Step::ControllerStep(input) => {
                    if input.0 == controller_id
                        && input.1 == Some(resp_msg)
                        && input.2 == Some(vd.object_ref()) {
                        VDeploymentReconcileState::marshal_preserves_integrity();
                        VReplicaSetView::marshal_preserves_integrity();
                        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
                        assert(filter_old_and_new_vrs(vd, filter_vrs_list(vd, objects_to_vrs_list(resp_objs).unwrap()))
                            == filter_old_and_new_vrs_on_etcd(vd, s.resources()));
                        assert(objects_to_vrs_list(resp_objs).is_Some());
                        let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, filter_vrs_list(vd, objects_to_vrs_list(resp_objs).unwrap()));
                        assert((new_vrs, old_vrs_list) == filter_old_and_new_vrs_on_etcd(vd, s.resources()));
                        assert(new_vrs.is_None());
                        assert(resp_msg.content.get_list_response().res.is_Ok());
                        let (state_prime, req) = create_new_vrs(old_vrs_list, vd);
                        assert(state_prime == VDeploymentReconcileState {
                            reconcile_step: VDeploymentReconcileStepView::AfterCreateNewVRS,
                            new_vrs: Some(make_replica_set(vd)),
                            old_vrs_list: old_vrs_list,
                        });
                        assert(req == Some(RequestView::<VoidEReqView>::KRequest(APIRequest::CreateRequest(CreateRequest {
                            namespace: vd.metadata.namespace.unwrap(),
                            obj: make_replica_set(vd).marshal(),
                        }))));
                        assert(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.is_Some()) by {
                            assert(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0().content.get_APIRequest_0()
                                == APIRequest::CreateRequest(CreateRequest {
                                    namespace: vd.metadata.namespace.unwrap(),
                                    obj: make_replica_set(vd).marshal(),
                                }));
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