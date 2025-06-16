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

pub proof fn lemma_from_init_to_current_state_matches(
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
       .leads_to(lift_state(and!(at_vd_step_with_vd(vd, controller_id, at_step_or!(Done)), current_state_matches(vd))))),
{
    let no_pending_req_at_init = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(Init)),
        no_pending_req_in_cluster(vd, controller_id)
    );
    let pending_list_req_after_list_vrs = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
        pending_list_req_in_flight(vd, controller_id)
    );
    assert(spec.entails(lift_state(no_pending_req_at_init).leads_to(lift_state(pending_list_req_after_list_vrs)))) by {
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
        assert forall |s, s_prime| no_pending_req_at_init(s) && #[trigger] stronger_next(s, s_prime)
            implies no_pending_req_at_init(s_prime) || pending_list_req_after_list_vrs(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    if input.0 == controller_id && input.2 == Some(vd.object_ref()) {
                        let msg = s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.get_Some_0();
                        let req = msg.content.get_APIRequest_0();
                        assert(s_prime.ongoing_reconciles(controller_id)[vd.object_ref()].pending_req_msg.is_Some());
                        assert(msg.src.is_controller_id(controller_id));
                        assert(msg.dst == HostId::APIServer);
                        assert(req.is_ListRequest());
                        assert(req.get_ListRequest_0() == ListRequest{
                            kind: VReplicaSetView::kind(),
                            namespace: vd.metadata.namespace.unwrap()
                        });
                        assert(pending_list_req_after_list_vrs(s_prime));
                    } else {
                    }
                },
                _ => {},
            }
        }
        cluster.lemma_pre_leads_to_post_by_controller(
            spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, no_pending_req_at_init, pending_list_req_after_list_vrs
        );
    }
    let exist_list_resp_after_list_vrs = and!(
        at_vd_step_with_vd(vd, controller_id, at_step_or!(AfterListVRS)),
        exists_list_resp_in_flight(vd, controller_id)
    );
    // Q: what's the better choice? exists or instantiated msg?
    // Q: Is it possible to simplify the liveness proof with quantifiers w/wo ranking function?
    assume(false);
}
}