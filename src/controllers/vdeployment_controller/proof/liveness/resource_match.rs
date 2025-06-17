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

//pub open spec fn old_vrs_rank_n_in_etcd(vd: VDeploymentView, n: nat) -> StatePred<ClusterState> {
//    |s: ClusterState| {
//        let dyn_vrs_list = s.resources().values().to_seq().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind());
//        let vrs_list = objects_to_vrs_list(dyn_vrs_list);
//        let filtered_vrs_list = filter_vrs_list(vrs_list.unwrap(), vd);
//        let (_, old_vrs_list) = filter_old_and_new_vrs(filtered_vrs_list, vd);
//        &&& vrs_list.is_Some()
//        &&& old_vrs_list.len() == n
//    }
//}
// // if old vrs list length reaches n in controller state, etcd will follow up
// #[verifier(external_body)]
// pub proof fn local_old_vrs_rank_leads_to_etcd_old_vrs_rank(
//     vd: VDeploymentView, controller_id: int, cluster: Cluster, n: nat
// )
// requires
//     cluster.type_is_installed_in_cluster::<VDeploymentView>(),
//     cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
//     spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
//     spec.entails(always(lift_action(cluster.next()))),
//     spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
// ensures
//     // Q: How to reason about Error state in wf proof
//     spec.entails(lift_state(lift_local(controller_id, vd, at_step_or!((AfterScaleDownOldVRS, old_vrs_list_len(n)))))
//         .leads_to(lift_state(old_vrs_rank_n_in_etcd(vd, n))));
// 
// pub proof fn local_new_vrs_match_leads_to_etcd_new_vrs_match(
//     vd: VDeploymentView, controller_id: int, cluster: Cluster
// )
// requires
//     cluster.type_is_installed_in_cluster::<VDeploymentView>(),
//     cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
//     spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
//     spec.entails(always(lift_action(cluster.next()))),
//     spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
// ensures
//     spec.entails(lift_state(lift_local(controller_id, vd, at_step_or!(AfterScaleUpNewVRS)))
//         .leads_to(lift_state(new_vrs_match_in_etcd(vd))));

// keep filters consistent with filter_old_and_new_vrs
pub open spec fn local_new_vrs_has_replicas_of(vd: VDeploymentView, n: nat) -> spec_fn(ReconcileLocalState) -> bool {
    // vrs.spec.replicas.is_None => 1 replica
    |s: ReconcileLocalState| {
        let vds = VDeploymentReconcileState::unmarshal(s).unwrap();
        &&& vds.new_vrs.is_Some() && vds.new_vrs.unwrap().spec.replicas.unwrap_or(1) == n
        &&& match_template_without_hash(vd, vds.new_vrs.unwrap())
    }
}

pub open spec fn local_new_vrs_is_none() -> spec_fn(ReconcileLocalState) -> bool {
    // vrs.spec.replicas.is_None => 1 replica
    |s: ReconcileLocalState| {
        let vds = VDeploymentReconcileState::unmarshal(s).unwrap();
        vds.new_vrs.is_None()
    }
}

pub open spec fn local_old_vrs_list_has_len_of(vd: VDeploymentView, n: nat) -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
        let vds = VDeploymentReconcileState::unmarshal(s).unwrap();
        &&& vds.old_vrs_list.len() == n
        &&& forall |vrs: VReplicaSetView| #![trigger match_template_without_hash(vd, vrs)] 
            vds.old_vrs_list.contains(vrs)
            ==> !match_template_without_hash(vd, vrs) && (vrs.spec.replicas.is_None() || vrs.spec.replicas.unwrap() > 0)
    }
}

// keep consistent with current_state_matches
pub open spec fn etcd_only_one_vrs_has_replicas_of(vd: VDeploymentView, n: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let dyn_vrs_list = s.resources().values().to_seq().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind());
        let vrs_list = objects_to_vrs_list(dyn_vrs_list);
        let filtered_vrs_list = filter_vrs_list(vrs_list.unwrap(), vd);
        let (new_vrs_list, _) = filter_old_and_new_vrs(filtered_vrs_list, vd);
        let new_vrs = new_vrs_list[0];
        // not needed
        // &&& vrs_list.is_Some()
        &&& new_vrs_list.len() == 1
        &&& new_vrs.spec.replicas.unwrap_or(1) == n
    }
}

pub open spec fn etcd_new_vrs_does_not_exist(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let dyn_vrs_list = s.resources().values().to_seq().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind());
        let vrs_list = objects_to_vrs_list(dyn_vrs_list);
        let filtered_vrs_list = filter_vrs_list(vrs_list.unwrap(), vd);
        // &&& vrs_list.is_Some()
        filter_old_and_new_vrs(filtered_vrs_list, vd).0.len() == 0
    }
}

pub open spec fn etcd_old_vrs_list_has_len_of(vd: VDeploymentView, n: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let dyn_vrs_list = s.resources().values().to_seq().filter(|obj: DynamicObjectView| obj.kind == VReplicaSetView::kind());
        let vrs_list = objects_to_vrs_list(dyn_vrs_list);
        let filtered_vrs_list = filter_vrs_list(vrs_list.unwrap(), vd);
        let (_, old_vrs_list) = filter_old_and_new_vrs(filtered_vrs_list, vd);
        // &&& vrs_list.is_Some()
        filter_old_and_new_vrs(filtered_vrs_list, vd).1.len() == n
    }
}

#[verifier(external_body)]
pub proof fn lemma_local_state_leads_to_etcd_state_since_list_vrs_step(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
ensures
    spec.entails(lift_state(lift_local(controller_id, vd, at_step_or!(AfterCreateNewVRS, AfterScaleNewVRS, AfterScaleDownOldVRS, Done)))) ==> {
        &&& forall |n: nat| spec.entails(lift_state(lift_local(controller_id, vd, #[trigger] local_new_vrs_has_replicas_of(vd, n)))
                               .leads_to(lift_state( #[trigger] etcd_only_one_vrs_has_replicas_of(vd, n))))
        &&& forall |n: nat| spec.entails(lift_state(lift_local(controller_id, vd, #[trigger] local_old_vrs_list_has_len_of(vd, n)))
                               .leads_to(lift_state( #[trigger] etcd_old_vrs_list_has_len_of(vd, n))))
        &&&                 spec.entails(lift_state(lift_local(controller_id, vd, #[trigger] local_new_vrs_is_none()))
                               .leads_to(lift_state( #[trigger] etcd_new_vrs_does_not_exist(vd))))
    }{}

}