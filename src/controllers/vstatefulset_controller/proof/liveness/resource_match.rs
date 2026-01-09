use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::{types::*, state_machine::*},
    cluster::*, 
    message::*
};
use crate::vstatefulset_controller::{
    trusted::{spec_types::*, step::*, liveness_theorem::*, rely},
    model::{install::*, reconciler::*},
    proof::{predicate::*, liveness::{api_actions::*, state_predicates::*}, guarantee, shield_lemma},
};
use crate::vstatefulset_controller::trusted::step::VStatefulSetReconcileStepView::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{seq_lib::*, set_lib::*};
use vstd::{seq_lib::*, map_lib::*, multiset::*, relations::*};
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub proof fn lemma_from_init_to_current_state_matches(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely::vsts_rely_conditions(cluster, controller_id)))),
ensures
    spec.entails(lift_state(and!(
            at_vsts_step(vsts, controller_id, at_step![Init]),
            no_pending_req_in_cluster(vsts, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vsts_step(vsts, controller_id, at_step![Done]),
            no_pending_req_in_cluster(vsts, controller_id),
            current_state_matches(vsts)
        )))),
{}

pub proof fn lemma_from_init_step_to_send_list_pod_req(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
ensures
    spec.entails(lift_state(and!(at_vsts_step(vsts, controller_id, at_step![Init]), no_pending_req_in_cluster(vsts, controller_id)))
       .leads_to(lift_state(and!(at_vsts_step(vsts, controller_id, at_step![AfterListPod]), pending_list_req_in_flight(vsts, controller_id))))),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
    let pre = and!(
        at_vsts_step(vsts, controller_id, at_step![Init]),
        no_pending_req_in_cluster(vsts, controller_id)
    );
    let post = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterListPod]),
        pending_list_req_in_flight(vsts, controller_id)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let input = (None::<Message>, Some(vsts.object_ref()));
    assert(forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) ==> pre(s_prime) || post(s_prime));
    cluster.lemma_pre_leads_to_post_by_controller(
        spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post
    );
}

pub proof fn lemma_from_after_send_list_pod_req_to_receive_list_pod_resp(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
ensures
    spec.entails(lift_state(and!(at_vsts_step(vsts, controller_id, at_step![AfterListPod]), req_msg_is_pending_list_req_in_flight(vsts, controller_id, req_msg)))
       .leads_to(lift_state(and!(at_vsts_step(vsts, controller_id, at_step![AfterListPod]), exists_pending_list_resp_in_flight_and_match_req(vsts, controller_id))))),
{
    let pre = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterListPod]),
        req_msg_is_pending_list_req_in_flight(vsts, controller_id, req_msg)
    );
    let post = and!(
        at_vsts_step(vsts, controller_id, at_step![AfterListPod]),
        exists_pending_list_resp_in_flight_and_match_req(vsts, controller_id)
    );
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s)
    };
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id))
    );
    let input = Some(req_msg);
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                if msg == req_msg {
                    let resp_msg = lemma_list_pod_request_returns_ok_with_objs_matching_vsts(
                        s, s_prime, vsts, cluster, controller_id, msg
                    );
                    // instantiate existential quantifier.
                    assert(s_prime.in_flight().contains(resp_msg));
                }
            },
            _ => {}
        }
    }
    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        let msg = input->0;
        let resp_msg = lemma_list_pod_request_returns_ok_with_objs_matching_vsts(
            s, s_prime, vsts, cluster, controller_id, msg,
        );
        assert(s_prime.in_flight().contains(resp_msg));
    }
    cluster.lemma_pre_leads_to_post_by_api_server(
        spec, input, stronger_next, APIServerStep::HandleRequest, pre, post
    );
}

pub proof fn lemma_from_list_resp_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, resp_msg: Message
) -> (next_local_state: VStatefulSetReconcileState)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp_msg), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s),
    resp_msg_is_ok_list_resp_of_pods(vsts, resp_msg, s),
ensures
    local_state_is(vsts, controller_id, next_local_state)(s_prime),
    at_vsts_step(vsts, controller_id, at_step_or![GetPVC, CreateNeeded, UpdateNeeded, DeleteCondemned, DeleteOutdated])(s_prime),
{
    let current_local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let triggering_cr = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr).unwrap();
    let wrapped_resp = Some(ResponseView::KResponse(resp_msg.content->APIResponse_0));
    let next_local_state = handle_after_list_pod(vsts, wrapped_resp, current_local_state).0;
    let objs = resp_msg.content.get_list_response().res->Ok_0;
    let pods = objects_to_pods(objs)->0;
    VStatefulSetReconcileState::marshal_preserves_integrity();
    VStatefulSetView::marshal_preserves_integrity();
    assert(objects_to_pods(objs) is Some);
    assert(pod_filter(vsts) == pod_filter(triggering_cr));
    let next_local_state_from_cluster = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    // for better proof stability
    assert(next_local_state =~= next_local_state_from_cluster) by {
        assert(next_local_state.needed == next_local_state_from_cluster.needed);
        assert(next_local_state.condemned == next_local_state_from_cluster.condemned);
        assert(next_local_state.pvcs == next_local_state_from_cluster.pvcs);
    }
    assert(objs == extract_some_k_list_resp_view(wrapped_resp)->Ok_0);
    assert(next_local_state.reconcile_step != Error);
    let replicas = vsts.spec.replicas.unwrap_or(1) as nat;
    let vsts_name = vsts.metadata.name->0;
    assert(replicas >= 0);
    assert(local_state_is(vsts, controller_id, next_local_state)(s_prime)) by {
        let filtered_pods = pods.filter(pod_filter(vsts));
        let (needed, condemned) = partition_pods(vsts_name, replicas, filtered_pods);
        assert forall |pod: PodView| #[trigger] filtered_pods.contains(pod) implies {
            &&& pod.metadata.name is Some
            &&& pod.metadata.namespace is Some
            &&& pod.metadata.namespace->0 == vsts.metadata.namespace->0
            &&& pod.metadata.owner_references_contains(vsts.controller_owner_ref())
            &&& s.resources().contains_key(pod.object_ref())
        } by {
            PodView::marshal_preserves_metadata();
            seq_filter_contains_implies_seq_contains(pods, pod_filter(vsts), pod);
            let i = choose |i: int| 0 <= i < pods.len() && pods[i as int] == pod;
            assert(objs.contains(objs[i]));
            assert(PodView::unmarshal(objs[i]) is Ok);
            assert(PodView::unmarshal(objs[i])->Ok_0 == pod);
        }
        assert(partition_pods(vsts_name, replicas, filtered_pods) == 
            partition_pods(triggering_cr.metadata.name->0, replicas, filtered_pods));
        assert(next_local_state.needed == needed);
        assert(next_local_state.condemned == condemned);
        let condemned_ord_filter = |pod: PodView| get_ordinal(vsts_name, pod) is Some && get_ordinal(vsts_name, pod)->0 >= replicas;
        assert forall |pod: PodView| #[trigger] condemned.contains(pod) implies filtered_pods.contains(pod) by {
            let leq = |p1: PodView, p2: PodView| get_ordinal(vsts_name, p1)->0 >= get_ordinal(vsts_name, p2)->0;
            assert(condemned == filtered_pods.filter(condemned_ord_filter).sort_by(leq));
            assume(total_ordering(leq)); // TODO: prove or skip
            filtered_pods.filter(condemned_ord_filter).lemma_sort_by_ensures(leq);
            seq_filter_contains_implies_seq_contains(filtered_pods, condemned_ord_filter, pod);
        }
        assert(forall |pod: PodView| #[trigger] condemned.contains(pod)
            ==> pod.metadata.name is Some);
        // coherence of needed pods
        assert forall |ord: nat| #![trigger needed[ord as int]] ord < needed.len() && needed[ord as int] is Some implies {
            let needed_pod = needed[ord as int]->0;
            let key = ObjectRef {
                kind: Kind::PodKind,
                namespace: vsts.metadata.namespace->0,
                name: needed_pod.metadata.name->0,
            };
            &&& needed_pod.object_ref() == key
            &&& needed_pod.metadata.name == Some(pod_name(vsts.metadata.name->0, ord))
            &&& s.resources().contains_key(key)
        } by {
            assert(get_pod_with_ord(vsts_name, filtered_pods, ord) is Some);
            seq_filter_contains_implies_seq_contains(filtered_pods, pod_has_ord(vsts_name, ord), needed[ord as int]->0);
        }
        // coherence of condemned pods
    }
    return next_local_state;
}
}