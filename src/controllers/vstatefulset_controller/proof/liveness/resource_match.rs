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
    proof::{predicate::*, helper_lemmas::*, liveness::{api_actions::*, state_predicates::*}, guarantee, shield_lemma},
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
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![Init])(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s_prime),
    pending_list_pod_req_in_flight(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_after_send_list_pod_req_to_receive_list_pod_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts, controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s),
    pending_list_pod_req_in_flight(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s_prime),
    pending_list_pod_resp_in_flight(vsts, controller_id)(s_prime),
{
    lemma_list_pod_request_returns_ok_with_objs_matching_vsts(
        s, s_prime, vsts, cluster, controller_id
    );
}

// Then, prove at_step_or![GetPVC, CreateNeeded, UpdateNeeded, DeleteCondemned, DeleteOutdated] |=
// || at_step![GetPVC] || at_step![CreateNeeded] || at_step![UpdateNeeded] || at_step![DeleteCondemned] || at_step![DeleteOutdated]
// and go to next step with local_state_is_valid_and_coherent
pub proof fn lemma_from_list_resp_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    resp_msg_or_none(s, vsts, controller_id) is Some,
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts, controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s),
    pending_list_pod_resp_in_flight(vsts, controller_id)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step_or![GetPVC, CreateNeeded, UpdateNeeded, DeleteCondemned, DeleteOutdated])(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
{
    let current_local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let triggering_cr = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr).unwrap();
    let resp_msg = resp_msg_or_none(s, vsts, controller_id).unwrap();
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
    assert(local_state_is_valid_and_coherent(vsts, controller_id)(s_prime)) by {
        let filtered_pods = pods.filter(pod_filter(vsts));
        let (needed, condemned) = partition_pods(vsts_name, replicas, filtered_pods);
        assert forall |pod: PodView| #[trigger] filtered_pods.contains(pod) implies {
            let obj = s.resources()[pod.object_ref()];
            &&& pod.metadata.name is Some
            &&& pod.metadata.namespace is Some
            &&& pod.metadata.namespace->0 == vsts.metadata.namespace->0
            &&& pod.metadata.owner_references_contains(vsts.controller_owner_ref())
            &&& s.resources().contains_key(pod.object_ref())
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        } by {
            PodView::marshal_preserves_metadata();
            seq_filter_contains_implies_seq_contains(pods, pod_filter(vsts), pod);
            let i = choose |i: int| 0 <= i < pods.len() && pods[i as int] == pod;
            assert(objs.contains(objs[i]));
            assert(PodView::unmarshal(objs[i]) is Ok);
            assert(PodView::unmarshal(objs[i])->Ok_0 == pod);
        }
        assert(partition_pods(vsts_name, replicas, filtered_pods) == partition_pods(triggering_cr.metadata.name->0, replicas, filtered_pods));
        assert(next_local_state.needed == needed);
        assert(next_local_state.condemned == condemned);
        let condemned_ord_filter = |pod: PodView| get_ordinal(vsts_name, pod.metadata.name->0) is Some && get_ordinal(vsts_name, pod.metadata.name->0)->0 >= replicas;
        assert(condemned.to_set() == filtered_pods.filter(condemned_ord_filter).to_set()) by {
            let leq = |p1: PodView, p2: PodView| get_ordinal(vsts_name, p1.metadata.name->0)->0 >= get_ordinal(vsts_name, p2.metadata.name->0)->0;
            assert(condemned == filtered_pods.filter(condemned_ord_filter).sort_by(leq));
            lemma_sort_by_does_not_add_or_delete_elements(filtered_pods.filter(condemned_ord_filter), leq);
        }
        assert forall |pod: PodView| #[trigger] condemned.contains(pod) implies filtered_pods.contains(pod) by {
            assert(filtered_pods.filter(condemned_ord_filter).contains(pod)) by {
                assert(condemned.to_set().contains(pod));
                assert(filtered_pods.filter(condemned_ord_filter).contains(pod));
            }
            seq_filter_contains_implies_seq_contains(filtered_pods, condemned_ord_filter, pod);
        }
        assert(forall |pod: PodView| #[trigger] condemned.contains(pod) ==> pod.metadata.name is Some);
        // coherence of needed pods
        assert forall |ord: nat| #![trigger needed[ord as int]] ord < needed.len() && needed[ord as int] is Some implies {
            let needed_pod = needed[ord as int]->0;
            let key = ObjectRef {
                kind: Kind::PodKind,
                namespace: vsts.metadata.namespace->0,
                name: needed_pod.metadata.name->0,
            };
            let obj = s.resources()[key];
            &&& needed_pod.object_ref() == key
            &&& needed_pod.metadata.name == Some(pod_name(vsts.metadata.name->0, ord))
            &&& s.resources().contains_key(key)
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        } by {
            assert(get_pod_with_ord(vsts_name, filtered_pods, ord) is Some);
            seq_filter_contains_implies_seq_contains(filtered_pods, pod_has_ord(vsts_name, ord), needed[ord as int]->0);
        }
        // coherence of condemned pods
        let unlawful_cond = |ord: nat| {
            let key = ObjectRef {
                kind: PodView::kind(),
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s.resources()[key];
            &&& ord >= vsts.spec.replicas.unwrap_or(1)
            &&& s.resources().contains_key(key)
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
            &&& !exists |pod: PodView| #[trigger] condemned.contains(pod) && pod.object_ref() == key
        };
        if exists |ord: nat| #![trigger pod_name(vsts.metadata.name->0, ord)] unlawful_cond(ord) {
            let ord = choose |ord: nat| #![trigger pod_name(vsts.metadata.name->0, ord)] unlawful_cond(ord);
            let key = ObjectRef {
                kind: PodView::kind(),
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s.resources()[key];
            let owner_ref_filter = |obj: DynamicObjectView| obj.metadata.owner_references_contains(vsts.controller_owner_ref());
            let filtered_resp_objs = objs.filter(owner_ref_filter);
            get_ordinal_eq_pod_name(vsts_name, ord, key.name);
            // prove that object can pass through all filters and enter condemned
            assert(s.resources().values().filter(valid_owned_object_filter(vsts)).contains(obj));
            assert(s.resources().values().filter(valid_owned_object_filter(vsts)).map(|obj: DynamicObjectView| obj.object_ref()).contains(key));
            assert(filtered_resp_objs.to_set().map(|obj: DynamicObjectView| obj.object_ref()).contains(key));
            assert(get_ordinal(vsts_name, key.name) == Some(ord));
            assert({
                &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
                &&& vsts.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
            }); // by all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_labels
            assert(exists |obj: DynamicObjectView| #[trigger] filtered_resp_objs.contains(obj) && obj.object_ref() == key);
            let condemned_obj = choose |obj: DynamicObjectView| #[trigger] filtered_resp_objs.contains(obj) && obj.object_ref() == key;
            seq_filter_contains_implies_seq_contains(objs, owner_ref_filter, condemned_obj);
            let condemned_pod = PodView::unmarshal(condemned_obj)->Ok_0;
            PodView::marshal_preserves_metadata();
            assert(condemned_pod.object_ref() == key);
            assert(filtered_pods.contains(condemned_pod)) by {
                assert(pods.contains(condemned_pod)) by {
                    let i = choose |i: int| 0 <= i < objs.len() && objs[i] == condemned_obj;
                    assert(PodView::unmarshal(objs[i]) is Ok);
                    assert(pods[i] == condemned_pod);
                    assert(pods.contains(pods[i]));
                }
                seq_filter_contains_implies_seq_contains(pods, pod_filter(vsts), condemned_pod);
            }
            assert(condemned.contains(condemned_pod) && condemned_pod.object_ref() == key) by {
                assert(filtered_pods.filter(condemned_ord_filter).contains(condemned_pod));
                assert(condemned.to_set().contains(condemned_pod));
            }
            assert(false);
        }
    }
}

// TODO: check if req itself can be exposed and that exposure is beneficial (msg contains rpc_id)
// and do we need to expose next_local_state as it can be extracted from s_prime
pub proof fn lemma_from_at_get_pvc_step_to_after_get_pvc_step(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![GetPVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterGetPVC])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_pvc_req_in_flight(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_after_send_get_pvc_req_to_receive_get_pvc_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts, controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterGetPVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_pvc_req_in_flight(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterGetPVC])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_pvc_resp_msg_in_flight(vsts, controller_id)(s_prime),
{
    lemma_get_pvc_request_returns_ok_or_err_response(
        s, s_prime, vsts, cluster, controller_id
    );
}

}