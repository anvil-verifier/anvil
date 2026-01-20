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
    proof::{predicate::*, helper_lemmas::*, helper_invariants, liveness::{api_actions::*, state_predicates::*}, guarantee, shield_lemma},
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

// PVC loop terminates. Proved using rank function on PVC index
#[verifier(rlimit(100))]
pub proof fn lemma_pvc_steps_terminates(
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
        at_vsts_step(vsts, controller_id, at_step![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id)
    ))))
{
    let get_pvc_state_with_pvc_index = |pvc_index: nat| and!(
        at_vsts_step(vsts, controller_id, at_step![GetPVC]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id),
        pvc_index_is(vsts, controller_id, pvc_index)
    );
    let create_or_update_needed_step = and!(
        at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id)
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
    assert forall |pvc_index: nat| spec.entails(lift_state(#[trigger] get_pvc_state_with_pvc_index(pvc_index))
        .leads_to(lift_state(get_pvc_state_with_pvc_index((pvc_index + 1) as nat)))) by {
        let get_pvc_state = and!(
            at_vsts_step(vsts, controller_id, at_step![GetPVC]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_index_is(vsts, controller_id, pvc_index)
        );
        let after_get_pvc_state = and!(
            at_vsts_step(vsts, controller_id, at_step![AfterGetPVC]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            pending_get_pvc_req_in_flight(vsts, controller_id),
            pvc_index_is(vsts, controller_id, pvc_index)
        );
        assert(spec.entails(lift_state(get_pvc_state).leads_to(lift_state(after_get_pvc_state)))) by {
            assert forall |s, s_prime| get_pvc_state(s) && #[trigger] stronger_next(s, s_prime) implies get_pvc_state(s_prime) || after_get_pvc_state(s_prime) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        lemma_api_request_other_than_pending_req_msg_maintains_local_state_cocherence(s, s_prime, vsts, cluster, controller_id, input->0);
                    },
                    Step::ControllerStep(input) => {
                        if input.0 == controller_id && input.2 == Some(vsts.object_ref()) {
                            lemma_from_at_get_pvc_step_to_after_get_pvc_step(s, s_prime, vsts, cluster, controller_id, pvc_index);
                        }
                    },
                    _ => {}
                }
            }
            let input = (None, Some(vsts.object_ref()));
            cluster.lemma_pre_leads_to_post_by_controller(
                spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, get_pvc_state, after_get_pvc_state
            );
        }
        let after_get_pvc_state_with_request = |msg| and!(
            at_vsts_step(vsts, controller_id, at_step![AfterGetPVC]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            pending_get_pvc_req_in_flight(vsts, controller_id),
            pvc_index_is(vsts, controller_id, pvc_index),
            req_msg_is(msg, vsts.object_ref(), controller_id)
        );
        let after_get_pvc_state = and!(
            at_vsts_step(vsts, controller_id, at_step![AfterGetPVC]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            pending_get_pvc_resp_in_flight_reflecting_existence_of_requested_pvc(vsts, controller_id),
            pvc_index_is(vsts, controller_id, pvc_index)
        );
        assert forall |msg| spec.entails(lift_state(#[trigger] after_get_pvc_state_with_request(msg)).leads_to(lift_state(after_get_pvc_state))) by {
            assert forall |s, s_prime| after_get_pvc_state_with_request(msg)(s) && #[trigger] stronger_next(s, s_prime) implies
                after_get_pvc_state_with_request(msg)(s_prime) || after_get_pvc_state(s_prime) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {},
                    Step::APIServerStep(input) => {
                        if input == Some(msg) {
                            lemma_get_pvc_request_returns_ok_or_err_response(s, s_prime, vsts, cluster, controller_id, msg);
                        } else {
                            lemma_api_request_other_than_pending_req_msg_maintains_local_state_cocherence(s, s_prime, vsts, cluster, controller_id, input->0);
                        }
                    },
                    // harden proof
                    Step::BuiltinControllersStep(_) => {},
                    Step::PodMonkeyStep(_) => {},
                    Step::ScheduleControllerReconcileStep(_) => {},
                    _ => {}
                }
            }
            let input = Some(msg);
            assert forall |s, s_prime| after_get_pvc_state_with_request(msg)(s) && #[trigger] stronger_next(s, s_prime) && cluster.api_server_next().forward(input)(s, s_prime)
                implies after_get_pvc_state(s_prime) by {
                lemma_get_pvc_request_returns_ok_or_err_response(s, s_prime, vsts, cluster, controller_id, msg);
            }
            cluster.lemma_pre_leads_to_post_by_api_server(
                spec, input, stronger_next, APIServerStep::HandleRequest, after_get_pvc_state_with_request(msg), after_get_pvc_state
            );
        }
        let skip_or_create_pvc_state = and!(
            at_vsts_step(vsts, controller_id, at_step_or![SkipPVC, CreatePVC]),
            local_state_is_valid_and_coherent(vsts, controller_id), 
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_index_is(vsts, controller_id, pvc_index)
        );
        assume(false);
        let skip_pvc_state = and!(
            at_vsts_step(vsts, controller_id, at_step![SkipPVC]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_index_is(vsts, controller_id, pvc_index)
        );
        let create_pvc_state = and!(
            at_vsts_step(vsts, controller_id, at_step![CreatePVC]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            no_pending_req_in_cluster(vsts, controller_id),
            pvc_index_is(vsts, controller_id, pvc_index)
        );
        let after_create_pvc_state_with_request = and!(
            at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            pending_create_pvc_req_in_flight(vsts, controller_id),
            pvc_index_is(vsts, controller_id, pvc_index + nat1!())
        );
        let after_create_pvc_state_with_response = and!(
            at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC]),
            local_state_is_valid_and_coherent(vsts, controller_id),
            pending_create_pvc_resp_msg_in_flight_and_created_pvc_exists(vsts, controller_id),
            pvc_index_is(vsts, controller_id, pvc_index + nat1!())
        );
    }
    let create_needed_pod_state = and!(
        at_vsts_step(vsts, controller_id, at_step![CreateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id)
    );
    let update_needed_pod_state = and!(
        at_vsts_step(vsts, controller_id, at_step![UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id)
    );
    assume(false);
}

#[verifier(external_body)] // prove using rank function on needed index
pub proof fn lemma_from_needed_pod_steps_to_condemned_or_outdated_pod_steps(
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
        at_vsts_step(vsts, controller_id, at_step_or![CreateNeeded, UpdateNeeded]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id)
    )).leads_to(lift_state(and!(
        at_vsts_step(vsts, controller_id, at_step_or![DeleteCondemned, DeleteOutdated]),
        local_state_is_valid_and_coherent(vsts, controller_id),
        no_pending_req_in_cluster(vsts, controller_id)
    ))))
{}

pub proof fn lemma_from_at_init_step_to_after_list_pod_step(
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
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
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
    resp_msg_or_none(s, vsts.object_ref(), controller_id) is Some,
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
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
    let resp_msg = resp_msg_or_none(s, vsts.object_ref(), controller_id).unwrap();
    let wrapped_resp = Some(ResponseView::KResponse(resp_msg.content->APIResponse_0));
    let next_local_state = handle_after_list_pod(vsts, wrapped_resp, current_local_state).0;
    let objs = resp_msg.content.get_list_response().res->Ok_0;
    let pods = objects_to_pods(objs)->0;
    VStatefulSetReconcileState::marshal_preserves_integrity();
    VStatefulSetView::marshal_preserves_integrity();
    // assert(objects_to_pods(objs) is Some);
    // assert(pod_filter(vsts) == pod_filter(triggering_cr));
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
            // assert(PodView::unmarshal(objs[i]) is Ok);
            // assert(PodView::unmarshal(objs[i])->Ok_0 == pod);
        }
        assert(partition_pods(vsts_name, replicas, filtered_pods) == partition_pods(triggering_cr.metadata.name->0, replicas, filtered_pods));
        // assert(next_local_state.needed == needed);
        // assert(next_local_state.condemned == condemned);
        let condemned_ord_filter = |pod: PodView| get_ordinal(vsts_name, pod.metadata.name->0) is Some && get_ordinal(vsts_name, pod.metadata.name->0)->0 >= replicas;
        assert(condemned.to_set() == filtered_pods.filter(condemned_ord_filter).to_set()) by {
            let leq = |p1: PodView, p2: PodView| get_ordinal(vsts_name, p1.metadata.name->0)->0 >= get_ordinal(vsts_name, p2.metadata.name->0)->0;
            assert(condemned == filtered_pods.filter(condemned_ord_filter).sort_by(leq));
            lemma_sort_by_does_not_add_or_delete_elements(filtered_pods.filter(condemned_ord_filter), leq);
        }
        assert forall |i: nat| #![trigger condemned[i as int]] i < condemned.len() implies {
            &&& filtered_pods.contains(condemned[i as int])
            &&& condemned_ord_filter(condemned[i as int])
         } by {
            let condemned_pod = condemned[i as int];
            assert(condemned.contains(condemned_pod));
            assert(filtered_pods.filter(condemned_ord_filter).contains(condemned_pod)) by {
                assert(condemned.to_set().contains(condemned_pod));
                assert(filtered_pods.filter(condemned_ord_filter).contains(condemned_pod));
            }
            seq_filter_contains_implies_seq_contains(filtered_pods, condemned_ord_filter, condemned_pod);
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
        // no negative sample of uncaptured condemned pods or needed pods, prove by contradiction
        assert forall |ord: nat| ord >= vsts.spec.replicas.unwrap_or(1) implies {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: #[trigger] pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            s.resources().contains_key(key)
                ==> exists |pod: PodView| #[trigger] condemned.contains(pod) && pod.object_ref() == key
        } by {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            if s.resources().contains_key(key) {
                let obj = s.resources()[key];
                let owner_ref_filter = |obj: DynamicObjectView| obj.metadata.owner_references_contains(vsts.controller_owner_ref());
                let filtered_resp_objs = objs.filter(owner_ref_filter);
                get_ordinal_eq_pod_name(vsts_name, ord, key.name);
                // prove that object can pass through all filters
                assert(helper_invariants::all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_labels(vsts)(s));
                assert({
                    &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
                    &&& vsts.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
                }); // by all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_labels
                assert(s.resources().values().filter(valid_owned_object_filter(vsts)).contains(obj));
                assert(s.resources().values().filter(valid_owned_object_filter(vsts)).map(|obj: DynamicObjectView| obj.object_ref()).contains(key));
                assert(filtered_resp_objs.to_set().map(|obj: DynamicObjectView| obj.object_ref()).contains(key));
                assert(get_ordinal(vsts_name, key.name) == Some(ord));
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
            }
        }
    }
}

/* .. -> GetPVC -> AfterGetPVC -> .. */
pub proof fn lemma_from_at_get_pvc_step_to_after_get_pvc_step(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![GetPVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
    pvc_index_is(vsts, controller_id, pvc_index)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterGetPVC])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_pvc_req_in_flight(vsts, controller_id)(s_prime),
    pvc_index_is(vsts, controller_id, pvc_index)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_after_send_get_pvc_req_to_receive_get_pvc_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat, req_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterGetPVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_pvc_req_in_flight(vsts, controller_id)(s),
    pvc_index_is(vsts, controller_id, pvc_index)(s),
    req_msg_is(req_msg, vsts.object_ref(), controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterGetPVC])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_pvc_resp_in_flight_reflecting_existence_of_requested_pvc(vsts, controller_id)(s_prime),
    pvc_index_is(vsts, controller_id, pvc_index)(s_prime),
{
    lemma_get_pvc_request_returns_ok_or_err_response(
        s, s_prime, vsts, cluster, controller_id, req_msg
    );
}

// TODO: talk about pvc_index's rank
pub proof fn lemma_from_get_pvc_resp_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat
)
requires
    resp_msg_or_none(s, vsts.object_ref(), controller_id) is Some,
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterGetPVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_pvc_resp_in_flight_reflecting_existence_of_requested_pvc(vsts, controller_id)(s),
    pvc_index_is(vsts, controller_id, pvc_index)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step_or![SkipPVC, CreatePVC])(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
    pvc_index_is(vsts, controller_id, pvc_index)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_skip_pvc_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![SkipPVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
    pvc_index_is(vsts, controller_id, pvc_index)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step_or![GetPVC, CreateNeeded, UpdateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
    pvc_index_is(vsts, controller_id, (pvc_index + 1) as nat)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    if local_state.pvc_index + 1 < local_state.pvcs.len() {} else if local_state.needed_index < local_state.needed.len() {}
}

pub proof fn lemma_from_create_pvc_step_to_after_create_pvc_step(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![CreatePVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
    pvc_index_is(vsts, controller_id, pvc_index)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_create_pvc_req_in_flight(vsts, controller_id)(s_prime),
    pvc_index_is(vsts, controller_id, (pvc_index + 1) as nat)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_after_send_create_pvc_req_to_receive_create_pvc_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_create_pvc_req_in_flight(vsts, controller_id)(s),
    pvc_index_is(vsts, controller_id, pvc_index)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterCreatePVC])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_create_pvc_resp_msg_in_flight_and_created_pvc_exists(vsts, controller_id)(s_prime),
    pvc_index_is(vsts, controller_id, pvc_index)(s_prime),
{
    lemma_create_pvc_request_returns_ok_or_already_exists_err_response(
        s, s_prime, vsts, cluster, controller_id
    );
}

/* .. -> SkipPVC/AfterCreatePVC -> .. */
// handle_after_create_or_skip_pvc_helper slows down the reasoning
pub proof fn lemma_from_after_create_pvc_step_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, pvc_index: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step_or![AfterCreatePVC])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_create_pvc_resp_msg_in_flight_and_created_pvc_exists(vsts, controller_id)(s),
    pvc_index_is(vsts, controller_id, pvc_index)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step_or![GetPVC, CreateNeeded, UpdateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
    pvc_index_is(vsts, controller_id, pvc_index)(s_prime),
    pvc_index < local_state(s, vsts, controller_id).pvcs.len()
        ==> local_state(s_prime, vsts, controller_id).reconcile_step == GetPVC,
    pvc_index >= local_state(s, vsts, controller_id).pvcs.len()
        ==> (local_state(s_prime, vsts, controller_id).reconcile_step == CreateNeeded || local_state(s_prime, vsts, controller_id).reconcile_step == UpdateNeeded),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    if local_state.pvc_index < local_state.pvcs.len() {} else if local_state.needed_index < local_state.needed.len() {}
}

/* .. -> CreateNeeded -> AfterCreateNeeded -> .. */
pub proof fn lemma_from_create_needed_step_to_after_create_needed_step(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![CreateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_create_needed_pod_req_in_flight(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

// TODO: anyway to increase proof automation by change the way to invoke get_ordinal_eq_pod_name?
pub proof fn lemma_from_after_send_create_needed_pod_req_to_receive_create_needed_pod_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_create_needed_pod_req_in_flight(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_create_needed_pod_resp_in_flight_and_created_pod_exists(vsts, controller_id)(s_prime),
{
    lemma_create_needed_pod_request_returns_ok_response(
        s, s_prime, vsts, cluster, controller_id
    );
    let replicas = vsts.spec.replicas.unwrap_or(1) as nat;
    let req = req_msg_or_none(s, vsts.object_ref(), controller_id).unwrap().content.get_create_request();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    // prove that creation will not affect coherence of condemned pods
    assert(local_state_is_coherent_with_etcd(vsts, next_local_state)(s_prime)) by {
        // 2.a. all pods to be condemned in etcd are captured in next_local_state.condemned
        assert forall |ord: nat| ord >= replicas implies {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: #[trigger] pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            s_prime.resources().contains_key(key)
                ==> exists |pod: PodView| #[trigger] next_local_state.condemned.contains(pod) && pod.object_ref() == key
        } by {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: #[trigger] pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            // created obj shouldn't be considered as condemned
            if !s.resources().contains_key(key) && key == req.key() {
                get_ordinal_eq_pod_name(vsts.metadata.name->0, ord, key.name);
                get_ordinal_eq_pod_name(vsts.metadata.name->0, (next_local_state.needed_index - 1) as nat, key.name);
                assert(false);
            }
        }
        // 2.b. all pods before condemned_index are deleted
        assert forall |i: nat| #![trigger next_local_state.condemned[i as int]] i < next_local_state.condemned_index implies {
            let key = next_local_state.condemned[i as int].object_ref();
            &&& !s_prime.resources().contains_key(key)
        } by {
            let condemned_pod = next_local_state.condemned[i as int];
            if req.key() == condemned_pod.object_ref() {
                let ord = get_ordinal(vsts.metadata.name->0, condemned_pod.metadata.name->0)->0;
                assert(ord >= replicas);
                get_ordinal_eq_pod_name(vsts.metadata.name->0, ord, req.key().name);
                get_ordinal_eq_pod_name(vsts.metadata.name->0, (next_local_state.needed_index - 1) as nat, req.key().name);
                assert(false);
            }
        }
    }
}

pub proof fn lemma_from_create_needed_pod_resp_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    resp_msg_or_none(s, vsts.object_ref(), controller_id) is Some,
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterCreateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_create_needed_pod_resp_in_flight_and_created_pod_exists(vsts, controller_id)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step_or![GetPVC, CreateNeeded, UpdateNeeded, DeleteCondemned, DeleteOutdated])(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

/* .. -> UpdateNeeded -> AfterUpdateNeeded -> .. */
pub proof fn lemma_from_update_needed_step_to_after_update_needed_step(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![UpdateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_then_update_needed_pod_req_in_flight(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_after_send_get_then_update_needed_pod_req_to_receive_get_then_update_needed_pod_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_then_update_needed_pod_req_in_flight(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_then_update_needed_pod_resp_in_flight(vsts, controller_id)(s_prime),
{
    lemma_get_then_update_needed_pod_request_returns_ok_response(
        s, s_prime, vsts, cluster, controller_id
    );
}

pub proof fn lemma_from_get_then_update_needed_pod_resp_to_next_state(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    resp_msg_or_none(s, vsts.object_ref(), controller_id) is Some,
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterUpdateNeeded])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_then_update_needed_pod_resp_in_flight(vsts, controller_id)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step_or![GetPVC, CreateNeeded, UpdateNeeded, DeleteCondemned, DeleteOutdated])(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_delete_condemned_step_to_after_delete_condemned_step(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![DeleteCondemned])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_then_delete_condemned_pod_req_in_flight(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_after_send_get_then_delete_condemned_pod_req_to_receive_get_then_delete_condemned_pod_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_then_delete_condemned_pod_req_in_flight(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    pending_get_then_delete_condemned_pod_resp_in_flight_and_condemned_pod_is_deleted(vsts, controller_id)(s_prime),
{
    let req_msg = req_msg_or_none(s, vsts.object_ref(), controller_id).unwrap();
    lemma_get_then_delete_pod_request_returns_ok_or_not_found_err(
        s, s_prime, vsts, cluster, controller_id, req_msg
    );
    // prove that deletion will not affect coherence of needed pods
    let req = req_msg.content.get_get_then_delete_request();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    assert(local_state_is_coherent_with_etcd(vsts, next_local_state)(s_prime)) by {
        // 1.a. all needed pods in etcd are captured in next_local_state.needed
        assert forall |ord: nat| #![trigger next_local_state.needed[ord as int]] {
            &&& ord < next_local_state.needed.len()
            &&& next_local_state.needed[ord as int] is Some || ord < next_local_state.needed_index
        } implies {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s_prime.resources()[key];
            &&& s_prime.resources().contains_key(key)
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
            // TODO: cover pod updates
        } by {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            if !s_prime.resources().contains_key(key) {
                if req.key() == key {
                    get_ordinal_eq_pod_name(vsts.metadata.name->0, ord, key.name);
                    get_ordinal_eq_pod_name(vsts.metadata.name->0, (next_local_state.needed_index - 1) as nat, key.name);
                    assert(false);
                } else {
                    assert(!s.resources().contains_key(key));
                    assert(false);
                }
            }
        }
    }
}

pub proof fn lemma_from_after_delete_condemned_step_to_delete_outdated_step(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteCondemned])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_then_delete_condemned_pod_resp_in_flight_and_condemned_pod_is_deleted(vsts, controller_id)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step_or![DeleteOutdated, DeleteCondemned])(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

pub proof fn lemma_from_delete_outdated_step_to_after_delete_outdated_step(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, None, Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![DeleteOutdated])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    no_pending_req_in_cluster(vsts, controller_id)(s),
ensures
    at_vsts_step(vsts, controller_id, at_step_or![AfterDeleteOutdated, Done])(s_prime),
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    lift_local(controller_id, vsts, at_step![AfterDeleteOutdated])(s_prime) ==>
        pending_get_then_delete_outdated_pod_req_in_flight(vsts, controller_id)(s_prime),
    lift_local(controller_id, vsts, at_step![Done])(s_prime) ==>
        no_pending_req_in_cluster(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let triggering_cr = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr).unwrap();
    let outdated_pods = local_state.needed.filter(outdated_pod_filter(triggering_cr));
    assert(next_local_state == handle_delete_outdated(triggering_cr, None, local_state).0);
    assert forall |pod_or_none: Option<PodView>| #[trigger] outdated_pods.contains(pod_or_none)
        && pod_or_none is Some implies pod_or_none->0.metadata.name is Some by {
        seq_filter_contains_implies_seq_contains(local_state.needed, outdated_pod_filter(triggering_cr), pod_or_none);
    }
    if let Some(pod) = get_largest_unmatched_pods(triggering_cr, local_state.needed) {
        assert(outdated_pods.contains(Some(pod))); // trigger
        assert(get_largest_unmatched_pods(triggering_cr, next_local_state.needed) ==
            get_largest_unmatched_pods(vsts, next_local_state.needed)) by {
            same_filter_implies_same_result(next_local_state.needed, outdated_pod_filter(triggering_cr), outdated_pod_filter(vsts));
        }
    }
}

pub proof fn lemma_from_after_send_get_then_delete_outdated_pod_req_to_receive_get_then_delete_outdated_pod_resp(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteOutdated])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_then_delete_outdated_pod_req_in_flight(vsts, controller_id)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteOutdated])(s_prime),
    pending_get_then_delete_outdated_pod_resp_in_flight_and_outdated_pod_is_deleted(vsts, controller_id)(s_prime),
{
    lemma_get_then_delete_pod_request_returns_ok_or_not_found_err(
        s, s_prime, vsts, cluster, controller_id, req_msg_or_none(s, vsts.object_ref(), controller_id)->0
    );
    VStatefulSetReconcileState::marshal_preserves_integrity();
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
    let victim_pod = get_largest_unmatched_pods(vsts, local_state.needed)->0;
    let victim_ord = get_ordinal(vsts.metadata.name->0, victim_pod.metadata.name->0)->0;
    let req = req_msg_or_none(s, vsts.object_ref(), controller_id)->0.content.get_get_then_delete_request();
    // prove that deletion will not affect coherence of other needed pods
    assert(local_state_is_coherent_with_etcd(vsts, next_local_state)(s_prime)) by {
        assert forall |ord: nat| #![trigger next_local_state.needed[ord as int]] {
            &&& ord < next_local_state.needed.len()
            &&& next_local_state.needed[ord as int] is Some || ord < next_local_state.needed_index
            &&& ord != victim_ord
        } implies {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            let obj = s_prime.resources()[key];
            &&& s_prime.resources().contains_key(key)
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        } by {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: pod_name(vsts.metadata.name->0, ord),
                namespace: vsts.metadata.namespace->0
            };
            if !s_prime.resources().contains_key(key) && req.key() == key {
                get_ordinal_eq_pod_name(vsts.metadata.name->0, ord, key.name);
                get_ordinal_eq_pod_name(vsts.metadata.name->0, victim_ord, key.name);
                assert(false);
            }
        }
    }
}

pub proof fn lemma_from_after_delete_outdated_step_to_done_step(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, resp_msg_or_none(s, vsts.object_ref(), controller_id), Some(vsts.object_ref())))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterDeleteOutdated])(s),
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
    pending_get_then_delete_outdated_pod_resp_in_flight_and_outdated_pod_is_deleted(vsts, controller_id)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
    at_vsts_step(vsts, controller_id, at_step![Done])(s_prime),
    no_pending_req_in_cluster(vsts, controller_id)(s_prime),
{
    VStatefulSetReconcileState::marshal_preserves_integrity();
}

}