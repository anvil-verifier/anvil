use crate::kubernetes_api_objects::spec::{prelude::*, persistent_volume_claim::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::kubernetes_cluster::spec::api_server::{state_machine::*, types::InstalledTypes};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::{
    trusted::{spec_types::*, liveness_theorem::*},
    model::{reconciler::*, install::*},
    proof::predicate::*,
    proof::helper_lemmas::*
};
use crate::vstatefulset_controller::trusted::step::VStatefulSetReconcileStepView;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::{prelude::*, map_lib::*};
use crate::vstd_ext::{string_view::*, seq_lib::*, set_lib::*, map_lib::*};

verus! {

// VSTS Guarantee Condition (for other controllers)

pub open spec fn vsts_guarantee(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
            APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
            APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
            // No Update, UpdateStatus and Delete requests submitted
            _ => false,
        }
    }
}

// VSTS controller only creates Pods owned by itself
// and only creates PVC matching its PVC templates
pub open spec fn vsts_guarantee_create_req(req: CreateRequest) -> bool {
    let owner_references = req.obj.metadata.owner_references->0;
    &&& req.obj.metadata.name is Some
    &&& has_vsts_prefix(req.obj.metadata.name->0)
    &&& req.obj.kind == Kind::PodKind
        ==> exists |vsts: VStatefulSetView| req.obj.metadata.owner_references == Some(Seq::empty().push(#[trigger] vsts.controller_owner_ref()))
    &&& req.obj.kind == Kind::PersistentVolumeClaimKind
        ==> req.obj.metadata.owner_references is None
}

// VSTS controller Only updates Pod owned by itself and does not update PVC
pub open spec fn vsts_guarantee_get_then_update_req(req: GetThenUpdateRequest) -> bool {
    &&& req.obj.kind == Kind::PodKind
    &&& req.obj.metadata.name is Some
    &&& has_vsts_prefix(req.name)
    &&& exists |vsts: VStatefulSetView| {
        &&& req.owner_ref == #[trigger] vsts.controller_owner_ref()
        // do not change ownership
        &&& req.obj.metadata.owner_references == Some(Seq::empty().push(req.owner_ref))
    }
}

// VSTS controller Only deletes Pod owned by itself
pub open spec fn vsts_guarantee_get_then_delete_req(req: GetThenDeleteRequest) -> bool {
    &&& req.key.kind == Kind::PodKind
    &&& has_vsts_prefix(req.key.name)
    &&& exists |vsts: VStatefulSetView| req.owner_ref == #[trigger] vsts.controller_owner_ref()
}

// VSTS internal Rely-Guarantee condition (for itself and used in shield lemma)

pub open spec fn vsts_internal_guarantee_conditions(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |vsts: VStatefulSetView| #[trigger] no_interfering_request_between_vsts(controller_id, vsts)(s)
    }
}

pub open spec fn every_msg_from_vsts_controller_carries_vsts_key(
    controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            let content = msg.content;
            &&& s.in_flight().contains(msg)
            &&& msg.src.is_controller_id(controller_id)
        } ==> {
            msg.src->Controller_1.kind == VStatefulSetView::kind()
        }
    }
}

// all requests sent from one reconciliation do not interfere with other reconciliations on different CRs.
// TODO: we only use cr_key here, can be simplified
pub open spec fn no_interfering_request_between_vsts(controller_id: int, vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src == HostId::Controller(controller_id, vsts.object_ref())
        } ==> match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => vsts_internal_guarantee_create_req(req, vsts),
            APIRequest::GetThenDeleteRequest(req) => vsts_internal_guarantee_get_then_delete_req(req, vsts),
            APIRequest::GetThenUpdateRequest(req) => vsts_internal_guarantee_get_then_update_req(req, vsts),
            // VSTS controller will not issue DeleteRequest, UpdateRequest and UpdateStatusRequest
            _ => false
        }
    }
}

// VSTS controller only creates Pods and PVCs bound to the specific vsts instance
pub open spec fn vsts_internal_guarantee_create_req(req: CreateRequest, vsts: VStatefulSetView) -> bool {
    &&& req.namespace == vsts.metadata.namespace->0
    &&& req.obj.metadata.name is Some
    &&& req.obj.metadata.generate_name is None
    &&& req.obj.metadata.finalizers is None
    &&& req.obj.kind == Kind::PodKind ==> {
        &&& exists |owner_reference: OwnerReferenceView| {
            &&& req.obj.metadata.owner_references == Some(Seq::empty().push(owner_reference))
            &&& #[trigger] owner_reference_eq_without_uid(owner_reference, vsts.controller_owner_ref())
        }
        &&& pod_name_match(req.key().name, vsts.metadata.name->0)
    }
    &&& req.obj.kind == Kind::PersistentVolumeClaimKind ==> {
        &&& req.obj.metadata.owner_references is None
        &&& pvc_name_match(req.obj.metadata.name->0, vsts.metadata.name->0)
    }
}

// VSTS controller only deletes Pods bound to the specific vsts instance
pub open spec fn vsts_internal_guarantee_get_then_delete_req(req: GetThenDeleteRequest, vsts: VStatefulSetView) -> bool {
    &&& req.key().namespace == vsts.metadata.namespace->0
    &&& req.key().kind == Kind::PodKind
    &&& pod_name_match(req.key().name, vsts.metadata.name->0)
    &&& owner_reference_eq_without_uid(req.owner_ref, vsts.controller_owner_ref())
}

// VSTS controller only updates Pods bound to the specific vsts instance
pub open spec fn vsts_internal_guarantee_get_then_update_req(req: GetThenUpdateRequest, vsts: VStatefulSetView) -> bool {
    &&& req.obj.metadata.name == Some(req.name)
    &&& req.obj.metadata.namespace == Some(req.namespace)
    &&& req.obj.kind == Kind::PodKind
    &&& req.namespace == vsts.metadata.namespace->0
    &&& pod_name_match(req.name, vsts.metadata.name->0)
    &&& req.obj.metadata.owner_references == Some(Seq::empty().push(req.owner_ref))
    &&& owner_reference_eq_without_uid(req.owner_ref, vsts.controller_owner_ref())
    &&& req.obj.metadata.deletion_timestamp is None
    &&& req.obj.metadata.finalizers is None
}
// similar to local_pods_and_pvcs_are_bound_to_vsts
// helper invariant to prove both (external) guarantee conditions and internal guarantee conditions

// HINT: because we will prove it as an invariant, we need to pass key to local_pods_and_pvcs_are_bound_to_vsts_with_key
// before the reconciliation starts, !s.ongoing_reconciles(controller_id).contains_key(k) and this proof will be trivial
// during reconciliation, controller obtains vsts from s.ongoing_reconciles(controller_id)[k].triggering_cr
pub open spec fn local_pods_and_pvcs_are_bound_to_vsts(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |k: ObjectRef| #[trigger] s.ongoing_reconciles(controller_id).contains_key(k) && k.kind == VStatefulSetView::kind()
            ==> local_pods_and_pvcs_are_bound_to_vsts_with_key(controller_id, k, s)
    }
}

pub open spec fn local_pods_and_pvcs_are_bound_to_vsts_with_key_in_local_state(cr_key: ObjectRef, local_state: VStatefulSetReconcileState) -> bool {
    let pvcs = local_state.pvcs;
    let needed_pods = local_state.needed;
    let condemned_pods = local_state.condemned;
    &&& forall |i| #![trigger needed_pods[i]] 0 <= i < needed_pods.len() && needed_pods[i] is Some ==> {
        let pod = needed_pods[i]->0;
        &&& pod.metadata.name is Some
        &&& pod_name_match(pod.metadata.name->0, cr_key.name)
        &&& pod.metadata.namespace == Some(cr_key.namespace)
    }
    &&& forall |i| #![trigger condemned_pods[i]] 0 <= i < condemned_pods.len() ==> {
        let pod = condemned_pods[i];
        &&& pod.metadata.name is Some
        &&& pod_name_match(pod.metadata.name->0, cr_key.name)
        &&& pod.metadata.namespace == Some(cr_key.namespace)
    }
    &&& forall |i| #![trigger pvcs[i]] 0 <= i < pvcs.len() ==> {
        let pvc = pvcs[i];
        &&& pvc.metadata.name is Some
        &&& pvc_name_match(pvc.metadata.name->0, cr_key.name)
        &&& pvc.metadata.generate_name is None
        &&& pvc.metadata.namespace == Some(cr_key.namespace)
        &&& pvc.metadata.owner_references is None
        &&& pvc.metadata.finalizers is None
    }
}

pub open spec fn local_pods_and_pvcs_are_bound_to_vsts_with_key(controller_id: int, cr_key: ObjectRef, s: ClusterState) -> bool {
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0;
    &&& local_pods_and_pvcs_are_bound_to_vsts_with_key_in_local_state(cr_key, local_state)
    &&& local_state.reconcile_step == VStatefulSetReconcileStepView::AfterListPod ==> {
        let req_msg = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
        &&& s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg is Some
        &&& req_msg.dst is APIServer
        &&& req_msg.content.is_list_request()
        &&& req_msg.content.get_list_request() == ListRequest {
            kind: Kind::PodKind,
            namespace: cr_key.namespace,
        }
        &&& forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg is Some
            &&& msg.src is APIServer
            &&& resp_msg_matches_req_msg(msg, req_msg)
            &&& is_ok_resp(msg.content->APIResponse_0)
        } ==> {
            let resp_objs = msg.content.get_list_response().res.unwrap();
            &&& forall |i| #![trigger resp_objs[i]] 0 <= i < resp_objs.len()
                ==> resp_objs[i].metadata.namespace == Some(cr_key.namespace)
        }
    }
}

// similar to lemma_vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd_with_key_preserves_from_s_to_s_prime
#[verifier(spinoff_prover)]
#[verifier(rlimit(200))]
pub proof fn lemma_local_pods_and_pvcs_are_bound_to_vsts_with_key_preserves_from_s_to_s_prime(
    cluster: Cluster, controller_id: int, cr_key: ObjectRef, s: ClusterState, s_prime: ClusterState
)
requires
    cluster.next()(s, s_prime),
    Cluster::there_is_the_controller_state(controller_id)(s),
    Cluster::every_in_flight_msg_has_unique_id()(s),
    Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s),
    Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s),
    Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    cluster.each_builtin_object_in_etcd_is_well_formed()(s),
    cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s),
    cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
    Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
    Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id)(s),
    Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)(s),
    Cluster::etcd_is_finite()(s),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    local_pods_and_pvcs_are_bound_to_vsts_with_key(controller_id, cr_key, s),
    s.ongoing_reconciles(controller_id).contains_key(cr_key),
    s_prime.ongoing_reconciles(controller_id).contains_key(cr_key),
    cr_key.kind == VStatefulSetView::kind(),
ensures
    local_pods_and_pvcs_are_bound_to_vsts_with_key(controller_id, cr_key, s_prime),
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0;
    let next_local_state = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0;
    let vsts = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr)->Ok_0;
    let req_msg = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
    match step {
        Step::APIServerStep(req_msg_opt) => {
            let new_msgs = s_prime.in_flight().sub(s.in_flight());
            assert(next_local_state == local_state);
            assert(local_pods_and_pvcs_are_bound_to_vsts_with_key_in_local_state(cr_key, next_local_state));
            if local_state.reconcile_step == VStatefulSetReconcileStepView::AfterListPod {
                assert(s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg == Some(req_msg));
                assert forall |msg| {
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.src is APIServer
                    &&& resp_msg_matches_req_msg(msg, req_msg)
                    &&& is_ok_resp(msg.content->APIResponse_0)
                } implies {
                    let resp_objs = msg.content.get_list_response().res.unwrap();
                    &&& forall |i| #![trigger resp_objs[i]] 0 <= i < resp_objs.len()
                        ==> resp_objs[i].metadata.namespace == Some(cr_key.namespace)
                } by {
                    if new_msgs.contains(msg) {
                        if req_msg_opt == Some(req_msg) {
                            let resp_objs = msg.content.get_list_response().res.unwrap();
                            assert forall |i| #![trigger resp_objs[i]] 0 <= i < resp_objs.len()
                                implies resp_objs[i].metadata.namespace == Some(cr_key.namespace) by {
                                let selector = |o: DynamicObjectView| {
                                    &&& o.object_ref().namespace == req_msg.content.get_list_request().namespace
                                    &&& o.object_ref().kind == req_msg.content.get_list_request().kind
                                };
                                let selected_elements = s.resources().values().filter(selector);
                                lemma_values_finite(s.resources());
                                element_in_seq_exists_in_original_finite_set(selected_elements, resp_objs[i]);
                                lemma_filter_set(s.resources().values(), selector);
                            }
                        } else {
                            assert(s.in_flight().contains(req_msg_opt->0)); // trigger
                        }
                    } else {
                        assert(s.in_flight().contains(msg)); // trigger
                    }
                }
            }
            assert(local_pods_and_pvcs_are_bound_to_vsts_with_key(controller_id, cr_key, s_prime));
        },
        Step::ControllerStep((id, resp_msg_opt, cr_key_opt)) => {
            let resp_msg = resp_msg_opt->0;
            if cr_key_opt == Some(cr_key) {
                VStatefulSetReconcileState::marshal_preserves_integrity();
                let needed_index = if local_state.reconcile_step == VStatefulSetReconcileStepView::AfterListPod {
                    0
                } else {
                    local_state.needed_index
                };
                let new_pvcs = make_pvcs(vsts, needed_index);
                assert(new_pvcs.len() == pvc_cnt(vsts));
                if next_local_state.pvcs != local_state.pvcs && next_local_state.pvcs.len() > 0 {
                    assert(next_local_state.pvcs == new_pvcs);
                    assert(vsts.state_validation());
                    assert forall |i| #![trigger new_pvcs[i]] 0 <= i < new_pvcs.len() implies {
                        &&& new_pvcs[i].metadata.name is Some
                        &&& pvc_name_match(new_pvcs[i].metadata.name->0, cr_key.name)
                        &&& new_pvcs[i].metadata.generate_name is None
                        &&& new_pvcs[i].metadata.namespace == Some(cr_key.namespace)
                        &&& new_pvcs[i].metadata.owner_references is None
                        &&& new_pvcs[i].metadata.finalizers is None
                    } by {
                        let pvc = new_pvcs[i];
                        assert(pvc == make_pvc(vsts, needed_index, i));
                        // pre of pvc_name_with_vsts_implies_pvc_name_match_vsts
                        assert((|i: (nat, nat)| pvc.metadata.name->0 == pvc_name(vsts.spec.volume_claim_templates->0[i.0 as int].metadata.name->0, vsts.metadata.name->0, i.1)
                            && dash_free(vsts.spec.volume_claim_templates->0[i.0 as int].metadata.name->0))((i as nat, needed_index as nat)));
                        pvc_name_with_vsts_implies_pvc_name_match_vsts(pvc.metadata.name->0, vsts);
                        assert(pvc_name_match(pvc.metadata.name->0, cr_key.name));
                    }
                }
                if local_state.reconcile_step == VStatefulSetReconcileStepView::Init {
                    assert(next_local_state.needed == local_state.needed);
                    assert(next_local_state.condemned == local_state.condemned);
                    assert(next_local_state.pvcs == local_state.pvcs);
                    assert(local_pods_and_pvcs_are_bound_to_vsts_with_key_in_local_state(cr_key, next_local_state));
                    if next_local_state.reconcile_step == VStatefulSetReconcileStepView::AfterListPod {
                        assert(s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg is Some);
                        let req_msg = s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                        assert(req_msg.dst is APIServer);
                        assert(req_msg.content.is_list_request());
                        assert(req_msg.content.get_list_request() == ListRequest {
                            kind: Kind::PodKind,
                            namespace: cr_key.namespace,
                        });
                        assert(forall |msg| {
                            &&& #[trigger] s_prime.in_flight().contains(msg)
                            &&& msg.src is APIServer
                            &&& resp_msg_matches_req_msg(msg, req_msg)
                        } ==> s.in_flight().contains(msg));
                    }
                } else if local_state.reconcile_step == VStatefulSetReconcileStepView::AfterListPod
                    && resp_msg_opt is Some && is_ok_resp(resp_msg.content->APIResponse_0) {
                    assume(resp_msg.src is APIServer); // FIXME
                    assume(resp_msg_matches_req_msg(resp_msg, req_msg));
                    // similar to lemma_from_list_resp_to_next_state but simplified
                    let objs = resp_msg.content.get_list_response().res.unwrap();
                    if let Some(pods) = objects_to_pods(objs) {
                        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                            objs,
                            |o: DynamicObjectView| PodView::unmarshal(o).is_err()
                        );
                        assert forall |i| 0 <= i < objs.len() implies PodView::unmarshal(#[trigger] objs[i]) is Ok by {
                            assert(objs.contains(objs[i]));
                        }
                        let filtered_pods = pods.filter(pod_filter(vsts));
                        assert forall |pod: PodView| #[trigger] filtered_pods.contains(pod) implies {
                            &&& pod.metadata.name is Some
                            &&& pod_name_match(pod.metadata.name->0, cr_key.name)
                            &&& pod.metadata.namespace == Some(vsts.metadata.namespace->0)
                        } by {
                            PodView::marshal_preserves_metadata();
                            seq_filter_contains_implies_seq_contains(pods, pod_filter(vsts), pod);
                            let i = choose |i: int| 0 <= i < pods.len() && pods[i as int] == pod;
                            assert(PodView::unmarshal(objs[i as int]) is Ok);
                            assert(pod.metadata.namespace == objs[i as int].metadata.namespace);
                            assert(objs[i as int].metadata.namespace == Some(cr_key.namespace));
                            let ord = get_ordinal(cr_key.name, pod.metadata.name->0)->0;
                            get_ordinal_eq_pod_name(cr_key.name, ord, pod.metadata.name->0);
                            assert(pod_name_match(pod.metadata.name->0, cr_key.name));
                        }
                        let (needed, condemned) = partition_pods(vsts.metadata.name->0, replicas(vsts), filtered_pods);
                        assert forall |ord: nat| #![trigger needed[ord as int]] ord < needed.len() && needed[ord as int] is Some implies {
                            let pod = needed[ord as int]->0;
                            &&& pod.metadata.name is Some
                            &&& pod_name_match(pod.metadata.name->0, cr_key.name)
                            &&& pod.metadata.namespace == Some(vsts.metadata.namespace->0)
                        } by {
                            seq_filter_contains_implies_seq_contains(filtered_pods, pod_has_ord(cr_key.name, ord), needed[ord as int]->0);
                        }
                        let condemned_ord_filter = |pod: PodView| get_ordinal(cr_key.name, pod.metadata.name->0) is Some && get_ordinal(cr_key.name, pod.metadata.name->0)->0 >= replicas(vsts);
                        assert(condemned.to_set() == filtered_pods.filter(condemned_ord_filter).to_set()) by {
                            let leq = |p1: PodView, p2: PodView| get_ordinal(cr_key.name, p1.metadata.name->0)->0 >= get_ordinal(cr_key.name, p2.metadata.name->0)->0;
                            assert(condemned == filtered_pods.filter(condemned_ord_filter).sort_by(leq));
                            lemma_sort_by_does_not_add_or_delete_elements(filtered_pods.filter(condemned_ord_filter), leq);
                        }
                        assert forall |i: nat| #![trigger condemned[i as int]] i < condemned.len() implies {
                            let pod = condemned[i as int];
                            &&& pod.metadata.name is Some
                            &&& pod_name_match(pod.metadata.name->0, cr_key.name)
                            &&& pod.metadata.namespace == Some(vsts.metadata.namespace->0)
                        } by {
                            let condemned_pod = condemned[i as int];
                            assert(condemned.contains(condemned_pod));
                            assert(filtered_pods.filter(condemned_ord_filter).contains(condemned_pod)) by {
                                assert(condemned.to_set().contains(condemned_pod));
                                assert(filtered_pods.filter(condemned_ord_filter).contains(condemned_pod));
                            }
                            seq_filter_contains_implies_seq_contains(filtered_pods, condemned_ord_filter, condemned_pod);
                        }
                    }
                }
                assert(forall |msg| {
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.src is APIServer
                    &&& resp_msg_matches_req_msg(msg, req_msg)
                } ==> s.in_flight().contains(msg));
            } else {
                if local_state.reconcile_step == VStatefulSetReconcileStepView::AfterListPod {
                    assert(forall |msg| {
                        &&& #[trigger] s_prime.in_flight().contains(msg)
                        &&& msg.src is APIServer
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                    } ==> s.in_flight().contains(msg));
                }
            }
        },
        _ => {
            if local_state.reconcile_step == VStatefulSetReconcileStepView::AfterListPod {
                assert(forall |msg| {
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.src is APIServer
                    &&& resp_msg_matches_req_msg(msg, req_msg)
                    &&& is_ok_resp(msg.content->APIResponse_0)
                } ==> s.in_flight().contains(msg));
            }
        }
    }
}

pub proof fn lemma_always_local_pods_and_pvcs_are_bound_to_vsts(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures spec.entails(always(lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id)))),
{
    let invariant = local_pods_and_pvcs_are_bound_to_vsts(controller_id);

    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_builtin_object_in_etcd_is_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>(spec);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(spec, controller_id);
    cluster.lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(spec, controller_id);
    cluster.lemma_always_etcd_is_finite(spec);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id)(s)
        &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)(s)
        &&& Cluster::etcd_is_finite()(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)),
        lift_state(Cluster::etcd_is_finite())
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| {
            &&& invariant(s)
            &&& stronger_next(s, s_prime)
            &&& #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key) && key.kind == VStatefulSetView::kind()
        } implies local_pods_and_pvcs_are_bound_to_vsts_with_key(controller_id, key, s_prime) by {
            if s.ongoing_reconciles(controller_id).contains_key(key) {
                lemma_local_pods_and_pvcs_are_bound_to_vsts_with_key_preserves_from_s_to_s_prime(
                    cluster, controller_id, key, s, s_prime
                );
            } else { // RunScheduledReconcile
                VStatefulSetView::marshal_preserves_integrity();
                VStatefulSetReconcileState::marshal_preserves_integrity();
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}


pub proof fn lemma_guarantee_from_reconcile_state(
    msg: Message,
    state: VStatefulSetReconcileState,
    vsts: VStatefulSetView,
)
    requires
        msg.content is APIRequest,
        reconcile_core(vsts, None, state).1 is Some,
        reconcile_core(vsts, None, state).1->0 is KRequest,
        msg.content->APIRequest_0 == reconcile_core(vsts, None, state).1->0->KRequest_0,
        local_pods_and_pvcs_are_bound_to_vsts_with_key_in_local_state(vsts.object_ref(), state),
    ensures
        match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
            APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
            APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
            _ => false,
        }
{
    match state.reconcile_step {
        VStatefulSetReconcileStepView::CreateNeeded => {
            assert(msg.content.is_create_request());
            let req = msg.content.get_create_request();
            assert(has_vsts_prefix(req.obj.metadata.name->0));
            assert(req.obj.metadata.owner_references == Some(seq![vsts.controller_owner_ref()]));
            assert(has_vsts_prefix(req.obj.metadata.name->0));
        },
        VStatefulSetReconcileStepView::CreatePVC => {
            assert(msg.content.is_create_request());
            let req = msg.content.get_create_request();
            let pvc = state.pvcs[state.pvc_index as int];
            pvc_name_match_implies_has_vsts_prefix(pvc.metadata.name->0);
            assert(pvc.metadata.owner_references is None);
            assert(req.obj == pvc.marshal());
            assert(has_vsts_prefix(req.obj.metadata.name->0));
        },
        VStatefulSetReconcileStepView::UpdateNeeded => {
            assert(msg.content.is_get_then_update_request());
            let req = msg.content.get_get_then_update_request();
            let pod = state.needed[state.needed_index as int]->0;
            assert(req.name == pod.metadata.name->0);
            assert(has_vsts_prefix(req.name));
            assert(req.obj.metadata.owner_references == Some(seq![vsts.controller_owner_ref()]));
            assert(has_vsts_prefix(req.obj.metadata.name->0));
        },
        VStatefulSetReconcileStepView::DeleteCondemned => {
            assert(msg.content.is_get_then_delete_request());
            let req = msg.content.get_get_then_delete_request();
            let pod = state.condemned[state.condemned_index as int];
            assert(has_vsts_prefix(pod.metadata.name->0));
            assert(req.key.name == pod.metadata.name->0);
            assert(has_vsts_prefix(req.key.name));
            assert(req.owner_ref == vsts.controller_owner_ref());
        },
        VStatefulSetReconcileStepView::DeleteOutdated => {
            if let Some(pod) = get_largest_unmatched_pods(vsts, state.needed) {
                assert(msg.content.is_get_then_delete_request());
                let req = msg.content.get_get_then_delete_request();
                seq_filter_contains_implies_seq_contains(state.needed, outdated_pod_filter(vsts), Some(pod));
                assert(exists |i| 0 <= i < state.needed.len() && #[trigger] state.needed[i] == Some(pod));
                assert(has_vsts_prefix(pod.metadata.name->0));
                assert(req.key.name == pod.metadata.name->0);
                assert(has_vsts_prefix(req.key.name));
                assert(req.owner_ref == vsts.controller_owner_ref());
            }
        }
        VStatefulSetReconcileStepView::Init | VStatefulSetReconcileStepView::GetPVC => {},
        _ => {
            assert(reconcile_core(vsts, None, state).1 is None); // there is no message sent
        }
    }
}

pub proof fn guarantee_condition_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action (without weak fairness).
        spec.entails(always(lift_action(cluster.next()))),
        // The vsts type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        // The vsts controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    ensures
        spec.entails(always(lift_state(vsts_guarantee(controller_id))))
{
    let invariant = vsts_guarantee(controller_id);

    cluster.lemma_always_cr_states_are_unmarshallable::<VStatefulSetReconciler, VStatefulSetReconcileState, VStatefulSetView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    lemma_always_local_pods_and_pvcs_are_bound_to_vsts(spec, cluster, controller_id);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(spec, controller_id);

    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& local_pods_and_pvcs_are_bound_to_vsts(controller_id)(s)
        &&& local_pods_and_pvcs_are_bound_to_vsts(controller_id)(s_prime)
        &&& Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)(s)
    };

    always_to_always_later(spec, lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id)));

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id)),
        later(lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id))),
        lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id))
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |msg| {
            &&& invariant(s)
            &&& stronger_next(s, s_prime)
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } implies match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
            APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
            APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
            _ => false,
        } by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            let new_msgs = s_prime.in_flight().sub(s.in_flight());
            match step {
                Step::ControllerStep((id, _, cr_key_opt)) => {
                    let cr_key = cr_key_opt->0;
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                    if id == controller_id && new_msgs.contains(msg) {
                        let state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                        let vsts = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                        assert(msg.content->APIRequest_0 == reconcile_core(vsts, None, state).1->0->KRequest_0);
                        lemma_guarantee_from_reconcile_state(msg, state, vsts);
                    }
                },
                _ => {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}

pub proof fn internal_guarantee_condition_holds(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    ensures
        spec.entails(always(lift_state(no_interfering_request_between_vsts(controller_id, vsts))))
{
    let invariant = no_interfering_request_between_vsts(controller_id, vsts);

    cluster.lemma_always_cr_states_are_unmarshallable::<VStatefulSetReconciler, VStatefulSetReconcileState, VStatefulSetView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    lemma_always_local_pods_and_pvcs_are_bound_to_vsts(spec, cluster, controller_id);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(spec, controller_id);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>(spec);

    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& local_pods_and_pvcs_are_bound_to_vsts(controller_id)(s)
        &&& local_pods_and_pvcs_are_bound_to_vsts(controller_id)(s_prime)
        &&& Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s)
    };

    always_to_always_later(spec, lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id)));

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id)),
        later(lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id))),
        lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>())
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        VStatefulSetView::marshal_preserves_integrity();
        VStatefulSetReconcileState::marshal_preserves_integrity();
        PodView::marshal_preserves_integrity();
        PersistentVolumeClaimView::marshal_preserves_integrity();

        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(req_msg_opt) => {
                let req_msg = req_msg_opt.unwrap();

                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src == HostId::Controller(controller_id, vsts.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true,
                    APIRequest::CreateRequest(req) => vsts_internal_guarantee_create_req(req, vsts),
                    APIRequest::GetThenDeleteRequest(req) => vsts_internal_guarantee_get_then_delete_req(req, vsts),
                    APIRequest::GetThenUpdateRequest(req) => vsts_internal_guarantee_get_then_update_req(req, vsts),
                    _ => false,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
            Step::ControllerStep((id, resp_msg_opt, cr_key_opt)) => {
                let cr_key = cr_key_opt->0;
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src == HostId::Controller(controller_id, vsts.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true,
                    APIRequest::CreateRequest(req) => vsts_internal_guarantee_create_req(req, vsts),
                    APIRequest::GetThenDeleteRequest(req) => vsts_internal_guarantee_get_then_delete_req(req, vsts),
                    APIRequest::GetThenUpdateRequest(req) => vsts_internal_guarantee_get_then_update_req(req, vsts),
                    _ => false,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.

                    if id == controller_id && cr_key == vsts.object_ref() {
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());
                        if new_msgs.contains(msg) {
                            let triggering_vsts = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                            let state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            assert(reconcile_core(triggering_vsts, None, state).1 is Some);
                            assert(reconcile_core(triggering_vsts, None, state).1->0 is KRequest);
                            assert(msg.content->APIRequest_0 == reconcile_core(triggering_vsts, None, state).1->0->KRequest_0);

                            // Match on the reconcile step to handle each case
                            match state.reconcile_step {
                                VStatefulSetReconcileStepView::CreatePVC => {
                                    assert(msg.content.is_create_request());
                                    let req = msg.content.get_create_request();
                                    let pvc = state.pvcs[state.pvc_index as int];
                                    assert(req.obj.metadata == pvc.metadata);
                                    assert(pvc_name_match(req.obj.metadata.name->0, vsts.metadata.name->0));
                                    assert(req.obj.metadata.owner_references is None);
                                    assert(req.obj.metadata.finalizers is None);
                                    assert(req.obj.metadata.generate_name is None);
                                    assert(vsts_internal_guarantee_create_req(req, vsts));
                                },
                                VStatefulSetReconcileStepView::CreateNeeded => {
                                    assert(msg.content.is_create_request());
                                    let req = msg.content.get_create_request();
                                    assert(req.key().name == pod_name(vsts.metadata.name->0, state.needed_index));
                                    assert(req.obj.metadata.generate_name is None); 
                                    let owner_ref = req.obj.metadata.owner_references->0[0];
                                    assert(owner_reference_eq_without_uid(owner_ref, vsts.controller_owner_ref()));
                                    assert(vsts_internal_guarantee_create_req(req, vsts));
                                },
                                VStatefulSetReconcileStepView::UpdateNeeded => {
                                    assert(msg.content.is_get_then_update_request());
                                    let req = msg.content.get_get_then_update_request();
                                    let pod = state.needed[state.needed_index as int]->0;
                                    assert(get_ordinal(vsts.metadata.name->0, pod.metadata.name->0) is Some);
                                    let ord = get_ordinal(vsts.metadata.name->0, pod.metadata.name->0)->0;
                                    assert(req.name == pod_name(vsts.metadata.name->0, ord));
                                    let controller_owner_references = req.obj.metadata.owner_references->0;
                                    let owner_ref = controller_owner_references[0];
                                    assert(owner_reference_eq_without_uid(owner_ref, vsts.controller_owner_ref()));
                                    assert(vsts_internal_guarantee_get_then_update_req(req, vsts));
                                },
                                VStatefulSetReconcileStepView::DeleteCondemned => {
                                    assert(msg.content.is_get_then_delete_request());
                                    let req = msg.content.get_get_then_delete_request();
                                    let condemned_pod = state.condemned[state.condemned_index as int];
                                    assert(get_ordinal(vsts.metadata.name->0, condemned_pod.metadata.name->0) is Some);
                                    let ord = get_ordinal(vsts.metadata.name->0, condemned_pod.metadata.name->0)->0;
                                    assert(req.key().name == pod_name(vsts.metadata.name->0, ord));
                                    assert(vsts_internal_guarantee_get_then_delete_req(req, vsts));
                                },
                                VStatefulSetReconcileStepView::DeleteOutdated => {
                                    assert(msg.content.is_get_then_delete_request());
                                    let req = msg.content.get_get_then_delete_request();
                                    if let Some(pod) = get_largest_unmatched_pods(triggering_vsts, state.needed) {
                                        seq_filter_contains_implies_seq_contains(state.needed, outdated_pod_filter(triggering_vsts), Some(pod));
                                        // trigger for local_pods_and_pvcs_are_bound_to_vsts_with_key_in_local_state
                                        assert(exists |i: int| 0 <= i < state.needed.len() && #[trigger] state.needed[i] == Some(pod));
                                        assert(get_ordinal(vsts.metadata.name->0, pod.metadata.name->0) is Some);
                                        let ord = get_ordinal(vsts.metadata.name->0, pod.metadata.name->0)->0;
                                        get_ordinal_eq_pod_name(vsts.metadata.name->0, ord, pod.metadata.name->0);
                                        assert(req.key().name == pod.metadata.name->0);
                                    } else {
                                        assert(false); // should not have any new message
                                    }
                                    assert(vsts_internal_guarantee_get_then_delete_req(req, vsts));
                                },
                                _ => {
                                    // other cases are trivial
                                }
                            }
                        }
                    }
                }
            }
            _ => {
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src == HostId::Controller(controller_id, vsts.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true,
                    APIRequest::CreateRequest(req) => vsts_internal_guarantee_create_req(req, vsts),
                    APIRequest::GetThenDeleteRequest(req) => vsts_internal_guarantee_get_then_delete_req(req, vsts),
                    APIRequest::GetThenUpdateRequest(req) => vsts_internal_guarantee_get_then_update_req(req, vsts),
                    _ => false,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}

pub proof fn internal_guarantee_condition_holds_on_all_vsts(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    ensures
        spec.entails(always(lift_state(vsts_internal_guarantee_conditions(controller_id))))
{
    let guarantee = lift_state(vsts_internal_guarantee_conditions(controller_id));
    let target = always(guarantee);
    let no_interfering_request = |vsts: VStatefulSetView| lift_state(no_interfering_request_between_vsts(controller_id, vsts));
    assert forall |ex: Execution<ClusterState>| spec.satisfied_by(ex) implies target.satisfied_by(ex) by {
        assert forall |vsts: VStatefulSetView| #![trigger no_interfering_request(vsts)] always(no_interfering_request(vsts)).satisfied_by(ex) by {
            internal_guarantee_condition_holds(spec, cluster, controller_id, vsts);
            assert(spec.entails(always(no_interfering_request(vsts))));
            assert(valid(spec.implies(always(no_interfering_request(vsts)))));
            assert(spec.implies(always(no_interfering_request(vsts))).satisfied_by(ex));
        }
        assert(forall |vsts: VStatefulSetView, i: nat| #[trigger] no_interfering_request(vsts).satisfied_by(ex.suffix(i)));
        assert forall |i: nat| #[trigger] guarantee.satisfied_by(ex.suffix(i)) by {
            assert forall |vsts: VStatefulSetView| #[trigger] no_interfering_request_between_vsts(controller_id, vsts)(ex.suffix(i).head()) by {
                assert(no_interfering_request(vsts).satisfied_by(ex.suffix(i)));
            }
        };
    }
}

}