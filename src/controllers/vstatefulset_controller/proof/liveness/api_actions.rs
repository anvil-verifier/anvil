use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::{spec::prelude::*, error::APIError::*};
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::{types::*, state_machine::*},
    cluster::*, 
    message::*
};
use crate::vstatefulset_controller::{
    trusted::{spec_types::*, step::*, liveness_theorem::*},
    model::{install::*, reconciler::*},
    proof::{predicate::*, liveness::state_predicates::*, shield_lemma, helper_invariants},
};
use crate::vstatefulset_controller::trusted::step::VStatefulSetReconcileStepView::*;
use crate::reconciler::spec::io::*;
use vstd::{seq_lib::*, prelude::*, map_lib::*, set::*};
use crate::vstd_ext::{seq_lib::*, set_lib::*, map_lib::*, string_view::*};

verus! {

pub proof fn lemma_list_pod_request_returns_ok_with_objs_matching_vsts(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    pending_list_pod_req_in_flight(vsts, controller_id)(s),
    req_msg_is(req_msg, vsts.object_ref(), controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
ensures
    pending_list_pod_resp_in_flight(vsts, controller_id)(s_prime),
{
    broadcast use group_seq_properties;
    PodView::marshal_preserves_integrity();
    let req = req_msg.content.get_list_request();
    let list_req_filter = |o: DynamicObjectView| {
        // changing the order of fields makes a difference
        &&& o.object_ref().namespace == vsts.metadata.namespace->0
        &&& o.object_ref().kind == Kind::PodKind
    }; 
    let resp_msg = handle_list_request_msg(req_msg, s.api_server).1;
    assert(s_prime.in_flight().contains(resp_msg));
    assert(s.resources() == s_prime.resources());
    assert(resp_msg_is_ok_list_resp_of_pods(vsts, resp_msg, s_prime)) by {
        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
        let owner_ref_filter = |obj: DynamicObjectView| obj.metadata.owner_references_contains(vsts.controller_owner_ref());
        let owned_objs = resp_objs.filter(owner_ref_filter);
        assert(resp_objs == s.resources().values().filter(list_req_filter).to_seq());
        lemma_values_finite(s.resources());
        assert(resp_objs.no_duplicates()) by {
            finite_set_to_seq_has_no_duplicates(s.resources().values().filter(list_req_filter));
        }
        assert forall |o| #[trigger] resp_objs.contains(o) implies {
            &&& o.kind == Kind::PodKind
            &&& PodView::unmarshal(o) is Ok
            &&& s_prime.resources().contains_key(o.object_ref())
            &&& s_prime.resources()[o.object_ref()] == o
            &&& o.metadata.namespace is Some
            &&& o.metadata.namespace->0 == vsts.metadata.namespace->0
            &&& o.metadata.name is Some
        } by {
            assert(s.resources().values().filter(list_req_filter).contains(o)) by {
                finite_set_to_seq_contains_all_set_elements(s.resources().values().filter(list_req_filter));
            }
        }
        assert(objects_to_pods(resp_objs) is Some) by {
            seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                resp_objs, |obj: DynamicObjectView| PodView::unmarshal(obj) is Err
            );
        }
        assert(resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref()).no_duplicates()) by {
            assert forall|i, j| (0 <= i < resp_objs.len() && 0 <= j < resp_objs.len() && i != j)
                implies #[trigger] resp_objs[i].object_ref() != #[trigger] resp_objs[j].object_ref() by {
                if resp_objs[i].object_ref() == resp_objs[j].object_ref() {
                    assert(resp_objs.contains(resp_objs[i]));
                    assert(resp_objs.contains(resp_objs[j])); // trigger of s.resources()[o.object_ref()] == o
                    assert(resp_objs[i] == resp_objs[j]);
                }
            }
        }
        // s.res.v.f(list_req_filter).to_seq.f(owner_ref_filter).to_set.map(key) == s.res.v.f(valid_owned_object_filter).map(key)
        assert(owned_objs.to_set() == s_prime.resources().values().filter(valid_owned_object_filter(vsts))) by {
            // move to_set ahead and cancel to_seq
            assert(owned_objs.to_set() == s_prime.resources().values().filter(list_req_filter).filter(owner_ref_filter)) by {
                lemma_filter_to_set_eq_to_set_filter(resp_objs, owner_ref_filter);
                lemma_to_seq_to_set_equal(s_prime.resources().values().filter(list_req_filter));
            }
            // s.res.v.f(list_req_filter).f(owner_ref_filter).map(key) == s.res.v.f(valid_owned_object_filter).map(key)
            assert(forall |obj| #[trigger] s_prime.resources().values().contains(obj) ==>
                (list_req_filter(obj) && owner_ref_filter(obj) <==> valid_owned_object_filter(vsts)(obj)));
        }
        assert forall |obj: DynamicObjectView| #[trigger] owned_objs.contains(obj) implies {
            let key = obj.object_ref();
            let etcd_obj = s_prime.resources()[key];
            &&& s_prime.resources().contains_key(key)
            &&& weakly_eq(obj, etcd_obj)
        } by {
            assert(owned_objs.to_set().contains(obj));
            assert(s_prime.resources().values().contains(obj));
        }
    }
}

pub proof fn lemma_get_pvc_request_returns_ok_or_err_response(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    req_msg_is(req_msg, vsts.object_ref(), controller_id)(s),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    pending_get_pvc_req_in_flight(vsts, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
ensures
    pending_get_pvc_resp_in_flight(vsts, controller_id)(s_prime),
{
    let resp_msg = handle_get_request_msg(req_msg, s.api_server).1;
    assert(s_prime.in_flight().contains(resp_msg));
}

pub proof fn lemma_create_pvc_request_returns_ok_or_already_exists_err_response(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    req_msg_is(req_msg, vsts.object_ref(), controller_id)(s),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    pending_create_pvc_req_in_flight(vsts, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
ensures
    pending_create_pvc_resp_msg_in_flight_and_created_pvc_exists(vsts, controller_id)(s_prime),
{
    let resp_msg = handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).1;
    let req = req_msg.content.get_create_request();
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
    let (ord, i) = (local_state.needed_index, (local_state.pvc_index - 1) as nat);
    VStatefulSetReconcileState::marshal_preserves_integrity();
    assert(s_prime.in_flight().contains(resp_msg));
    let admission_chk_res = create_request_admission_check(cluster.installed_types, req, s.api_server);
    if admission_chk_res is None {
        let created_obj = DynamicObjectView {
            kind: Kind::PersistentVolumeClaimKind,
            metadata: ObjectMetaView {
                name: Some(pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, ord)),
                namespace: Some(req.namespace),
                resource_version: Some(s.api_server.resource_version_counter),
                uid: Some(s.api_server.uid_counter),
                deletion_timestamp: None,
                ..req.obj.metadata
            },
            spec: req.obj.spec,
            status: marshalled_default_status(Kind::PersistentVolumeClaimKind, cluster.installed_types), // Overwrite the status with the default one
        };
        assert(created_object_validity_check(created_obj, cluster.installed_types) is None) by {
            assert(metadata_validity_check(created_obj) is None);
            assert(object_validity_check(created_obj, cluster.installed_types) is None) by {
                PersistentVolumeClaimView::marshal_status_preserves_integrity();
                assert(PersistentVolumeClaimView::unmarshal_status(created_obj.status) is Ok);
                assert(PersistentVolumeClaimView::unmarshal_spec(created_obj.spec) is Ok);
            }
        }
    }
}

pub proof fn lemma_create_needed_pod_request_returns_ok_or_already_exists_err_response(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    req_msg_is(req_msg, vsts.object_ref(), controller_id)(s),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    pending_create_needed_pod_req_in_flight(vsts, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
ensures
    pending_create_needed_pod_resp_in_flight_and_created_pod_exists(vsts, controller_id)(s_prime),
{
    let resp_msg = handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).1;
    let req = req_msg.content.get_create_request();
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
    let ord = (local_state.needed_index - 1) as nat;
    VStatefulSetReconcileState::marshal_preserves_integrity();
    assert(s_prime.in_flight().contains(resp_msg));
    let admission_chk_res = create_request_admission_check(cluster.installed_types, req, s.api_server);
    if !s.resources().contains_key(req.key()) {
        assert(admission_chk_res is None);
        let created_obj = DynamicObjectView {
            kind: Kind::PodKind,
            metadata: ObjectMetaView {
                name: Some(pod_name(vsts.metadata.name->0, ord)),
                namespace: Some(req.namespace),
                resource_version: Some(s.api_server.resource_version_counter),
                uid: Some(s.api_server.uid_counter),
                deletion_timestamp: None,
                ..req.obj.metadata
            },
            spec: req.obj.spec,
            status: marshalled_default_status(Kind::PodKind, cluster.installed_types), // Overwrite the status with the default one
        };
        assert(created_object_validity_check(created_obj, cluster.installed_types) is None) by {
            PodView::marshal_status_preserves_integrity();
            assert(metadata_validity_check(created_obj) is None) by {
                assert(created_obj.metadata.owner_references == Some(seq![vsts.controller_owner_ref()]));
                assert(controller_owner_filter()(vsts.controller_owner_ref()));
            }
            assert(object_validity_check(created_obj, cluster.installed_types) is None) by {
                assert(PodView::unmarshal_status(created_obj.status) is Ok);
                assert(PodView::unmarshal_spec(created_obj.spec) is Ok);
            }
        }
        assert(vsts.spec.selector.matches(created_obj.metadata.labels.unwrap_or(Map::empty())));
        assert(s_prime.resources() == s.resources().insert(req.key(), created_obj));
    } else {
        assert(admission_chk_res->0 == ObjectAlreadyExists);
        assume(false); // TODO: prove it's impossible
    }
}

pub proof fn lemma_get_then_update_needed_pod_request_returns_ok_response(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    req_msg_is(req_msg, vsts.object_ref(), controller_id)(s),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    pending_get_then_update_needed_pod_req_in_flight(vsts, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
ensures
    pending_get_then_update_needed_pod_resp_in_flight(vsts, controller_id)(s_prime),
{
    let resp_msg = handle_get_then_update_request_msg(cluster.installed_types, req_msg, s.api_server).1;
    let req = req_msg.content.get_get_then_update_request();
    let key = req.key();
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
    let ord = (local_state.needed_index - 1) as nat;
    VStatefulSetReconcileState::marshal_preserves_integrity();
    PodView::marshal_status_preserves_integrity();
    assert(s_prime.in_flight().contains(resp_msg));
    assert(s.resources().contains_key(key));
    assert(resp_msg.content.get_get_then_update_response().res is Ok) by {
        assert(req.well_formed());
        let current_obj = s.resources()[key];
        assert(current_obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
        let new_obj = DynamicObjectView {
            metadata: ObjectMetaView {
                resource_version: current_obj.metadata.resource_version,
                uid: current_obj.metadata.uid,
                ..req.obj.metadata
            },
            ..req.obj
        };
        let update_req = UpdateRequest {
            name: req.name,
            namespace: req.namespace,
            obj: new_obj,
        };
        assert(handle_update_request(cluster.installed_types, update_req, s.api_server).1.res is Ok) by {
            assert(update_request_admission_check(cluster.installed_types, update_req, s.api_server) is None);
            assert(current_obj.metadata.deletion_timestamp is None);
            let updated_obj = updated_object(update_req, current_obj).with_resource_version(s.api_server.resource_version_counter);
            assert(updated_object_validity_check(updated_obj, current_obj, cluster.installed_types) is None) by {
                assert(metadata_validity_check(updated_obj) is None) by {
                    assert(updated_obj.metadata.owner_references == Some(seq![vsts.controller_owner_ref()]));
                    assert(controller_owner_filter()(vsts.controller_owner_ref()));
                }
            }
        }
    }
}

pub proof fn lemma_get_then_delete_pod_request_returns_ok_or_not_found_err(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message,
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    req_msg.src == HostId::Controller(controller_id, vsts.object_ref()),
    req_msg.dst == HostId::APIServer,
    req_msg.content.is_get_then_delete_request(),
    ({
        let req = req_msg.content.get_get_then_delete_request();
        let key = req.key();
        &&& req.owner_ref == vsts.controller_owner_ref()
        // trigger all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp
        &&& key.kind == Kind::PodKind
        &&& key.namespace == vsts.metadata.namespace->0
        &&& pod_name_match(key.name, vsts.metadata.name->0)
    }),
ensures
    s_prime.in_flight().contains(resp_msg),
    resp_msg_matches_req_msg(resp_msg, req_msg),
    resp_msg.content.is_get_then_delete_response(),
    resp_msg.content.get_get_then_delete_response().res is Err
        ==> resp_msg.content.get_get_then_delete_response().res->Err_0 == ObjectNotFound,
    ({ // no side effect
        let req = req_msg.content.get_get_then_delete_request();
        &&& forall |key: ObjectRef| key != req.key() ==> (s_prime.resources().contains_key(key) == s.resources().contains_key(key))
        &&& !s_prime.resources().contains_key(req.key())
    }),
{
    let resp_msg = handle_get_then_delete_request_msg(req_msg, s.api_server).1;
    assert(s_prime.in_flight().contains(resp_msg));
    let req = req_msg.content.get_get_then_delete_request();
    let key = req.key();
    if s.resources().contains_key(key) {
        let obj = s.resources()[key];
        assert(obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
        assert(resp_msg.content.get_get_then_delete_response().res is Ok);
        assert(!s_prime.resources().contains_key(key));
    } else {
        assert(resp_msg.content.get_get_then_delete_response().res is Err);
        assert(resp_msg.content.get_get_then_delete_response().res->Err_0 == ObjectNotFound);
    }
    return resp_msg;
}

// *** shield lemma is heavily abused below this line *** //
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s_prime),
    req_msg.src != HostId::Controller(controller_id, vsts.object_ref()),
    req_msg.dst == HostId::APIServer,
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
{
    // basically copy-pasting coherence pred and invoke non-interference lemma
    let state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
    let state_prime = VStatefulSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vsts.object_ref()].local_state)->Ok_0;
    assert(state == state_prime);
    assert(local_state_is_valid(vsts, state_prime));
    let vsts_key = vsts.object_ref();
    let pvc_cnt = if vsts.spec.volume_claim_templates is Some {
        vsts.spec.volume_claim_templates->0.len()
    } else {0};
    let needed_index_for_pvc = match state.reconcile_step {
        CreateNeeded | UpdateNeeded => (state.needed_index + 1) as nat,
        _ => state.needed_index,
    };
    let needed_index_considering_creation = match state.reconcile_step {
        AfterCreateNeeded => (state.needed_index - 1) as nat,
        _ => state.needed_index,
    };
    let condemned_index_considering_deletion = match state.reconcile_step {
        AfterDeleteCondemned => (state.condemned_index - 1) as nat,
        _ => state.condemned_index,
    };
    let outdated_pod = get_largest_unmatched_pods(vsts, state.needed);
    let outdated_pod_keys = state.needed.filter(outdated_pod_filter(vsts)).map_values(|pod_opt: Option<PodView>| pod_opt->0.object_ref());
    VStatefulSetReconcileState::marshal_preserves_integrity();
    assert forall |ord: nat| ord < state.needed.len() implies {
        let key = ObjectRef {
            kind: Kind::PodKind,
            name: #[trigger] pod_name(vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        &&& s.resources().contains_key(key) <==> s_prime.resources().contains_key(key)
        &&& weakly_eq(s.resources()[key], s_prime.resources()[key])
    } by {
        let key = ObjectRef {
            kind: Kind::PodKind,
            name: #[trigger] pod_name(vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        assert({
            &&& key.kind == Kind::PodKind
            &&& key.namespace == vsts.metadata.namespace->0
            &&& pod_name_match(key.name, vsts.metadata.name->0)
        });
        shield_lemma::lemma_no_interference_on_pods(s, s_prime, vsts, cluster, controller_id, req_msg);
    }
    assert forall |ord: nat| ord >= vsts.spec.replicas.unwrap_or(1) implies {
        let key = ObjectRef {
            kind: Kind::PodKind,
            name: #[trigger] pod_name(vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        s_prime.resources().contains_key(key)
            ==> exists |pod: PodView| #[trigger] state.condemned.contains(pod) && pod.object_ref() == key
    } by {
        let key = ObjectRef {
            kind: Kind::PodKind,
            name: #[trigger] pod_name(vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        if s_prime.resources().contains_key(key) {
            assert({
                &&& s_prime.resources().contains_key(key)
                &&& key.kind == Kind::PodKind
                &&& key.namespace == vsts.metadata.namespace->0
                &&& pod_name_match(key.name, vsts.metadata.name->0)
            });
            shield_lemma::lemma_no_interference_on_pods(s, s_prime, vsts, cluster, controller_id, req_msg);
        }
    }
    assert forall |i: nat| #![trigger state.condemned[i as int]] i < condemned_index_considering_deletion implies {
        let key = ObjectRef {
            kind: Kind::PodKind,
            name: state.condemned[i as int].metadata.name->0,
            namespace: vsts.metadata.namespace->0
        };
        &&& !s_prime.resources().contains_key(key)
    } by {
        let key = ObjectRef {
            kind: Kind::PodKind,
            name: state.condemned[i as int].metadata.name->0,
            namespace: vsts.metadata.namespace->0
        };
        if s_prime.resources().contains_key(key) {
            assert({
                &&& s_prime.resources().contains_key(key)
                &&& key.kind == Kind::PodKind
                &&& key.namespace == vsts.metadata.namespace->0
                &&& pod_name_match(key.name, vsts.metadata.name->0)
            });
            shield_lemma::lemma_no_interference_on_pods(s, s_prime, vsts, cluster, controller_id, req_msg);
            assert(false);
        }
    }
    assert(needed_index_for_pvc <= replicas(vsts));
    assert(vsts.state_validation()) by {
        let cr = VStatefulSetView::unmarshal(s.resources()[vsts.object_ref()])->Ok_0;
        assert(cr.spec == vsts.spec);
    }
    assert forall |ord: nat, i: nat| ord < needed_index_for_pvc && i < pvc_cnt implies {
        let key = ObjectRef {
            kind: PersistentVolumeClaimView::kind(),
            name: #[trigger] pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        &&& s_prime.resources().contains_key(key)
    } by {
        let key = ObjectRef {
            kind: PersistentVolumeClaimView::kind(),
            name: #[trigger] pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        assert({
            &&& s.resources().contains_key(key)
            &&& key.kind == Kind::PersistentVolumeClaimKind
            &&& key.namespace == vsts.metadata.namespace->0
            &&& pvc_name_match(key.name, vsts.metadata.name->0)
        }) by {
            VStatefulSetView::marshal_preserves_integrity();
            assert(s.resources().contains_key(vsts.object_ref()));
            let trigger = (vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, ord);
            assert(dash_free(trigger.0));
            assert(key.name == (|i: (StringView, nat)| pvc_name(i.0, vsts.metadata.name->0, i.1))(trigger));
        }
        shield_lemma::lemma_no_interference_on_pvcs(s, s_prime, vsts, cluster, controller_id, req_msg);
    }
    if locally_at_step_or!(state, GetPVC, AfterGetPVC, CreatePVC, AfterCreatePVC, SkipPVC) {
        let pvc_index_tmp = match state.reconcile_step {
            AfterCreatePVC => (state.pvc_index - 1) as nat,
            SkipPVC => (state.pvc_index + 1) as nat,
            _ => state.pvc_index,
        };
        assert(pvc_index_tmp <= pvc_cnt);
        assert forall |i: nat| i < pvc_index_tmp implies {
            let key = ObjectRef {
                kind: PersistentVolumeClaimView::kind(),
                name: #[trigger] pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, state.needed_index),
                namespace: vsts.metadata.namespace->0
            };
            &&& s_prime.resources().contains_key(key)
        } by {
            let key = ObjectRef {
                kind: PersistentVolumeClaimView::kind(),
                name: #[trigger] pvc_name(vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, vsts.metadata.name->0, state.needed_index),
                namespace: vsts.metadata.namespace->0
            };
            assert({
                &&& s.resources().contains_key(key)
                &&& key.kind == Kind::PersistentVolumeClaimKind
                &&& key.namespace == vsts.metadata.namespace->0
                &&& pvc_name_match(key.name, vsts.metadata.name->0)
            }) by {
                VStatefulSetView::marshal_preserves_integrity();
                assert(s.resources().contains_key(vsts.object_ref()));
                let trigger = (vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, state.needed_index);
                assert(dash_free(trigger.0));
                assert(key.name == (|i: (StringView, nat)| pvc_name(i.0, vsts.metadata.name->0, i.1))(trigger));
            }
            shield_lemma::lemma_no_interference_on_pvcs(s, s_prime, vsts, cluster, controller_id, req_msg);
        }
    }
    assert(outdated_obj_keys_in_etcd(s, vsts) == outdated_obj_keys_in_etcd(s_prime, vsts)) by {
        lemma_api_request_other_than_pending_req_msg_maintains_outdated_pods_in_etcd(s, s_prime, vsts, cluster, controller_id, req_msg);
    }
    if outdated_pod is Some && state.reconcile_step == AfterDeleteOutdated {
        let outdated_key = outdated_pod->0.object_ref();
        assert(s_prime.resources().contains_key(outdated_key) == s.resources().contains_key(outdated_key)) by {
            assert({
                &&& outdated_key.kind == Kind::PodKind
                &&& outdated_key.namespace == vsts.metadata.namespace->0
                &&& pod_name_match(outdated_key.name, vsts.metadata.name->0)
            }) by {
                seq_filter_contains_implies_seq_contains(
                    state.needed, outdated_pod_filter(vsts), outdated_pod,
                );
            }
            if s.resources().contains_key(outdated_key) {
                shield_lemma::lemma_no_interference_on_pods(s, s_prime, vsts, cluster, controller_id, req_msg);
            }
            if s_prime.resources().contains_key(outdated_key) {
                shield_lemma::lemma_no_interference_on_pods(s, s_prime, vsts, cluster, controller_id, req_msg);
            }
        }
    }
}

pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_outdated_pods_in_etcd(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s_prime),
    req_msg.src != HostId::Controller(controller_id, vsts.object_ref()),
    req_msg.dst == HostId::APIServer,
ensures
    outdated_obj_keys_in_etcd(s, vsts) == outdated_obj_keys_in_etcd(s_prime, vsts),
{
    assert forall |key: ObjectRef| #[trigger] s.resources().dom().filter(outdated_obj_key_filter(s, vsts)).contains(key)
        implies s_prime.resources().dom().filter(outdated_obj_key_filter(s_prime, vsts)).contains(key) by {
        assert(outdated_obj_key_filter(s, vsts)(key));
        assert({
            &&& s.resources().contains_key(key)
            &&& key.kind == Kind::PodKind
            &&& key.namespace == vsts.metadata.namespace->0
            &&& pod_name_match(key.name, vsts.metadata.name->0)
        });
        shield_lemma::lemma_no_interference_on_pods(s, s_prime, vsts, cluster, controller_id, req_msg);
    }
    assert forall |key: ObjectRef| #[trigger] s_prime.resources().dom().filter(outdated_obj_key_filter(s_prime, vsts)).contains(key)
        implies s.resources().dom().filter(outdated_obj_key_filter(s, vsts)).contains(key) by {
        assert(outdated_obj_key_filter(s_prime, vsts)(key));
        assert({
            &&& s_prime.resources().contains_key(key)
            &&& key.kind == Kind::PodKind
            &&& key.namespace == vsts.metadata.namespace->0
            &&& pod_name_match(key.name, vsts.metadata.name->0)
        });
        shield_lemma::lemma_no_interference_on_pods(s, s_prime, vsts, cluster, controller_id, req_msg);
    }
}

pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_current_state_matches(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s_prime),
    req_msg.src != HostId::Controller(controller_id, vsts.object_ref()),
    req_msg.dst == HostId::APIServer,
    current_state_matches(vsts)(s),
ensures
    current_state_matches(vsts)(s_prime),
{
    assert forall |ord: nat| ord < replicas(vsts) implies {
        let key = ObjectRef {
            kind: Kind::PodKind,
            name: #[trigger] pod_name(vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        &&& s_prime.resources().contains_key(key)
        &&& weakly_eq(s.resources()[key], s_prime.resources()[key])
    } by {
        let key = ObjectRef {
            kind: Kind::PodKind,
            name: #[trigger] pod_name(vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        assert({
            &&& s.resources().contains_key(key)
            &&& key.kind == Kind::PodKind
            &&& key.namespace == vsts.metadata.namespace->0
            &&& pod_name_match(key.name, vsts.metadata.name->0)
        });
        shield_lemma::lemma_no_interference_on_pods(s, s_prime, vsts, cluster, controller_id, req_msg);
    }
    assert forall |ord: nat| ord >= replicas(vsts) implies {
        let key = ObjectRef {
            kind: PodView::kind(),
            name: #[trigger] pod_name(vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        &&& !s_prime.resources().contains_key(key)
    } by {
        let key = ObjectRef {
            kind: PodView::kind(),
            name: #[trigger] pod_name(vsts.metadata.name->0, ord),
            namespace: vsts.metadata.namespace->0
        };
        if s_prime.resources().contains_key(key) {
            assert({
                &&& s_prime.resources().contains_key(key)
                &&& key.kind == Kind::PodKind
                &&& key.namespace == vsts.metadata.namespace->0
                &&& pod_name_match(key.name, vsts.metadata.name->0)
            });
            shield_lemma::lemma_no_interference_on_pods(s, s_prime, vsts, cluster, controller_id, req_msg);
            assert(false);
        }
    }
    assert forall |ord: nat, i: nat| ord < replicas(vsts) && i < pvc_cnt(vsts) implies {
        let pvc_key = ObjectRef {
            kind: PersistentVolumeClaimView::kind(),
            name: #[trigger] pvc_name(
                vsts.spec.volume_claim_templates->0[i as int].metadata.name->0,
                vsts.metadata.name->0,
                ord
            ),
            namespace: vsts.metadata.namespace->0
        };
        &&& s_prime.resources().contains_key(pvc_key)
    } by {
        let pvc_key = ObjectRef {
            kind: PersistentVolumeClaimView::kind(),
            name: #[trigger] pvc_name(
                vsts.spec.volume_claim_templates->0[i as int].metadata.name->0,
                vsts.metadata.name->0,
                ord
            ),
            namespace: vsts.metadata.namespace->0
        };
        assert({
            &&& s.resources().contains_key(pvc_key)
            &&& pvc_key.kind == Kind::PersistentVolumeClaimKind
            &&& pvc_key.namespace == vsts.metadata.namespace->0
            &&& pvc_name_match(pvc_key.name, vsts.metadata.name->0)
        }) by {
            VStatefulSetView::marshal_preserves_integrity();
            assert(s.resources().contains_key(vsts.object_ref()));
            let cr = VStatefulSetView::unmarshal(s.resources()[vsts.object_ref()])->Ok_0;
            assert(cr.spec == vsts.spec);
            assert(vsts.state_validation());
            let trigger = (vsts.spec.volume_claim_templates->0[i as int].metadata.name->0, ord);
            assert(dash_free(trigger.0));
            assert(pvc_key.name == (|i: (StringView, nat)| pvc_name(i.0, vsts.metadata.name->0, i.1))(trigger));
        }
        shield_lemma::lemma_no_interference_on_pvcs(s, s_prime, vsts, cluster, controller_id, req_msg);
    }
}

}