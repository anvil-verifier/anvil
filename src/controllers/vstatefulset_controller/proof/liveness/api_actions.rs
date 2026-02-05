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
    proof::{predicate::*, liveness::state_predicates::*},
};
use crate::vstatefulset_controller::trusted::step::VStatefulSetReconcileStepView::*;
use crate::reconciler::spec::io::*;
use vstd::{seq_lib::*, prelude::*, map_lib::*, set::*};
use crate::vstd_ext::{seq_lib::*, set_lib::*, map_lib::*, string_view::int_to_string_view};

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
                assert(created_obj.metadata.owner_references is Some);
                assert(created_obj.metadata.owner_references->0.len() == 1);
            }
            assert(object_validity_check(created_obj, cluster.installed_types) is None) by {
                assert(PodView::unmarshal_status(created_obj.status) is Ok);
                assert(PodView::unmarshal_spec(created_obj.spec) is Ok);
            }
        }
        assert(s_prime.resources() == s.resources().insert(req.key(), created_obj));
    } else {
        assert(admission_chk_res->0 == ObjectAlreadyExists);
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
                    assert(updated_obj.metadata.owner_references is Some);
                    assert(updated_obj.metadata.owner_references->0.len() == 1);
                }
            }
        }
    }
}

pub proof fn lemma_get_then_delete_pod_request_returns_ok_or_not_found_err(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message,
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    Cluster::pending_req_msg_is(controller_id, s, vsts.object_ref(), req_msg),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    req_msg.src == HostId::Controller(controller_id, vsts.object_ref()),
    req_msg.dst == HostId::APIServer,
    req_msg.content.is_get_then_delete_request(),
ensures
    resp_msg_or_none(s_prime, vsts.object_ref(), controller_id) is Some,
    ({
        let resp_msg = resp_msg_or_none(s_prime, vsts.object_ref(), controller_id).unwrap();
        &&& resp_msg.content.is_get_then_delete_response()
        &&& resp_msg.content.get_get_then_delete_response().res is Err
            ==> resp_msg.content.get_get_then_delete_response().res->Err_0 == ObjectNotFound
    }),
    ({ // no side effect
        let req = req_msg.content.get_get_then_delete_request();
        &&& forall |key: ObjectRef| key != req.key() ==> (s_prime.resources().contains_key(key) == s.resources().contains_key(key))
        &&& !s_prime.resources().contains_key(req.key())
    }),
{}

#[verifier(external_body)]
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_local_state_coherence(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    req_msg.src != HostId::Controller(controller_id, vsts.object_ref()),
    req_msg.dst == HostId::APIServer,
    local_state_is_valid_and_coherent(vsts, controller_id)(s),
ensures
    local_state_is_valid_and_coherent(vsts, controller_id)(s_prime),
{}

#[verifier(external_body)]
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_outdated_pods_count_in_etcd(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message, outdated_len: nat
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    req_msg.src != HostId::Controller(controller_id, vsts.object_ref()),
    req_msg.dst == HostId::APIServer,
    n_outdated_pods_in_etcd(vsts, outdated_len)(s),
ensures
    n_outdated_pods_in_etcd(vsts, outdated_len)(s_prime),
{}

#[verifier(external_body)]
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_current_state_matches(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
    req_msg.src != HostId::Controller(controller_id, vsts.object_ref()),
    req_msg.dst == HostId::APIServer,
    current_state_matches(vsts)(s),
ensures
    current_state_matches(vsts)(s_prime),
{}

}