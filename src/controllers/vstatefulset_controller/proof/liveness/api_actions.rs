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

// TODO: if req does not need to be exposed, remove it from input and output
#[verifier(external_body)]
pub proof fn lemma_list_pod_request_returns_ok_with_objs_matching_vsts(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int,
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts.object_ref(), controller_id))),
    pending_list_pod_req_in_flight(vsts, controller_id)(s),
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
ensures
    pending_list_pod_resp_in_flight(vsts, controller_id)(s_prime),
{}

#[verifier(external_body)]
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
{}

#[verifier(external_body)]
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
{}

#[verifier(external_body)]
pub proof fn lemma_create_needed_pod_request_returns_ok_response(
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
{}

#[verifier(external_body)]
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
{}

#[verifier(external_body)]
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
    etcd_contains_outdated_pods_of(vsts, outdated_len)(s),
ensures
    etcd_contains_outdated_pods_of(vsts, outdated_len)(s_prime),
{}

}