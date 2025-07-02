use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::{types::*, state_machine::*},
    cluster::*, 
    message::*
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::{
    trusted::{spec_types::*, step::*, util::*, liveness_theorem::*},
    model::{install::*, reconciler::*},
    proof::predicate::*,
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub proof fn lemma_list_vrs_request_returns_ok_with_objs_matching_vd(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message,
) -> (resp_msg: Message)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    req_msg_is_list_vrs_req(vd, controller_id, msg),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
ensures
    resp_msg == handle_list_request_msg(msg, s.api_server).1,
    resp_msg_is_ok_list_resp_containing_matched_vrs(s_prime, vd, resp_msg),
{
    let resp_msg = handle_list_request_msg(msg, s.api_server).1;
    return resp_msg;
}

#[verifier(external_body)]
pub proof fn lemma_create_new_vrs_request_returns_ok_at_after_ensure_new_vrs(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message, n: nat
) -> (resp_msg: Message)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    req_msg_is_pending_create_new_vrs_req_in_flight(vd, controller_id, msg)(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    n_old_vrs_exists_in_etcd(controller_id, vd, n)(s),
    no_new_vrs_exists_in_etcd(controller_id, vd)(s),
ensures
    resp_msg == handle_create_request_msg(cluster.installed_types, msg, s.api_server).1,
    resp_msg_is_ok_create_new_vrs_resp(vd, controller_id, resp_msg)(s_prime),
    n_old_vrs_exists_in_etcd(controller_id, vd, (n - nat1!()) as nat)(s_prime),
    new_vrs_with_replicas_exists_in_etcd(controller_id, vd, vd.spec.replicas.unwrap_or(int1!()))(s_prime),
{
    return handle_create_request_msg(cluster.installed_types, msg, s.api_server).1;
}

#[verifier(external_body)]
pub proof fn lemma_get_then_update_request_returns_ok_at_after_scale_new_vrs(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message, replicas: int, n: nat
) -> (resp_msg: Message)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    req_msg_is_get_then_update_req_with_replicas(vd, controller_id, msg, vd.spec.replicas.unwrap_or(int1!()))(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    n_old_vrs_exists_in_etcd(controller_id, vd, n)(s),
    new_vrs_with_replicas_exists_in_etcd(controller_id, vd, replicas)(s),
ensures
    resp_msg == handle_get_then_update_request_msg(cluster.installed_types, msg, s.api_server).1,
    resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, resp_msg, replicas)(s_prime),
    n_old_vrs_exists_in_etcd(controller_id, vd, n)(s_prime),
    new_vrs_with_replicas_exists_in_etcd(controller_id, vd, vd.spec.replicas.unwrap_or(int1!()))(s_prime),
{
    return handle_get_then_update_request_msg(cluster.installed_types, msg, s.api_server).1;
}

#[verifier(external_body)]
pub proof fn lemma_get_then_update_request_returns_ok_at_after_scale_down_old_vrs(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message, n: nat
) -> (resp_msg: Message)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    req_msg_is_get_then_update_req_with_replicas(vd, controller_id, msg, int0!())(s),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    n_old_vrs_exists_in_etcd(controller_id, vd, n)(s),
    new_vrs_with_replicas_exists_in_etcd(controller_id, vd, vd.spec.replicas.unwrap_or(int1!()))(s),
ensures
    resp_msg == handle_get_then_update_request_msg(cluster.installed_types, msg, s.api_server).1,
    resp_msg_is_ok_get_then_update_resp_with_replicas(vd, controller_id, resp_msg, int0!())(s_prime),
    n_old_vrs_exists_in_etcd(controller_id, vd, (n - nat1!()) as nat)(s_prime),
    new_vrs_with_replicas_exists_in_etcd(controller_id, vd, vd.spec.replicas.unwrap_or(int1!()))(s_prime),
{
    return handle_get_then_update_request_msg(cluster.installed_types, msg, s.api_server).1;
}

#[verifier(external_body)]
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_filter_old_and_new_vrs_on_etcd(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message,
)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    (!Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg)
        || !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()))
ensures
    filter_old_and_new_vrs_on_etcd(vd, s.resources()) ==
    filter_old_and_new_vrs_on_etcd(vd, s_prime.resources()),
    s.resources().values().filter(list_vrs_obj_filter(vd)).to_seq() ==
    s_prime.resources().values().filter(list_vrs_obj_filter(vd)).to_seq(),
    objects_to_vrs_list(s.resources().values().filter(list_vrs_obj_filter(vd)).to_seq()) ==
    objects_to_vrs_list(s_prime.resources().values().filter(list_vrs_obj_filter(vd)).to_seq()),
{}

}