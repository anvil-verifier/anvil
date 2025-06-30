use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::{types::*, state_machine::handle_list_request_msg},
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
    req_msg_is_list_vrs_req(vd, msg),
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
ensures
    resp_msg == handle_list_request_msg(msg, s.api_server).1,
    resp_msg_is_ok_list_resp_containing_matched_vrs(s_prime, vd, resp_msg),
{
    let resp_msg = handle_list_request_msg(msg, s.api_server).1;
    return resp_msg;
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
    // TODO: find a place for this post condition which holds since AfterListVRS state
    local_state_match_etcd_on_old_vrs_list(vd, controller_id)(s) == local_state_match_etcd_on_old_vrs_list(vd, controller_id)(s_prime),
    // TODO: find a place for this post condition which holds since AfterEnsureNewVRS state
    local_state_match_etcd_on_new_vrs(vd, controller_id)(s) == local_state_match_etcd_on_new_vrs(vd, controller_id)(s_prime),
{}

}