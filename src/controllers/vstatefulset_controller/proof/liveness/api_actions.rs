use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
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
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, req_msg: Message,
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(req_msg))),
    req_msg_is_list_pod_req(vsts.object_ref(), controller_id, req_msg),
    at_vsts_step(vsts, controller_id, at_step![AfterListPod])(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
ensures
    resp_msg == handle_list_request_msg(req_msg, s.api_server).1,
    resp_msg_is_ok_list_resp_of_pods(vsts, resp_msg, s_prime),
{
    return handle_create_request_msg(cluster.installed_types, req_msg, s.api_server).1;
}

#[verifier(external_body)]
pub proof fn lemma_get_pvc_request_returns_ok_or_err_response(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int,
)
requires
    req_msg_or_none(s, vsts, controller_id) is Some,
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(req_msg_or_none(s, vsts, controller_id))),
    pending_get_pvc_req_in_flight(vsts, controller_id)(s),
    cluster_invariants_since_reconciliation(cluster, vsts, controller_id)(s),
ensures
    pending_get_pvc_resp_msg_in_flight(vsts, controller_id)(s_prime),
{}
}