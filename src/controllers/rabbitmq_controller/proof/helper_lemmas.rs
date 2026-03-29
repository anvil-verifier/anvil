#![allow(unused_imports)]
use super::predicate::*;
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    message::*,
    api_server::state_machine::*,
};
use crate::rabbitmq_controller::{
    model::resource::*,
    proof::{predicate::*, resource::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*, rely_guarantee::*},
};
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

#[verifier(external_body)]
pub proof fn rmq_with_different_key_implies_request_with_different_key(rmq: RabbitmqClusterView, other_rmq: RabbitmqClusterView, sub_resource: SubResource)
requires
    rmq.object_ref() != other_rmq.object_ref()
ensures
    get_request(sub_resource, other_rmq).key != get_request(sub_resource, rmq).key,
{}

// shield_lemma

pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_resource_object(
    s: ClusterState, s_prime: ClusterState, rmq: RabbitmqClusterView, cluster: Cluster, controller_id: int, sub_resource: SubResource, msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rmq, sub_resource)(s),
    no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s),
    rmq_rely_conditions(cluster, controller_id)(s),
    msg.src != HostId::Controller(controller_id, rmq.object_ref()),
ensures
    // ultimate version of ownership and guarantee
    s.resources().contains_key(get_request(sub_resource, rmq).key) == s_prime.resources().contains_key(get_request(sub_resource, rmq).key),
    s.resources()[get_request(sub_resource, rmq).key] == s_prime.resources()[get_request(sub_resource, rmq).key],
{}

pub proof fn lemma_update_sub_resource_request_returns_ok(
    s: ClusterState, s_prime: ClusterState, rmq: RabbitmqClusterView, cluster: Cluster, controller_id: int, sub_resource: SubResource, msg: Message
) -> (resp_msg: Message)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    cluster_invariants_since_reconciliation(cluster, controller_id, rmq, sub_resource)(s),
    req_msg_is_the_in_flight_pending_req_at_after_update_resource_step(sub_resource, rmq, controller_id, msg)(s),
ensures
    resp_msg_is_the_in_flight_ok_resp_at_after_update_resource_step(sub_resource, rmq, controller_id, resp_msg)(s_prime),
    resource_state_matches(sub_resource, rmq)(s_prime),
{
    let resp_msg = handle_update_request_msg(cluster.installed_types, msg, s.api_server).1;

    let step = after_update_k_request_step(sub_resource);
    let msg = s_prime.ongoing_reconciles(controller_id)[rmq.object_ref()].pending_req_msg->0;
    let request = msg.content->APIRequest_0;
    let key = get_request(sub_resource, rmq).key;
    let local_state = s_prime.ongoing_reconciles(controller_id)[rmq.object_ref()].local_state;
    let unmarshalled_state = RabbitmqReconcileState::unmarshal(local_state).unwrap();
    assert(at_rabbitmq_step_with_rabbitmq(rmq, controller_id, step)(s_prime));
    assert(Cluster::has_pending_k8s_api_req_msg(controller_id, s_prime, rmq.object_ref()));
    assert(msg.src == HostId::Controller(controller_id, rmq.object_ref()));
    assert(resource_update_request_msg(key)(msg));
    assert(s_prime.in_flight().contains(resp_msg));
    assert(resp_msg_matches_req_msg(resp_msg, msg));
    assert(resp_msg.content.get_update_response().res is Ok);
    assert(state_after_update(sub_resource, rmq, resp_msg.content.get_update_response().res->Ok_0, unmarshalled_state) is Ok);

    return resp_msg;
}

}