#![allow(unused_imports)]
use super::predicate::*;
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    message::*,
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
    // Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    // cluster.each_builtin_object_in_etcd_is_well_formed()(s),
    // cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s),
    // Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s),
    // cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
    // Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
    // Cluster::cr_objects_in_schedule_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s),
    // Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s),
    // Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
    // Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)(s),
    // Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, rmq.object_ref())(s),
    // Cluster::there_is_the_controller_state(controller_id)(s),
    // Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, rmq.object_ref())(s),
    // Cluster::no_pending_request_to_api_server_from_non_controllers()(s),
    // helper_invariants::garbage_collector_does_not_delete_vd_vrs_objects(rmq)(s), // still relies on desired_state_is indirectly
    // helper_invariants::every_msg_from_vd_controller_carries_vd_key(controller_id)(s),
    // helper_invariants::vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)(s),
    no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s),
    rmq_rely_conditions(cluster, controller_id)(s),
    msg.src != HostId::Controller(controller_id, rmq.object_ref()),
ensures
    // ultimate version of ownership and guarantee
    s.resources().contains_key(get_request(sub_resource, rmq).key) == s_prime.resources().contains_key(get_request(sub_resource, rmq).key),
    s.resources()[get_request(sub_resource, rmq).key] == s_prime.resources()[get_request(sub_resource, rmq).key],
{}

}