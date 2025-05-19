// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    proof::{helper_invariants, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*};
use vstd::{map::*, map_lib::*, prelude::*};

verus! {

// TODO: broken by changed ESR spec, needs new set-based (rather than map-based) argument.
#[verifier(external_body)]
pub proof fn lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
    s: ClusterState, s_prime: ClusterState, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, 
    msg: Message,
)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_builtin_object_in_etcd_is_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s),
        helper_invariants::no_pending_interfering_update_request()(s),
        helper_invariants::no_pending_interfering_update_status_request()(s),
        helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s),
        helper_invariants::no_pending_create_or_get_then_delete_request_not_from_controller_on_pods()(s),
        helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s),
        helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)(s),
        forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(diff))(s)),
        forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s)),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vrs_rely(other_id)(s)
    ensures
        matching_pods(vrs, s.resources()) == matching_pods(vrs, s_prime.resources()),
{
    if msg.src.is_Controller() {
        let id = msg.src.get_Controller_0();
        assert(
            (id != controller_id ==> cluster.controller_models.remove(controller_id).contains_key(id)));
        // Invoke non-interference lemma by trigger.
        assert(id != controller_id ==> vrs_rely(id)(s));
    }

    // Dispatch through all the requests which may mutate the k-v store.
    let mutates_key = if msg.content.is_create_request() {
        let req = msg.content.get_create_request();
        Some(ObjectRef{
            kind: req.obj.kind,
            name: if req.obj.metadata.name.is_Some() {
                req.obj.metadata.name.unwrap()
            } else {
                generate_name(s.api_server)
            },
            namespace: req.namespace,
        })
    } else if msg.content.is_delete_request() {
        let req = msg.content.get_delete_request();
        Some(req.key)
    } else if msg.content.is_update_request() {
        let req = msg.content.get_update_request();
        Some(req.key())
    } else if msg.content.is_update_status_request() {
        let req = msg.content.get_update_status_request();
        Some(req.key())
    } else {
        None
    };

    match mutates_key {
        Some(key) => {
            assert_maps_equal!(s.resources().remove(key) == s_prime.resources().remove(key));
            assert_maps_equal!(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
        },
        _ => {}
    };
}

// TODO: broken by changed ESR spec, needs new set-based (rather than map-based) argument.
#[verifier(external_body)]
pub proof fn lemma_api_request_not_made_by_vrs_maintains_matching_pods(
    s: ClusterState, s_prime: ClusterState, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
    diff: int, msg: Message, req_msg: Option<Message>
)
    requires
        req_msg.is_Some() ==> msg != req_msg.get_Some_0(),
        req_msg == s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg,
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_builtin_object_in_etcd_is_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        helper_invariants::every_create_request_is_well_formed(cluster, controller_id)(s),
        helper_invariants::no_pending_interfering_update_request()(s),
        helper_invariants::no_pending_interfering_update_status_request()(s),
        helper_invariants::garbage_collector_does_not_delete_vrs_pods(vrs)(s),
        helper_invariants::no_pending_create_or_get_then_delete_request_not_from_controller_on_pods()(s),
        helper_invariants::every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s),
        helper_invariants::every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)(s),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] vrs_rely(other_id)(s)
    ensures
        matching_pods(vrs, s.resources()) == matching_pods(vrs, s_prime.resources()),
{
    if msg.src.is_Controller() {
        let id = msg.src.get_Controller_0();
        assert(
            (id != controller_id ==> cluster.controller_models.remove(controller_id).contains_key(id)));
        // Invoke non-interference lemma by trigger.
        assert(id != controller_id ==> vrs_rely(id)(s));
    }

    // Dispatch through all the requests which may mutate the k-v store.
    let mutates_key = if msg.content.is_create_request() {
        let req = msg.content.get_create_request();
        Some(ObjectRef{
            kind: req.obj.kind,
            name: if req.obj.metadata.name.is_Some() {
                req.obj.metadata.name.unwrap()
            } else {
                generate_name(s.api_server)
            },
            namespace: req.namespace,
        })
    } else if msg.content.is_delete_request() {
        let req = msg.content.get_delete_request();
        Some(req.key)
    } else if msg.content.is_update_request() {
        let req = msg.content.get_update_request();
        Some(req.key())
    } else if msg.content.is_update_status_request() {
        let req = msg.content.get_update_status_request();
        Some(req.key())
    } else {
        None
    };

    match mutates_key {
        Some(key) => {
            assert_maps_equal!(s.resources().remove(key) == s_prime.resources().remove(key));
            assert_maps_equal!(matching_pod_entries(vrs, s.resources()) == matching_pod_entries(vrs, s_prime.resources()));
        },
        _ => {}
    };
}

}
