// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::predicate::*;
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, owner_reference::*, prelude::*, resource::*, label_selector::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
    api_server::state_machine::*,
};
use crate::kubernetes_cluster::proof::api_server::*;
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::rabbitmq_controller::{
    model::resource::*,
    proof::{
        predicate::*, resource::*, helper_lemmas::*, guarantee::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*, rely_guarantee::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib::*, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};
use crate::reconciler::spec::io::*;

verus! {

pub proof fn lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated_forall(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(no_create_resource_request_msg_without_name_in_flight(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)))),
        spec.entails(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_delete_resource_request_msg_in_flight(res, rabbitmq))))),
        spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq))))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_delete_resource_request_msg_in_flight(res, rabbitmq)), SubResource::ServerConfigMap);
    lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, cluster, spec, rabbitmq);
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
proof fn lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(no_create_resource_request_msg_without_name_in_flight(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)))),
        spec.entails(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let inv = cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq);
    let next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& no_create_resource_request_msg_without_name_in_flight(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)(s)
        &&& object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s_prime)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s_prime)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    };
    always_to_always_later(spec, lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)));
    always_to_always_later(spec, lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        lift_state(no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(no_create_resource_request_msg_without_name_in_flight(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)),
        lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        later(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id))),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        later(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id))),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
    );
    leads_to_weaken(
        spec, true_pred(), lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())),
        true_pred(), lift_state(inv)
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
            RabbitmqClusterView::marshal_preserves_integrity();
            RabbitmqReconcileState::marshal_preserves_integrity();
            match RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].local_state).unwrap().reconcile_step {
                RabbitmqReconcileStep::AfterKRequestStep(_, sub_resource) => {
                    match sub_resource {
                        SubResource::ServiceAccount | SubResource::Role | SubResource::RoleBinding | SubResource::VStatefulSetView => {
                            let step = choose |step| cluster.next_step(s, s_prime, step);
                            match step {
                                Step::APIServerStep(input) => {
                                    let msg = input->0;
                                    if resource_get_then_update_request_msg(resource_key)(msg) {
                                    } else if resource_create_request_msg(resource_key)(msg) {
                                    } else {
                                        other_objects_are_unaffected_if_request_fails_to_be_applied(cluster, s, s_prime, input->0, resource_key);
                                    }
                                },
                                Step::ControllerStep(_) => {},
                                _ => {},
                            }
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        }
    }
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(inv));
}

pub proof fn lemma_eventually_always_object_in_response_at_after_create_resource_step_is_same_as_etcd_forall(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_delete_resource_request_msg_in_flight(res, rabbitmq))))),
        spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq))))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_interfering_requests_in_flight(res, controller_id, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, res, rabbitmq))))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq))))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_delete_resource_request_msg_in_flight(res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_interfering_requests_in_flight(res, controller_id, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, res, rabbitmq)), SubResource::ServerConfigMap);
    lemma_eventually_always_object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, cluster, spec, rabbitmq);
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_object_in_response_at_after_create_resource_step_is_same_as_etcd(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)))),
        spec.entails(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let inv = object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq);
    let next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, key)(s_prime)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())(s)
        &&& no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s_prime)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)(s)
        &&& every_resource_create_request_implies_at_after_create_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    };
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    always_to_always_later(spec, lift_state(Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, key)));
    always_to_always_later(spec, lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        later(lift_state(Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, key))),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())),
        lift_state(no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        later(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id))),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)),
        lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
    );
    leads_to_weaken(
        spec, true_pred(), lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())),
        true_pred(), lift_state(inv)
    );
    let resource_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let key = rabbitmq.object_ref();
    assert forall |s: ClusterState, s_prime: ClusterState| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, SubResource::ServerConfigMap))(s_prime) {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    RabbitmqReconcileState::marshal_preserves_integrity();
                    if controller_id == input.0 && input.2->0 == key {
                        // The controller just issued a new pending request.
                        // The new request was just added to in_flight, so no response for it
                        // can exist yet in s_prime.in_flight() (the request has a fresh unique id).
                        assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some);
                        let pending = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                        assert forall |msg: Message| s_prime.in_flight().contains(msg) && #[trigger] resp_msg_matches_req_msg(msg, pending) implies resource_create_response_msg(resource_key, s_prime)(msg) by {
                            assert(msg.content is APIResponse);
                            // A response matching the new pending req can't exist because
                            // the pending req was just created with a fresh id.
                            // Every in-flight msg in s has id < allocator, but the new req's id >= allocator.
                            if s.in_flight().contains(msg) {
                                assert(Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s));
                                assert(false);
                            } else {
                                assert(false);
                            }
                        }
                    } else {
                        // Different controller/key - ongoing_reconciles for our key is unchanged
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        object_in_response_at_after_create_resource_step_is_same_as_etcd_helper(controller_id, cluster, s, s_prime, rabbitmq);
                    }
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
                        && resource_create_request_msg(resource_key)(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0)) by{
                        assert(inv(s));
                    }
                    object_in_response_at_after_create_resource_step_is_same_as_etcd_helper(controller_id, cluster, s, s_prime, rabbitmq);
                }
            }
        }
    }
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(inv));
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
proof fn object_in_response_at_after_create_resource_step_is_same_as_etcd_helper(
    controller_id: int, cluster: Cluster, s: ClusterState, s_prime: ClusterState, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg is Some,
        resource_create_request_msg(get_request(SubResource::ServerConfigMap, rabbitmq).key)(s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, SubResource::ServerConfigMap))(s_prime),
        cluster.next()(s, s_prime),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        Cluster::every_in_flight_msg_has_unique_id()(s),
        cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime),
        Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())(s_prime),
        Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)(s),
        no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)(s),
        object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)(s),
        resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)(s),
        object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)(s),
        // added
        every_resource_create_request_implies_at_after_create_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)(s),
    ensures
        forall |msg: Message|
            s_prime.in_flight().contains(msg)
            && #[trigger] resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0)
            ==> resource_create_response_msg(get_request(SubResource::ServerConfigMap, rabbitmq).key, s_prime)(msg),
{
    let resource_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let key = rabbitmq.object_ref();
    let pending_req = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
    assert forall |msg: Message| s_prime.in_flight().contains(msg) && #[trigger] resp_msg_matches_req_msg(msg, pending_req) implies resource_create_response_msg(resource_key, s_prime)(msg) by {
        assert(msg.src is APIServer);
        assert(msg.content.is_create_response());
        if msg.content.get_create_response().res is Ok {
            assert(is_ok_create_response_msg()(msg));
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    let req_msg = input->0;
                    assert(!resource_delete_request_msg(resource_key)(req_msg));
                    assert(!resource_get_then_update_request_msg(resource_key)(req_msg));
                    assert(!resource_update_status_request_msg(resource_key)(req_msg));
                    assert(!resource_get_then_delete_request_msg(resource_key)(req_msg));
                    assert(!resource_get_then_update_request_msg(resource_key)(req_msg));
                    assert(!resource_get_then_update_status_request_msg(resource_key)(req_msg));
                    match req_msg.content->APIRequest_0 {
                        APIRequest::CreateRequest(_) => {
                            if !s.in_flight().contains(msg) {
                                let req = input->0;
                                assert(msg.content.get_create_response().res->Ok_0.object_ref() == req.content.get_create_request().key());
                                assert(msg.content.get_create_response().res->Ok_0.object_ref() == resource_key);
                                assert(msg.content.get_create_response().res->Ok_0 == s_prime.resources()[req.content.get_create_request().key()]);
                                assert(resource_create_request_msg(resource_key)(req));
                                assert(resource_create_response_msg(resource_key, s_prime)(msg));
                            } else {
                                if resource_create_request_msg(resource_key)(req_msg) {
                                    assert(Cluster::pending_req_msg_is(controller_id, s, key, req_msg));
                                    assert(req_msg == pending_req);
                                    assert(false);
                                }
                                assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                                assert(resource_create_response_msg(resource_key, s)(msg));
                            }
                        },
                        _ => {
                            assert(s.in_flight().contains(msg));
                            assert(resp_msg_matches_req_msg(msg, s.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                            assert(s.resources()[resource_key] == s_prime.resources()[resource_key]);
                            assert(resource_create_response_msg(resource_key, s_prime)(msg));
                        }
                    }
                },
                _ => {
                    assert(s.in_flight().contains(msg));
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    assert(resource_create_response_msg(resource_key, s_prime)(msg));
                }
            }
        }
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_object_in_response_at_after_update_resource_step_is_same_as_etcd(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)))),
        spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let inv = object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq);
    let next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, key)(s_prime)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s_prime)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    };
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    always_to_always_later(spec, lift_state(Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, key)));
    always_to_always_later(spec, lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        later(lift_state(Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, key))),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        later(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id))),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
    );
    leads_to_weaken(
        spec, true_pred(), lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())),
        true_pred(), lift_state(inv)
    );
    let resource_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let key = rabbitmq.object_ref();
    assert forall |s: ClusterState, s_prime: ClusterState| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, SubResource::ServerConfigMap))(s_prime) {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    RabbitmqReconcileState::marshal_preserves_integrity();
                    RabbitmqClusterView::marshal_preserves_integrity();
                    assert(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s));
                    assert(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s_prime));
                    if controller_id == input.0 && input.2->0 == key {
                        // The controller just issued a new pending request.
                        // The new request was just added to in_flight, so no response for it
                        // can exist yet in s_prime.in_flight() (the request has a fresh unique id).
                        assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some);
                        let pending = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                        assert forall |msg: Message| s_prime.in_flight().contains(msg) && #[trigger] resp_msg_matches_req_msg(msg, pending) implies resource_get_then_update_response_msg(resource_key, s_prime)(msg) by {
                            assert(msg.content is APIResponse);
                            // A response matching the new pending req can't exist because
                            // the pending req was just created with a fresh id.
                            // Every in-flight msg in s has id < allocator, but the new req's id >= allocator.
                            if s.in_flight().contains(msg) {
                                // msg was already in s.in_flight() but pending is new
                                assert(Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s));
                                // pending's id >= s.allocator, msg's id < s.allocator
                                // So msg.rpc_id != pending.rpc_id, contradicting resp_msg_matches_req_msg
                                assert(false);
                            } else {
                                // msg is new in s_prime.in_flight() - must come from the API server step
                                // but this is a ControllerStep, not APIServerStep, so no new response is added
                                assert(false);
                            }
                        }
                    } else {
                        // Different controller/key - ongoing_reconciles for our key is unchanged
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        object_in_response_at_after_update_resource_step_is_same_as_etcd_helper(controller_id, cluster, s, s_prime, rabbitmq);
                    }
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
                        && resource_get_then_update_request_msg(resource_key)(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0)) by{
                        assert(inv(s));
                    }
                    object_in_response_at_after_update_resource_step_is_same_as_etcd_helper(controller_id, cluster, s, s_prime, rabbitmq);
                }
            }
        }
    }
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(inv));
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
proof fn object_in_response_at_after_update_resource_step_is_same_as_etcd_helper(controller_id: int, cluster: Cluster, s: ClusterState, s_prime: ClusterState, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg is Some,
        resource_get_then_update_request_msg(get_request(SubResource::ServerConfigMap, rabbitmq).key)(s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, SubResource::ServerConfigMap))(s_prime),
        cluster.next()(s, s_prime),
        Cluster::every_in_flight_msg_has_unique_id()(s),
        cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime),
        Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())(s_prime),
        Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        no_delete_resource_request_msg_in_flight(SubResource::ServerConfigMap, rabbitmq)(s),
        no_interfering_requests_in_flight(SubResource::ServerConfigMap, controller_id, rabbitmq)(s),
        object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)(s),
        resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)(s),
        object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)(s),
        every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)(s),
    ensures
        forall |msg: Message| #[trigger]
            s_prime.in_flight().contains(msg)
            && resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0)
            ==> resource_get_then_update_response_msg(get_request(SubResource::ServerConfigMap, rabbitmq).key, s_prime)(msg),
{
    let resource_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let key = rabbitmq.object_ref();
    let pending_req = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
    assert forall |msg: Message| s_prime.in_flight().contains(msg) && #[trigger] resp_msg_matches_req_msg(msg, pending_req) implies resource_get_then_update_response_msg(resource_key, s_prime)(msg) by {
        assert(msg.src is APIServer);
        assert(msg.content.is_update_response());
        if msg.content.get_update_response().res is Ok {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    let req_msg = input->0;
                    assert(req_msg.content is APIRequest);
                    assert(!resource_delete_request_msg(resource_key)(req_msg));
                    assert(!resource_update_status_request_msg(resource_key)(req_msg));
                    assert(!resource_get_then_delete_request_msg(resource_key)(req_msg));
                    assert(!resource_get_then_update_request_msg(resource_key)(req_msg));
                    assert(!resource_get_then_update_status_request_msg(resource_key)(req_msg));
                    match req_msg.content->APIRequest_0 {
                        APIRequest::UpdateRequest(_) => {
                            if !s.in_flight().contains(msg) {
                                assert(msg.content.get_update_response().res->Ok_0.object_ref() == req_msg.content.get_get_then_update_request().key());
                                assert(msg.content.get_update_response().res->Ok_0.object_ref() == resource_key);
                                assert(msg.content.get_update_response().res->Ok_0 == s_prime.resources()[req_msg.content.get_get_then_update_request().key()]);
                                assert(s_prime.resources().contains_key(resource_key));
                                assert(msg.content.get_update_response().res->Ok_0 == s_prime.resources()[resource_key]);
                                assert(resource_get_then_update_response_msg(resource_key, s_prime)(msg));
                            } else {
                                if resource_get_then_update_request_msg(resource_key)(req_msg) {
                                    assert(Cluster::pending_req_msg_is(controller_id, s, key, req_msg));
                                    assert(req_msg == pending_req);
                                    assert(false);
                                }
                                assert(!resource_get_then_update_request_msg(resource_key)(req_msg));
                                assert(req_msg.content.get_get_then_update_request().key() != resource_key);
                                assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                                assert(!s.in_flight().contains(pending_req));
                                assert(resource_get_then_update_response_msg(resource_key, s)(msg));
                            }
                        },
                        _ => {
                            assert(s.in_flight().contains(msg));
                            assert(resource_get_then_update_response_msg(resource_key, s)(msg));
                            assert(s.resources().contains_key(resource_key));
                            assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                            assert(!s.in_flight().contains(pending_req));
                        },
                    }
                },
                _ => {
                    assert(s.in_flight().contains(msg));
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    assert(!s.in_flight().contains(pending_req));
                    assert(resource_get_then_update_response_msg(resource_key, s)(msg));
                },
            }
        }
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_always_request_at_after_get_request_step_is_resource_get_request(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(request_at_after_get_request_step_is_resource_get_request(controller_id, sub_resource, rabbitmq)))),
{
    // hide(make_stateful_set); // TODO: Verus AIR code bug with fuel path
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let inv = request_at_after_get_request_step_is_resource_get_request(controller_id, sub_resource, rabbitmq);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_cr_states_are_unmarshallable::<RabbitmqReconciler, RabbitmqReconcileState, RabbitmqClusterView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(spec, controller_id);
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s_prime)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s_prime)
    };
    always_to_always_later(spec, lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)));
    always_to_always_later(spec, lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)));
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        later(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id))),
        later(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))
    );
    assert forall |s: ClusterState, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        if at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s_prime) {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    RabbitmqClusterView::marshal_preserves_integrity();
                    RabbitmqReconcileState::marshal_preserves_integrity();
                    if input.0 == controller_id && input.2->0 == key {
                        assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some);
                        assert(resource_get_request_msg(resource_key)(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                    } else {
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    }
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                }
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_response_at_after_get_resource_step_is_resource_get_response(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)))),
{
    let key = rabbitmq.object_ref();
    let next = |s: ClusterState| {
        &&& request_at_after_get_request_step_is_resource_get_request(controller_id, sub_resource, rabbitmq)(s)
        &&& Cluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(controller_id, key)(s)
    };
    lemma_always_request_at_after_get_request_step_is_resource_get_request(controller_id, cluster, spec, sub_resource, rabbitmq);
    assert(valid(lift_state(next).implies(lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)))));
    cluster.lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(spec, controller_id, key);
    invariant_n!(
        spec, lift_state(next), lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)),
        lift_state(request_at_after_get_request_step_is_resource_get_request(controller_id, sub_resource, rabbitmq)),
        lift_state(Cluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(controller_id, key))
    );
}

pub proof fn lemma_eventually_always_every_resource_get_then_update_request_implies_at_after_update_resource_step_forall(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, rabbitmq).key))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))),
        // rely
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, rabbitmq).key)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_delete_resource_request_msg_in_flight(res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_interfering_requests_in_flight(res, controller_id, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(res, rabbitmq)), sub_resource);
        lemma_eventually_always_every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
proof fn lemma_eventually_always_every_resource_get_then_update_request_implies_at_after_update_resource_step(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq)))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)))),
        // rely
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let requirements = |msg: Message, s: ClusterState| {
        resource_get_then_update_request_msg(resource_key)(msg) ==> {
            &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
            &&& at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
            &&& msg.content.get_get_then_update_request().obj.metadata.resource_version is Some
            &&& msg.content.get_get_then_update_request().obj.metadata.resource_version->0 < s.api_server.resource_version_counter
            &&& (
                s.resources().contains_key(resource_key)
                && msg.content.get_get_then_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
            ) ==> (
                update(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap(), s.resources()[resource_key]) is Ok
                && msg.content.get_get_then_update_request().obj == update(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap(), s.resources()[resource_key])->Ok_0
            )
        }
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(rabbitmq)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)(s)
        &&& Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, rabbitmq).key)(s)
        &&& response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)(s)
        &&& no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)(s)
        &&& no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::no_pending_request_to_api_server_from_non_controllers()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_get_then_update_request_msg(resource_key)(msg) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    RabbitmqReconcileState::marshal_preserves_integrity();
                    lemma_resource_get_then_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                    let resp = step->ControllerStep_0.1->0;
                    assert(is_ok_get_response_msg()(resp));
                    assert(s.in_flight().contains(resp));
                    assert(resp.content.get_get_response().res->Ok_0.metadata.resource_version == msg.content.get_get_then_update_request().obj.metadata.resource_version);
                    if s.resources().contains_key(resource_key) && resp.content.get_get_response().res->Ok_0.metadata.resource_version == s.resources()[resource_key].metadata.resource_version {
                        assert(resp.content.get_get_response().res->Ok_0 == s.resources()[resource_key]);
                        assert(s_prime.resources()[resource_key] == s.resources()[resource_key]);
                    }
                    if sub_resource == SubResource::VStatefulSetView {
                        let cm_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
                        assert(s.resources()[cm_key] == s_prime.resources()[cm_key]);
                        assert(RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap().latest_config_map_rv_opt == RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].local_state).unwrap().latest_config_map_rv_opt);
                    }
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    match step {
                        Step::APIServerStep(input) => {
                            let req_msg = input->0;
                            match req_msg.src {
                                HostId::Controller(id, cr_key) => {
                                    match req_msg.content->APIRequest_0 {
                                        APIRequest::GetRequest(_) | APIRequest::ListRequest(_) => {},
                                        APIRequest::CreateRequest(req) => {
                                            if id == controller_id { // use guarantee
                                                if resource_create_request_msg(resource_key)(req_msg) {}
                                            } else { // use rely
                                                assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                                assert(rmq_rely(id)(s));
                                            }
                                        },
                                        APIRequest::UpdateRequest(req) => {
                                            if resource_get_then_update_request_msg(resource_key)(req_msg) {}
                                        },
                                        _ => {}, // no_interfering_requests_in_flight
                                    }
                                },
                                HostId::BuiltinController => {},
                                _ => {},
                            }
                        },
                        _ => {},
                    }
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    invariant_n!(spec,
        lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)),
        lift_state(Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, rabbitmq).key)),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)),
        lift_state(no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)),
        lift_state(no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)),
        lift_state(rmq_rely_conditions(cluster, controller_id)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id))),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id))
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_resource_get_then_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub proof fn lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr_forall(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq))))) by {
        lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        // rely
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let requirements = |msg: Message, s: ClusterState| {
        resource_get_then_update_request_msg(resource_key)(msg) ==> {
            &&& at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
            &&& msg.content.get_get_then_update_request().obj.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
        }
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)(s)
        &&& Cluster::desired_state_is(rabbitmq)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_get_then_update_request_msg(resource_key)(msg) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    RabbitmqReconcileState::marshal_preserves_integrity();
                    lemma_resource_get_then_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    invariant_n!(spec,
        lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id))),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id))
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub proof fn lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step_forall(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        // rely
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq))))) by {
        lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        // rely
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let requirements = |msg: Message, s: ClusterState| {
        resource_create_request_msg(resource_key)(msg) ==> {
            &&& msg.src == HostId::Controller(controller_id, rabbitmq.object_ref())
            &&& at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
            &&& make(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap()) is Ok
            &&& msg.content.get_create_request().obj == make(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap())->Ok_0
        }
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)(s)
        &&& Cluster::desired_state_is(rabbitmq)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_create_request_msg(resource_key)(msg) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    RabbitmqReconcileState::marshal_preserves_integrity();
                    lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    invariant_n!(spec,
        lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub open spec fn make_owner_references_with_name_and_uid(name: StringView, uid: Uid) -> OwnerReferenceView {
    OwnerReferenceView {
        block_owner_deletion: None,
        controller: Some(true),
        kind: RabbitmqClusterView::kind(),
        name: name,
        uid: uid,
    }
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
pub proof fn lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref_and_no_interfering_requests_in_flight(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq)))),
{
    // they are proved together because there are dependencies in between
    let p = resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq);
    let q = no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq);
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let inv = |s: ClusterState| {
        &&& resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)(s)
        &&& no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq)(s)
    };
    lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers_nor_deletion_timestamp(controller_id, cluster, spec, sub_resource, rabbitmq);
    lemma_always_no_create_resource_request_msg_without_name_in_flight(cluster, controller_id, spec, sub_resource, rabbitmq);
    guarantee_condition_holds(spec, cluster, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_no_pending_request_to_api_server_from_api_server_or_external(spec);
    cluster.lemma_always_all_requests_from_pod_monkey_are_api_pod_requests(spec);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    cluster.lemma_always_cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    always_to_always_later(spec, lift_state(rmq_guarantee(controller_id)));
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    always_to_always_later(spec, lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()));
    always_to_always_later(spec, lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()));
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers_nor_deletion_timestamp(sub_resource, rabbitmq)(s)
        &&& no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& rmq_guarantee(controller_id)(s)
        &&& rmq_guarantee(controller_id)(s_prime)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& Cluster::cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers_nor_deletion_timestamp(sub_resource, rabbitmq)),
        lift_state(no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(rmq_guarantee(controller_id)),
        later(lift_state(rmq_guarantee(controller_id))),
        lift_state(rmq_rely_conditions(cluster, controller_id)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id))),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        later(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests())),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        later(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())
    );
    let resource_key = get_request(sub_resource, rabbitmq).key;
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        assert(p(s_prime)) by {
            assume(false);
            match step {
                Step::APIServerStep(input) => {
                    let msg = input->0;
                    match msg.content->APIRequest_0 {
                        APIRequest::CreateRequest(req) => {
                            assert(!resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg));
                            if req.obj.metadata.name is Some {
                                if resource_create_request_msg(resource_key)(msg) {} else {
                                    assert(s.resources().contains_key(resource_key) == s_prime.resources().contains_key(resource_key));
                                    assert(s.resources()[resource_key] == s_prime.resources()[resource_key]);
                                }
                            } else if req.obj.kind == resource_key.kind && req.namespace == resource_key.namespace {
                                assert(req.obj.metadata.generate_name is None);
                            }
                        },
                        APIRequest::UpdateRequest(req) => {
                            if resource_get_then_update_request_msg(resource_key)(msg) {} else {
                                assert(req.key() != resource_key);
                            }
                        },
                        _ => {}
                    }
                },
                _ => {},
            }
        }
        assert(q(s_prime)) by {
            assert forall |msg: Message| #[trigger] s_prime.in_flight().contains(msg) && msg.content is APIRequest
                implies request_does_not_interfere(sub_resource, controller_id, rabbitmq, msg)(s_prime) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    assert(has_rmq_prefix(resource_key.name)) by {
                        lemma_resource_key_has_rmq_prefix(sub_resource, rabbitmq);
                    }
                    let etcd_obj = s.resources()[resource_key];
                    assert(s.resources().contains_key(resource_key) ==> {// p(s)
                        &&& etcd_obj.metadata.resource_version is Some
                        &&& exists |some_rmq: RabbitmqClusterView| #[trigger] etcd_obj.metadata.owner_references_contains(some_rmq.controller_owner_ref())
                    }) by {
                        if s.resources().contains_key(resource_key) {
                            let uid = choose |uid: Uid| #![auto] etcd_obj.metadata.owner_references == Some(seq![OwnerReferenceView {
                                block_owner_deletion: None,
                                controller: Some(true),
                                kind: RabbitmqClusterView::kind(),
                                name: rabbitmq.metadata.name->0,
                                uid: uid,
                            }]);
                            let some_rmq = RabbitmqClusterView {
                                metadata: ObjectMetaView {
                                    name: rabbitmq.metadata.name,
                                    uid: Some(uid),
                                    ..ObjectMetaView::default()
                                },
                                ..RabbitmqClusterView::default()
                            };
                            assert(etcd_obj.metadata.owner_references->0.contains(etcd_obj.metadata.owner_references->0[0]));
                            assert(etcd_obj.metadata.owner_references_contains(some_rmq.controller_owner_ref()));
                        }
                    }
                    match step {
                        Step::ControllerStep((id, _, _)) => {
                            if id == controller_id {
                                assert(rmq_guarantee(controller_id)(s_prime));
                            } else {
                                assert(msg.src.is_controller_id(id));
                                assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                assert(rmq_rely(id)(s_prime));
                                if msg.content is APIRequest {
                                    match (msg.content->APIRequest_0) {
                                        APIRequest::CreateRequest(req) => {
                                            assert(rmq_rely_create_req(req));
                                        },
                                        APIRequest::UpdateRequest(req) => {
                                            if s.resources().contains_key(resource_key)
                                                && resource_update_request_msg(resource_key)(msg) 
                                                && req.obj.metadata.resource_version is Some {}
                                        },
                                        APIRequest::DeleteRequest(req) => {
                                            if s.resources().contains_key(resource_key)
                                                && resource_delete_request_msg(resource_key)(msg)
                                                && req.preconditions is Some
                                                && req.preconditions->0.resource_version is Some {}
                                        },
                                        APIRequest::UpdateStatusRequest(req) => {
                                            if s.resources().contains_key(resource_key)
                                                && resource_update_status_request_msg(resource_key)(msg) 
                                                && req.obj.metadata.resource_version is Some {}
                                        },
                                        APIRequest::GetThenDeleteRequest(req) => {
                                            if s.resources().contains_key(resource_key)
                                                && resource_get_then_delete_request_msg(resource_key)(msg)
                                                && req.owner_ref.controller == Some(true)
                                                && etcd_obj.metadata.owner_references_contains(req.owner_ref) {
                                                assert(req.owner_ref != rabbitmq.controller_owner_ref());
                                                lemma_singleton_contains_at_most_one_element(
                                                    etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()), req.owner_ref, rabbitmq.controller_owner_ref()
                                                );
                                            }
                                        },
                                        APIRequest::GetThenUpdateRequest(req) => {
                                            if s.resources().contains_key(resource_key)
                                                && resource_get_then_update_request_msg(resource_key)(msg)
                                                && req.owner_ref.controller == Some(true)
                                                && etcd_obj.metadata.owner_references_contains(req.owner_ref) {
                                                assert(req.owner_ref != rabbitmq.controller_owner_ref());
                                                lemma_singleton_contains_at_most_one_element(
                                                    etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()), req.owner_ref, rabbitmq.controller_owner_ref()
                                                );
                                            }
                                        },
                                        APIRequest::GetThenUpdateStatusRequest(req) => {
                                            if s.resources().contains_key(resource_key)
                                                && resource_get_then_update_status_request_msg(resource_key)(msg)
                                                && req.owner_ref.controller == Some(true)
                                                && etcd_obj.metadata.owner_references_contains(req.owner_ref)
                                                && resource_key.kind == Kind::ConfigMapKind {
                                                assert(req.owner_ref != rabbitmq.controller_owner_ref());
                                                lemma_singleton_contains_at_most_one_element(
                                                    etcd_obj.metadata.owner_references->0.filter(controller_owner_filter()), req.owner_ref, rabbitmq.controller_owner_ref()
                                                );
                                            }
                                        },
                                        _ => {},
                                    }
                                }
                            }
                        },
                        _ => {}
                    }
                } else {
                    match step {
                        Step::APIServerStep(msg_opt) => {
                            let req_msg = msg_opt->0;
                            match msg.src {
                                HostId::Controller(id, _) => {
                                    if id == controller_id { // guarantee
                                    } else { // rely
                                        assume(false);
                                    }
                                },
                                _ => {}
                            }
                        },
                        _ => {}
                    }
                }
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
    always_and_equality(lift_state(p), lift_state(q));
    temp_pred_equality(lift_state(inv), lift_state(p).and(lift_state(q)));
    entails_and_temp(spec, always(lift_state(p)), always(lift_state(q)));
}

pub open spec fn resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers_nor_deletion_timestamp(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = rabbitmq.object_ref();
        let resource_key = get_request(sub_resource, rabbitmq).key;
        forall |msg: Message| {
            #[trigger] s.in_flight().contains(msg) ==> {
                &&& resource_get_then_update_request_msg(resource_key)(msg)
                    ==> msg.content.get_get_then_update_request().obj.metadata.finalizers is None
                        && msg.content.get_get_then_update_request().obj.metadata.deletion_timestamp is None
                        && exists |uid: Uid| #![auto]
                            msg.content.get_get_then_update_request().obj.metadata.owner_references == Some(seq![
                                make_owner_references_with_name_and_uid(key.name, uid)
                            ])
                &&& resource_create_request_msg(resource_key)(msg)
                    ==> msg.content.get_create_request().obj.metadata.finalizers is None
                        && exists |uid: Uid| #![auto]
                            msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                                make_owner_references_with_name_and_uid(key.name, uid)
                            ])
            }
        }
    }
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(200))]
proof fn lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers_nor_deletion_timestamp(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(always(lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers_nor_deletion_timestamp(sub_resource, rabbitmq)))),
{
    let inv = resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers_nor_deletion_timestamp(sub_resource, rabbitmq);
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
    };
    let resource_key = get_request(sub_resource, rabbitmq).key;
    cluster.lemma_always_every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_cr_states_are_unmarshallable::<RabbitmqReconciler, RabbitmqReconcileState, RabbitmqClusterView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(spec, controller_id);
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );
    let create_msg_pred = |msg: Message| {
        resource_create_request_msg(resource_key)(msg)
        ==> msg.content.get_create_request().obj.metadata.finalizers is None
            && exists |uid: Uid| #![auto]
                msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                    make_owner_references_with_name_and_uid(rabbitmq.object_ref().name, uid)
                ])
    };
    let update_msg_pred = |msg: Message| {
        resource_get_then_update_request_msg(resource_key)(msg)
        ==> msg.content.get_get_then_update_request().obj.metadata.finalizers is None
            && msg.content.get_get_then_update_request().obj.metadata.deletion_timestamp is None
            && exists |uid: Uid| #![auto]
                msg.content.get_get_then_update_request().obj.metadata.owner_references == Some(seq![
                    make_owner_references_with_name_and_uid(rabbitmq.object_ref().name, uid)
                ])
    };
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) implies update_msg_pred(msg) && create_msg_pred(msg) by {
            if !s.in_flight().contains(msg) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep((id, _, cr_key_opt)) => {
                        if id == controller_id {
                            RabbitmqClusterView::marshal_preserves_integrity();
                            RabbitmqReconcileState::marshal_preserves_integrity();
                            let cr_key = cr_key_opt->0;
                            let cr = RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                            let local_state = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            if resource_create_request_msg(resource_key)(msg) {
                                lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                                assert(cr.object_ref() == rabbitmq.object_ref());
                                assert(msg.content.get_create_request().obj == make(sub_resource, cr, local_state)->Ok_0);
                                assert(msg.content.get_create_request().obj.metadata.finalizers is None);
                                assert(msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                                    make_owner_references_with_name_and_uid(cr_key.name, cr.metadata().uid->0)
                                ]));
                            }
                            if resource_get_then_update_request_msg(resource_key)(msg) {
                                lemma_resource_get_then_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                                assert(cr.object_ref() == rabbitmq.object_ref());
                                assert(step->ControllerStep_0.1->0.content.is_get_response());
                                assert(step->ControllerStep_0.1->0.content.get_get_response().res is Ok);
                                assert(update(
                                    sub_resource, cr, local_state, step->ControllerStep_0.1->0.content.get_get_response().res->Ok_0
                                ) is Ok);
                                assert(msg.content.get_get_then_update_request().obj == update(
                                    sub_resource, cr, local_state, step->ControllerStep_0.1->0.content.get_get_response().res->Ok_0
                                )->Ok_0);
                                assert(msg.content.get_get_then_update_request().obj.metadata.owner_references == Some(seq![
                                    make_owner_references_with_name_and_uid(cr_key.name, cr.metadata().uid->0)
                                ]));
                                assert(msg.content.get_get_then_update_request().obj.metadata.finalizers is None);
                                assert(msg.content.get_get_then_update_request().obj.metadata.deletion_timestamp is None);
                            }
                        } else {
                            if resource_create_request_msg(resource_key)(msg) || resource_get_then_update_request_msg(resource_key)(msg) {
                                assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                assert(rmq_rely(id)(s_prime));
                                assert(false);
                            }
                        }
                    },
                    _ => {},
                }

            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// This lemma is used to show that if an action (which transfers the state from s to s_prime) creates a sub resource object
// create/update request message (with key as key), it must be a controller action, and the triggering cr is s.ongoing_reconciles(controller_id)[key].triggering_cr.
//
// After the action, the controller stays at After(Create/Update, SubResource) step.
//
// Tips: Talking about both s and s_prime give more information to those using this lemma and also makes the verification faster.

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
pub proof fn lemma_resource_get_then_update_request_msg_implies_key_in_reconcile_equals(controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, s: ClusterState, s_prime: ClusterState, msg: Message, step: Step)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id) ==> #[trigger] rmq_rely(other_id)(s_prime),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        cluster.next_step(s, s_prime, step),
        resource_get_then_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg),
    ensures
        step is ControllerStep,
        step->ControllerStep_0.0 == controller_id,
        step->ControllerStep_0.2->0 == rabbitmq.object_ref(),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s_prime),
        Cluster::pending_req_msg_is(controller_id, s_prime, rabbitmq.object_ref(), msg),
{
    // Since we know that this step creates a create server config map message, it is easy to see that it's a controller action.
    // This action creates a config map, and there are two kinds of config maps, we have to show that only server config map
    // is possible by extra reasoning about the strings.
    assert(step is ControllerStep);
    let (id, _, cr_key_opt) = step->ControllerStep_0;
    if id != controller_id { // other controller, call rely condition
        assert(cluster.controller_models.remove(controller_id).contains_key(id));
        // rmq_rely(other_id)(s_prime): msg IS in s_prime.in_flight(), so rely applies
        assert(rmq_rely(id)(s_prime));
        assert(!resource_get_then_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
        assert(false);
    }
    let cr_key = cr_key_opt->0;
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    RabbitmqReconcileState::marshal_preserves_integrity();
    assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
    let local_step = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    let local_step_prime = RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    assert(local_step is AfterKRequestStep && local_step->AfterKRequestStep_0 == ActionKind::Get);
    match local_step_prime {
        RabbitmqReconcileStep::AfterKRequestStep(action, res) => {
            match action {
                ActionKind::Update => {},
                _ => {
                    assert(!msg.content.is_get_then_update_request());
                    assert(!resource_get_then_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
                },
            }
        },
        _ => {}
    }
    assert(local_step_prime is AfterKRequestStep && local_step_prime->AfterKRequestStep_0 == ActionKind::Update);
    // It's easy for the verifier to know that cr_key has the same kind and namespace as key.
    // We use two helper lemmas:
    // 1. lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key: eliminates the "wrong sub-resource"
    //    case for sub-resources sharing the same Kind (e.g., PluginsConfigMap vs ServerConfigMap).
    // 2. lemma_cr_name_neq_implies_resource_key_name_neq (contrapositive): if the resource key names
    //    are equal, then cr_key.name == key.name.
    let local_step_sub_resource = local_step->AfterKRequestStep_1;
    // Eliminate the case where the controller creates a different sub-resource type.
    if local_step_sub_resource != sub_resource {
        lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key(cr_key, key, local_step_sub_resource, sub_resource);
    }
    // Now local_step_sub_resource == sub_resource. Prove cr_key.name == key.name by contrapositive.
    match sub_resource {
        SubResource::ServerConfigMap => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server-conf"@);
            }
        },
        SubResource::PluginsConfigMap => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-plugins-conf"@);
            }
        },
        SubResource::ErlangCookieSecret => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-erlang-cookie"@);
            }
        },
        SubResource::DefaultUserSecret => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-default-user"@);
            }
        },
        SubResource::HeadlessService => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-nodes"@);
            }
        },
        SubResource::Service => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-client"@);
            }
        },
        SubResource::RoleBinding | SubResource::ServiceAccount | SubResource::VStatefulSetView => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server"@);
            }
        },
        SubResource::Role => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-peer-discovery"@);
            }
        },
    }
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
pub proof fn lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, s: ClusterState, s_prime: ClusterState, msg: Message, step: Step)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id) ==> #[trigger] rmq_rely(other_id)(s_prime),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        cluster.next_step(s, s_prime, step),
        resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg),
    ensures
        step is ControllerStep,
        step->ControllerStep_0.0 == controller_id,
        step->ControllerStep_0.2->0 == rabbitmq.object_ref(),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s_prime),
        Cluster::pending_req_msg_is(controller_id, s_prime, rabbitmq.object_ref(), msg),
{
    // Since we know that this step creates a sub resource create request message, it is easy to see that it's a controller action.
    // This action creates a resource, and there may be sub-resources sharing the same Kind, so we have to show that only the correct sub-resource
    // is possible by extra reasoning about the strings.
    assert(step is ControllerStep);
    let (id, _, cr_key_opt) = step->ControllerStep_0;

    if id != controller_id { // other controller, call rely condition
        assert(cluster.controller_models.remove(controller_id).contains_key(id));
        // rmq_rely(other_id)(s_prime): msg IS in s_prime.in_flight(), so rely applies
        assert(rmq_rely(id)(s_prime));
        assert(!resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
        assert(false);
    }
    let cr_key = cr_key_opt->0;
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    RabbitmqReconcileState::marshal_preserves_integrity();
    assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
    let local_step = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    let local_step_prime = RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    assert(local_step is AfterKRequestStep && local_step->AfterKRequestStep_0 == ActionKind::Get);
    match local_step_prime {
        RabbitmqReconcileStep::AfterKRequestStep(action, res) => {
            match action {
                ActionKind::Create => {},
                _ => {
                    assert(!msg.content.is_create_request());
                    assert(!resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
                },
            }
        },
        _ => {}
    }
    assert(local_step_prime is AfterKRequestStep && local_step_prime->AfterKRequestStep_0 == ActionKind::Create);
    // It's easy for the verifier to know that cr_key has the same kind and namespace as key.
    // We use two helper lemmas:
    // 1. lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key: eliminates the "wrong sub-resource"
    //    case for sub-resources sharing the same Kind (e.g., PluginsConfigMap vs ServerConfigMap).
    // 2. lemma_cr_name_neq_implies_resource_key_name_neq (contrapositive): if the resource key names
    //    are equal, then cr_key.name == key.name.
    let local_step_sub_resource = local_step->AfterKRequestStep_1;
    // Eliminate the case where the controller creates a different sub-resource type.
    if local_step_sub_resource != sub_resource {
        lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key(cr_key, key, local_step_sub_resource, sub_resource);
    }
    // Now local_step_sub_resource == sub_resource. Prove cr_key.name == key.name by contrapositive.
    match sub_resource {
        SubResource::ServerConfigMap => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server-conf"@);
            }
        },
        SubResource::PluginsConfigMap => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-plugins-conf"@);
            }
        },
        SubResource::ErlangCookieSecret => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-erlang-cookie"@);
            }
        },
        SubResource::DefaultUserSecret => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-default-user"@);
            }
        },
        SubResource::HeadlessService => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-nodes"@);
            }
        },
        SubResource::Service => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-client"@);
            }
        },
        SubResource::RoleBinding | SubResource::ServiceAccount | SubResource::VStatefulSetView => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server"@);
            }
        },
        SubResource::Role => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-peer-discovery"@);
            }
        },
    }
}

pub proof fn lemma_eventually_always_no_delete_resource_request_msg_in_flight_forall(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(res, rabbitmq)), sub_resource);
        lemma_eventually_always_no_delete_resource_request_msg_in_flight(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
proof fn lemma_eventually_always_no_delete_resource_request_msg_in_flight(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let requirements = |msg: Message, s: ClusterState| !{
        resource_delete_request_msg(resource_key)(msg)
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(rabbitmq)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
    };
    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.in_flight().contains(msg) {
                assert(requirements(msg, s));
                assert(requirements(msg, s_prime));
            } else {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::BuiltinControllersStep(_) => {
                        if s.resources().contains_key(resource_key) {
                            assert(cluster.etcd_object_is_well_formed(key)(s));
                            let owner_refs = s.resources()[resource_key].metadata.owner_references;
                            assert(owner_refs == Some(seq![rabbitmq.controller_owner_ref()]));
                            assert(owner_reference_to_object_reference(owner_refs->0[0], key.namespace) == key);
                        }
                    },
                    Step::ControllerStep(input) => {
                        let other_id = input.0;
                        let cr_key = input.2->0;
                        if other_id == controller_id {
                            if s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg is Some {
                                assert(msg == s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0);
                                assert(!s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0.content.is_delete_request());
                            }
                            assert(requirements(msg, s_prime));
                        } else {
                            assert(cluster.controller_models.remove(controller_id).contains_key(other_id));
                            assert(rmq_rely(other_id)(s_prime));
                            if msg.content is APIRequest {
                                match (msg.content->APIRequest_0) {
                                    APIRequest::CreateRequest(req) => {
                                        if resource_create_request_msg(resource_key)(msg) {
                                            assert(!is_rmq_managed_kind(req.key().kind));
                                            assert(false);
                                        }
                                    },
                                    APIRequest::UpdateRequest(req) => {
                                        if resource_get_then_update_request_msg(resource_key)(msg) {
                                            assert(!is_rmq_managed_kind(req.key().kind));
                                            assert(false);
                                        }
                                    },
                                    APIRequest::GetThenUpdateRequest(req) => {
                                        if resource_get_then_update_request_msg(resource_key)(msg) {
                                            assert(!is_rmq_managed_kind(req.key().kind));
                                            assert(false);
                                        }
                                    },
                                    APIRequest::DeleteRequest(req) => {
                                        if resource_delete_request_msg(resource_key)(msg) {
                                            assert(!is_rmq_managed_kind(req.key().kind));
                                            assert(false);
                                        }
                                    },
                                    APIRequest::GetThenDeleteRequest(req) => {
                                        if resource_get_then_delete_request_msg(resource_key)(msg) {
                                            assert(!is_rmq_managed_kind(req.key().kind));
                                            assert(false);
                                        }
                                    },
                                    APIRequest::UpdateStatusRequest(req) => {
                                        if resource_update_status_request_msg(resource_key)(msg) {
                                            assert(!is_rmq_managed_kind(req.key().kind));
                                            assert(false);
                                        }
                                    },
                                    APIRequest::GetThenUpdateStatusRequest(req) => {
                                        if resource_get_then_update_status_request_msg(resource_key)(msg) {
                                            assert(!is_rmq_managed_kind(req.key().kind));
                                            assert(false);
                                        }
                                    },
                                    // Get/List requests do not interfere
                                    _ => {},
                                }
                            }
                            assert(requirements(msg, s_prime));
                        }
                    },
                    _ => {
                        assert(requirements(msg, s_prime));
                    }
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    invariant_n!(spec,
        lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        later(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_delete_resource_request_msg_in_flight(sub_resource, rabbitmq)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr_forall(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource|lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource|lift_state(no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource|lift_state(no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| (lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_create_resource_request_msg_without_name_in_flight(res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_interfering_requests_in_flight(res, controller_id, rabbitmq)), sub_resource);
        lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))),
{
    let key = get_request(sub_resource, rabbitmq).key;
    let eventual_owner_ref = |owner_ref: Option<Seq<OwnerReferenceView>>| {owner_ref == Some(seq![rabbitmq.controller_owner_ref()])};
    assert forall |s: ClusterState|
        #[trigger] object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)(s)
        && no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq)(s)
        implies Cluster::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)(s) by {
        assert forall |msg: Message| s.in_flight().contains(msg) && #[trigger] resource_get_then_update_request_msg(key)(msg)
            implies eventual_owner_ref(msg.content.get_get_then_update_request().obj.metadata.owner_references) by {
        }
        assert forall |msg: Message| s.in_flight().contains(msg) && #[trigger] resource_get_then_update_request_msg(key)(msg)
            implies eventual_owner_ref(msg.content.get_get_then_update_request().obj.metadata.owner_references) by {
            assert(!resource_get_then_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
        }
    }
    assert(spec.entails(always(
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq))
        .and(lift_state(no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq)))
    ))) by {
        entails_and_temp(spec,
            always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq))),
            always(lift_state(no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq)))
        );
        always_and_equality(
            lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)),
            lift_state(no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq))
        );
    }
    always_weaken(spec,
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq))
            .and(lift_state(no_interfering_requests_in_flight(sub_resource, controller_id, rabbitmq))),
        lift_state(Cluster::every_update_msg_sets_owner_references_as(key, eventual_owner_ref))
    );
    always_weaken(spec, lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)), lift_state(Cluster::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)));
    always_weaken(spec, lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)), lift_state(Cluster::object_has_no_finalizers(key)));
    always_weaken(spec, lift_state(no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)), lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(key, eventual_owner_ref)));

    let state = |s: ClusterState| {
        Cluster::desired_state_is(rabbitmq)(s)
        && resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)(s)
    };
    invariant_n!(
        spec, lift_state(state), lift_state(Cluster::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(Cluster::garbage_collector_deletion_enabled(key))),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq))
    );
    cluster.lemma_eventually_objects_owner_references_satisfies(spec, key, eventual_owner_ref);
    temp_pred_equality(
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)),
        lift_state(Cluster::objects_owner_references_satisfies(key, eventual_owner_ref))
    );
}

pub proof fn leads_to_always_tla_forall_subresource(spec: TempPred<ClusterState>, p: TempPred<ClusterState>, a_to_p: spec_fn(SubResource)->TempPred<ClusterState>)
    requires forall |a: SubResource| spec.entails(p.leads_to(always(#[trigger] a_to_p(a)))),
    ensures spec.entails(p.leads_to(always(tla_forall(a_to_p)))),
{
    leads_to_always_tla_forall(
        spec, p, a_to_p,
        set![SubResource::HeadlessService, SubResource::Service, SubResource::ErlangCookieSecret, SubResource::DefaultUserSecret,
        SubResource::PluginsConfigMap, SubResource::ServerConfigMap, SubResource::ServiceAccount, SubResource::Role,
        SubResource::RoleBinding, SubResource::VStatefulSetView]
    );
}

// We can probably hide a lot of spec functions to make this lemma faster
#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
pub proof fn lemma_always_no_create_resource_request_msg_without_name_in_flight(cluster: Cluster, controller_id: int, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(always(lift_state(no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)))),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let inv = no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
    };
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    combine_spec_entails_always_n!(spec,
        lift_action(stronger_next),
        lift_action(cluster.next()),
        later(lift_state(rmq_rely_conditions(cluster, controller_id))),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())
    );

    assert forall |s: ClusterState, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: Message| #[trigger] s_prime.in_flight().contains(msg) implies !resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg) by {
            if !s.in_flight().contains(msg) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep((id, _, _)) => {
                        if id == controller_id {
                            assert(!resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg));
                        } else {
                            assert(msg.src.is_controller_id(id));
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(rmq_rely(id)(s_prime));
                            if msg.content.is_create_request() {
                                if resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg) {
                                    assert(!is_rmq_managed_kind(resource_key.kind));
                                    assert(false);
                                }
                            }
                        }
                    },
                    _ => {},
                }
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
pub proof fn lemma_always_there_is_no_request_msg_to_external_from_controller(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>,
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
{
    let inv = Cluster::there_is_no_request_msg_to_external_from_controller(controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    RabbitmqReconcileState::marshal_preserves_integrity();
    RabbitmqClusterView::marshal_preserves_integrity();
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime)
        implies inv(s_prime) by {
        let new_msgs = s_prime.in_flight().sub(s.in_flight());
        assert forall |msg: Message|
            inv(s)
            && #[trigger] s_prime.in_flight().contains(msg)
            && msg.src.is_controller_id(controller_id)
            implies msg.dst != HostId::External(controller_id) by {
            if s.in_flight().contains(msg) {}
            if new_msgs.contains(msg) {}
        }
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

pub open spec fn sts_create_request_msg_has_correct_selector_with_rabbitmq_name(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let sts_key = make_stateful_set_key(rabbitmq);
        forall |msg: Message| s.in_flight().contains(msg) && resource_create_request_msg(sts_key)(msg)
        ==> {
            let sts = VStatefulSetView::unmarshal(msg.content.get_create_request().obj)->Ok_0;
            &&& VStatefulSetView::unmarshal(msg.content.get_create_request().obj) is Ok
            &&& sts.spec.selector == LabelSelectorView::default().with_match_labels(Map::empty().insert("app"@, rabbitmq.metadata.name->0))
        }
    }
}

pub proof fn lemma_always_sts_create_request_msg_has_correct_selector_with_rabbitmq_name(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(always(lift_state(sts_create_request_msg_has_correct_selector_with_rabbitmq_name(rabbitmq)))),
{
    let sts_key = make_stateful_set_key(rabbitmq);
    let inv = sts_create_request_msg_has_correct_selector_with_rabbitmq_name(rabbitmq);
    let requirements = |msg: Message| resource_create_request_msg(sts_key)(msg)
    ==> {
        let sts = VStatefulSetView::unmarshal(msg.content.get_create_request().obj)->Ok_0;
        &&& VStatefulSetView::unmarshal(msg.content.get_create_request().obj) is Ok
        &&& sts.spec.selector == LabelSelectorView::default().with_match_labels(Map::empty().insert("app"@, rabbitmq.metadata.name->0))
    };
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
    };
    cluster.lemma_always_every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_cr_states_are_unmarshallable::<RabbitmqReconciler, RabbitmqReconcileState, RabbitmqClusterView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(spec, controller_id);
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) implies requirements(msg) by {
            if !s.in_flight().contains(msg) && resource_create_request_msg(sts_key)(msg) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep((id, _, cr_key_opt)) => {
                        if id == controller_id {
                            RabbitmqClusterView::marshal_preserves_integrity();
                            RabbitmqReconcileState::marshal_preserves_integrity();
                            VStatefulSetView::marshal_preserves_integrity();
                            let cr_key = cr_key_opt->0;
                            let cr = RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                            let local_state = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, SubResource::VStatefulSetView, rabbitmq, s, s_prime, msg, step);
                            assert(cr.object_ref() == rabbitmq.object_ref());
                            assert(msg.content.get_create_request().obj == make(SubResource::VStatefulSetView, cr, local_state)->Ok_0);
                            assert(msg.content.get_create_request().obj.metadata.finalizers is None);
                            assert(msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                                make_owner_references_with_name_and_uid(cr_key.name, cr.metadata().uid->0)
                            ]));
                        } else {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(rmq_rely(id)(s_prime));
                            assert(false);
                        }
                    },
                    _ => {}
                }
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// similar to resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref
#[verifier(spinoff_prover)]
#[verifier(rlimit(50))]
pub proof fn lemma_always_sts_in_etcd_with_rmq_key_match_rmq_selector(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(sts_in_etcd_with_rmq_key_match_rmq_selector(rabbitmq)))),
{
    let sts_key = make_stateful_set_key(rabbitmq);
    let inv = sts_in_etcd_with_rmq_key_match_rmq_selector(rabbitmq);
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s_prime)
        &&& no_create_resource_request_msg_without_name_in_flight(SubResource::VStatefulSetView, rabbitmq)(s)
        &&& no_interfering_requests_in_flight(SubResource::VStatefulSetView, controller_id, rabbitmq)(s)
        &&& sts_create_request_msg_has_correct_selector_with_rabbitmq_name(rabbitmq)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
    };
    cluster.lemma_always_every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_cr_states_are_unmarshallable::<RabbitmqReconciler, RabbitmqReconcileState, RabbitmqClusterView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>(spec);
    lemma_always_no_create_resource_request_msg_without_name_in_flight(cluster, controller_id, spec, SubResource::VStatefulSetView, rabbitmq);
    lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref_and_no_interfering_requests_in_flight(controller_id, cluster, spec, SubResource::VStatefulSetView, rabbitmq);
    lemma_always_sts_create_request_msg_has_correct_selector_with_rabbitmq_name(controller_id, cluster, spec, rabbitmq);
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    always_to_always_later(spec, lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        later(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>())),
        lift_state(no_create_resource_request_msg_without_name_in_flight(SubResource::VStatefulSetView, rabbitmq)),
        lift_state(no_interfering_requests_in_flight(SubResource::VStatefulSetView, controller_id, rabbitmq)),
        lift_state(sts_create_request_msg_has_correct_selector_with_rabbitmq_name(rabbitmq)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                match msg.content->APIRequest_0 {
                    APIRequest::CreateRequest(req) => {
                        assert(!resource_create_request_msg_without_name(sts_key.kind, sts_key.namespace)(msg));
                        if req.obj.metadata.name is Some {
                            if !s.resources().contains_key(sts_key)
                                && resource_create_request_msg(sts_key)(msg)
                                && s_prime.resources().contains_key(sts_key) {
                                VStatefulSetView::marshal_preserves_integrity();
                            }
                        } else if req.obj.kind == sts_key.kind && req.namespace == sts_key.namespace {
                            assert(req.obj.metadata.generate_name is None);
                        }
                    },
                    APIRequest::UpdateRequest(req) => {
                        if resource_get_then_update_request_msg(sts_key)(msg) {
                            // by transition validation
                        } else {
                            assert(req.key() != sts_key);
                        }
                    },
                    _ => {}
                }
            },
            _ => {},
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

}
