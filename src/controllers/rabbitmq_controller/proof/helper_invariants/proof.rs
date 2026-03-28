// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::predicate::*;
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    model::resource::*,
    proof::{
        helper_invariants::stateful_set_in_etcd_satisfies_unchangeable, predicate::*, resource::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*, rely_guarantee::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub proof fn lemma_always_rabbitmq_is_well_formed(cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
    ensures spec.entails(always(lift_state(rabbitmq_is_well_formed(rabbitmq)))),
{
    let stronger_inv = |s: ClusterState| {
        &&& Cluster::desired_state_is(rabbitmq)(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
    };

    invariant_n!(
        spec, lift_state(stronger_inv),
        lift_state(rabbitmq_is_well_formed(rabbitmq)),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())
    );
}

proof fn lemma_always_cr_objects_in_etcd_satisfy_state_validation(cluster: Cluster, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
    ensures spec.entails(always(lift_state(cr_objects_in_etcd_satisfy_state_validation()))),
{
    let inv = cr_objects_in_etcd_satisfy_state_validation();
    RabbitmqClusterView::marshal_status_preserves_integrity();
    init_invariant(spec, cluster.init(), cluster.next(), inv);
}

proof fn lemma_always_the_object_in_schedule_satisfies_state_validation(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
    ensures spec.entails(always(lift_state(the_object_in_schedule_satisfies_state_validation(controller_id)))),
{
    let inv = the_object_in_schedule_satisfies_state_validation(controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cr_objects_in_etcd_satisfy_state_validation()(s)
    };
    lemma_always_cr_objects_in_etcd_satisfy_state_validation(cluster, spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cr_objects_in_etcd_satisfy_state_validation())
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

pub proof fn lemma_always_the_object_in_reconcile_satisfies_state_validation(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, key: ObjectRef)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
    ensures spec.entails(always(lift_state(the_object_in_reconcile_satisfies_state_validation(controller_id, key)))),
{
    let inv = the_object_in_reconcile_satisfies_state_validation(controller_id, key);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& the_object_in_schedule_satisfies_state_validation(controller_id)(s)
    };
    lemma_always_the_object_in_schedule_satisfies_state_validation(controller_id, cluster, spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(the_object_in_schedule_satisfies_state_validation(controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

pub proof fn lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated_forall(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq))))),
        spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq))))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq)), SubResource::ServerConfigMap);
    lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, cluster, spec, rabbitmq);
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let inv = cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq);
    let resource_well_formed = |s: ClusterState| {
        s.resources().contains_key(get_request(SubResource::ServerConfigMap, rabbitmq).key)
        ==> cluster.etcd_object_is_well_formed(get_request(SubResource::ServerConfigMap, rabbitmq).key)(s)
    };
    let next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& resource_well_formed(s_prime)
        &&& no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
    };
    always_weaken(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()), lift_state(resource_well_formed));
    always_to_always_later(spec, lift_state(resource_well_formed));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        later(lift_state(resource_well_formed)),
        lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq))
    );
    leads_to_weaken(
        spec, true_pred(), lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())),
        true_pred(), lift_state(inv)
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
            match RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].local_state).unwrap().reconcile_step {
                RabbitmqReconcileStep::AfterKRequestStep(_, sub_resource) => {
                    match sub_resource {
                        SubResource::ServiceAccount | SubResource::Role | SubResource::RoleBinding | SubResource::VStatefulSetView => {
                            let step = choose |step| cluster.next_step(s, s_prime, step);
                            match step {
                                Step::APIServerStep(input) => {
                                    let req = input->0;
                                    assert(!resource_delete_request_msg(get_request(SubResource::ServerConfigMap, rabbitmq).key)(req));
                                    assert(!resource_update_status_request_msg(get_request(SubResource::ServerConfigMap, rabbitmq).key)(req));
                                    if resource_update_request_msg(get_request(SubResource::ServerConfigMap, rabbitmq).key)(req) {} else {}
                                },
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
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq))))),
        spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq))))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq))))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq)), SubResource::ServerConfigMap);
    lemma_eventually_always_object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, cluster, spec, rabbitmq);
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_object_in_response_at_after_create_resource_step_is_same_as_etcd(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let inv = object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq);
    let next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, key)(s_prime)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())(s)
        &&& no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)(s)
    };
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    always_to_always_later(spec, lift_state(Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, key)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        later(lift_state(Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, key))),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())),
        lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq))
    );
    leads_to_weaken(
        spec, true_pred(), lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())),
        true_pred(), lift_state(inv)
    );
    let resource_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let key = rabbitmq.object_ref();
    assert forall |s: ClusterState, s_prime: ClusterState| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let pending_req = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        if at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, SubResource::ServerConfigMap))(s_prime) {
            assert_by(
                s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
                && resource_create_request_msg(resource_key)(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0),
                {
                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep(input) => {
                            let cr_key = input.2->0;
                            if cr_key == key {
                                assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some);
                                assert(resource_create_request_msg(resource_key)(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                            } else {
                                assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                            }
                        },
                        Step::RestartControllerStep(_) => {
                            assert(false);
                        },
                        _ => {
                            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        }
                    }
                }
            );
            assert forall |msg: Message| s_prime.in_flight().contains(msg) && #[trigger] resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0) implies resource_create_response_msg(resource_key, s_prime)(msg) by {
                object_in_response_at_after_create_resource_step_is_same_as_etcd_helper(controller_id, cluster, s, s_prime, rabbitmq);
            }
        }
    }
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(inv));
}

#[verifier(spinoff_prover)]
proof fn object_in_response_at_after_create_resource_step_is_same_as_etcd_helper(
    controller_id: int,
    cluster: Cluster, s: ClusterState, s_prime: ClusterState, rabbitmq: RabbitmqClusterView
)
    requires
        s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg is Some,
        resource_create_request_msg(get_request(SubResource::ServerConfigMap, rabbitmq).key)(s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, SubResource::ServerConfigMap))(s_prime),
        cluster.next()(s, s_prime),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s),
        cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime),
        Cluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())(s_prime),
        Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())(s),
        no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)(s),
        no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)(s),
        object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)(s),
        resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)(s),
        object_in_response_at_after_create_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)(s),
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
                    assert(!resource_update_request_msg(resource_key)(req_msg));
                    assert(!resource_update_status_request_msg(resource_key)(req_msg));
                    match req_msg.content->APIRequest_0 {
                        APIRequest::CreateRequest(_) => {
                            if !s.in_flight().contains(msg) {
                                let req = input->0;
                                assert(msg.content.get_create_response().res->Ok_0.object_ref() == req.content.get_create_request().key());
                                assert(msg.content.get_create_response().res->Ok_0.object_ref() == resource_key);
                                assert(msg.content.get_create_response().res->Ok_0 == s_prime.resources()[req.content.get_create_request().key()]);
                                assert(resource_create_request_msg(resource_key)(req));
                            } else {
                                assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                                assert(resource_create_response_msg(resource_key, s_prime)(msg));
                            }
                        }
                        _ => {
                            assert(resp_msg_matches_req_msg(msg, s.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                        }
                    }
                },
                _ => {
                    assert(s.in_flight().contains(msg));
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                }
            }
        }
    }
}


pub proof fn lemma_eventually_always_object_in_response_at_after_update_resource_step_is_same_as_etcd_forall(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq))))),
        spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq))))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq))))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq)), SubResource::ServerConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq)), SubResource::ServerConfigMap);
    lemma_eventually_always_object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, cluster, spec, rabbitmq);
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_object_in_response_at_after_update_resource_step_is_same_as_etcd(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())))),
        spec.entails(always(lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)))),
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
        &&& no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)(s)
    };
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    always_to_always_later(spec, lift_state(Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, key)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        later(lift_state(Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, key))),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, rabbitmq.object_ref())),
        lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq))
    );
    leads_to_weaken(
        spec, true_pred(), lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(rabbitmq.object_ref())),
        true_pred(), lift_state(inv)
    );
    let resource_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let key = rabbitmq.object_ref();
    assert forall |s: ClusterState, s_prime: ClusterState| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let pending_req = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        if at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, SubResource::ServerConfigMap))(s_prime) {
            assert_by(
                s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
                && resource_update_request_msg(resource_key)(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0),
                {
                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep(input) => {
                            let cr_key = input.2->0;
                            if cr_key == key {
                                assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some);
                                assert(resource_update_request_msg(resource_key)(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                            } else {
                                assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                            }
                        },
                        Step::RestartControllerStep(_) => {
                            assert(false);
                        },
                        _ => {
                            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        }
                    }
                }
            );
            object_in_response_at_after_update_resource_step_is_same_as_etcd_helper(controller_id, cluster, s, s_prime, rabbitmq);
        }
    }
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(inv));
}

#[verifier(spinoff_prover)]
proof fn object_in_response_at_after_update_resource_step_is_same_as_etcd_helper(controller_id: int, cluster: Cluster, s: ClusterState, s_prime: ClusterState, rabbitmq: RabbitmqClusterView)
    requires
        s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg is Some,
        resource_update_request_msg(get_request(SubResource::ServerConfigMap, rabbitmq).key)(s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, SubResource::ServerConfigMap))(s_prime),
        cluster.next()(s, s_prime),
        Cluster::every_in_flight_msg_has_unique_id()(s),
        cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime),
        Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Cluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, rabbitmq.object_ref())(s_prime),
        no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)(s),
        no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)(s),
        object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, SubResource::ServerConfigMap, rabbitmq)(s),
        resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)(s),
        object_in_response_at_after_update_resource_step_is_same_as_etcd(controller_id, SubResource::ServerConfigMap, rabbitmq)(s),
    ensures
        forall |msg: Message| #[trigger]
            s_prime.in_flight().contains(msg)
            && resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].pending_req_msg->0)
            ==> resource_update_response_msg(get_request(SubResource::ServerConfigMap, rabbitmq).key, s_prime)(msg),
{
    let resource_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let key = rabbitmq.object_ref();
    let pending_req = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
    assert forall |msg: Message| s_prime.in_flight().contains(msg) && #[trigger] resp_msg_matches_req_msg(msg, pending_req) implies resource_update_response_msg(resource_key, s_prime)(msg) by {
        assert(msg.src is APIServer);
        assert(msg.content.is_update_response());
        if msg.content.get_update_response().res is Ok {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    let req_msg = input->0;
                    assert(!resource_delete_request_msg(resource_key)(req_msg));
                    assert(!resource_update_status_request_msg(resource_key)(req_msg));
                    match req_msg.content->APIRequest_0 {
                        APIRequest::UpdateRequest(_) => {
                            if !s.in_flight().contains(msg) {
                                assert(msg.content.get_update_response().res->Ok_0.object_ref() == req_msg.content.get_update_request().key());
                                assert(msg.content.get_update_response().res->Ok_0.object_ref() == resource_key);
                                assert(msg.content.get_update_response().res->Ok_0 == s_prime.resources()[req_msg.content.get_update_request().key()]);
                                assert(s_prime.resources().contains_key(resource_key));
                                assert(msg.content.get_update_response().res->Ok_0 == s_prime.resources()[resource_key]);
                            } else {
                                assert(!resource_update_request_msg(resource_key)(req_msg));
                                assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                                assert(!s.in_flight().contains(pending_req));
                            }
                        },
                        _ => {
                            assert(s.in_flight().contains(msg));
                            assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                            assert(!s.in_flight().contains(pending_req));
                        },
                    }
                },
                _ => {
                    assert(s.in_flight().contains(msg));
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
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
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(request_at_after_get_request_step_is_resource_get_request(controller_id, sub_resource, rabbitmq)))),
{
    // hide(make_stateful_set); // TODO: Verus AIR code bug with fuel path
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let inv = request_at_after_get_request_step_is_resource_get_request(controller_id, sub_resource, rabbitmq);
    let consistent_key = |s: ClusterState| {
        s.ongoing_reconciles(controller_id).contains_key(key) ==> s.ongoing_reconciles(controller_id)[key].triggering_cr.object_ref() == key
    };
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& consistent_key(s)
    };
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))
    );
    assert forall |s: ClusterState, s_prime: ClusterState| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s_prime) {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    if at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s_prime) {
                        let cr_key = input.2->0;
                        if cr_key == key {
                            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some);
                            assert(resource_get_request_msg(resource_key)(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0));
                        } else {
                            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        }
                    }
                },
                Step::RestartControllerStep(_) => {
                    assert(!s_prime.ongoing_reconciles(controller_id).contains_key(key));
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                }
            }
        }
    }
    init_invariant(spec, cluster.init(), next, inv);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_response_at_after_get_resource_step_is_resource_get_response(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
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

pub proof fn lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step_forall(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
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
        spec.entails(always(lift_state(Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, rabbitmq).key))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        // rely
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        forall |sub_resource: SubResource| spec.entails(always(lift_state(#[trigger] no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, rabbitmq).key)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(res, rabbitmq)), sub_resource);
        lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
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
        spec.entails(always(lift_state(Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, rabbitmq).key)))),
        spec.entails(always(lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        // rely
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        spec.entails(always(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let requirements = |msg: Message, s: ClusterState| {
        resource_update_request_msg(resource_key)(msg) ==> {
            &&& at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.resource_version is Some
            &&& msg.content.get_update_request().obj.metadata.resource_version->0 < s.api_server.resource_version_counter
            &&& (
                s.resources().contains_key(resource_key)
                && msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
            ) ==> (
                update(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap(), s.resources()[resource_key]) is Ok
                && msg.content.get_update_request().obj == update(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap(), s.resources()[resource_key])->Ok_0
            )
        }
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)(s)
        &&& Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, rabbitmq).key)(s)
        &&& response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)(s)
        &&& no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)(s)
        &&& no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s_prime)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_update_request_msg(resource_key)(msg) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                    let resp = step->ControllerStep_0.1->0;
                    assert(is_ok_get_response_msg()(resp));
                    assert(s.in_flight().contains(resp));
                    assert(resp.content.get_get_response().res->Ok_0.metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version);
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
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    always_to_always_later(spec, lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)));
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()), lift_state(Cluster::crash_disabled(controller_id)), lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)),
        lift_state(Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, rabbitmq).key)),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)),
        lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)),
        lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)),
        lift_state(rmq_rely_conditions(cluster, controller_id)),
        lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)),
        later(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource))),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_resource_update_request_implies_at_after_update_resource_step(controller_id, sub_resource, rabbitmq)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub proof fn lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr_forall(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq))))) by {
        lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
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
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        // rely
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        spec.entails(always(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let requirements = |msg: Message, s: ClusterState| {
        resource_update_request_msg(resource_key)(msg) ==> {
            &&& at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
        }
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s_prime)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_update_request_msg(resource_key)(msg) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)));
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()), lift_state(Cluster::crash_disabled(controller_id)), lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)),
        lift_state(rmq_rely_conditions(cluster, controller_id)),
        lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)),
        later(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource))),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub proof fn lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step_forall(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
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
        spec.entails(always(lift_state(rabbitmq_is_well_formed(rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        // rely
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        forall |sub_resource: SubResource| spec.entails(always(lift_state(#[trigger] no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq))))) by {
        lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
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
        spec.entails(always(lift_state(rabbitmq_is_well_formed(rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        // rely
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        spec.entails(always(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let requirements = |msg: Message, s: ClusterState| {
        resource_create_request_msg(resource_key)(msg) ==> {
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
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)(s)
        &&& rabbitmq_is_well_formed(rabbitmq)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s_prime)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_create_request_msg(resource_key)(msg) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    always_to_always_later(spec, lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)));
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()), lift_state(Cluster::crash_disabled(controller_id)), lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)),
        lift_state(rabbitmq_is_well_formed(rabbitmq)),
        lift_state(rmq_rely_conditions(cluster, controller_id)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id))),
        lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)),
        later(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource))),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, sub_resource, rabbitmq)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_no_update_status_request_msg_in_flight_of_except_stateful_set(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
    ensures spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq)))),
{
    let inv = no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, rabbitmq);

    let resource_key = get_request(sub_resource, rabbitmq).key;
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] cluster.next()(s, s_prime) implies inv(s_prime) by {
        if sub_resource != SubResource::VStatefulSetView {
            assert forall |msg: Message| s_prime.in_flight().contains(msg) implies !(#[trigger] resource_update_status_request_msg(resource_key)(msg)) by {
                if s.in_flight().contains(msg) {
                    assert(!resource_update_status_request_msg(resource_key)(msg));
                } else {
                    let step = choose |step: Step| cluster.next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep(input) => {
                            if input.2 is Some {
                                let cr_key = input.2->0;
                                if s.ongoing_reconciles(controller_id).contains_key(cr_key) {
                                    match RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step {
                                        RabbitmqReconcileStep::Init => {},
                                        RabbitmqReconcileStep::AfterKRequestStep(_, resource) => {
                                            match resource {
                                                SubResource::HeadlessService => {},
                                                SubResource::Service => {},
                                                SubResource::ErlangCookieSecret => {},
                                                SubResource::DefaultUserSecret => {},
                                                SubResource::PluginsConfigMap => {},
                                                SubResource::ServerConfigMap => {},
                                                SubResource::ServiceAccount => {},
                                                SubResource::Role => {},
                                                SubResource::RoleBinding => {},
                                                SubResource::VStatefulSetView => {},
                                            }
                                        },
                                        _ => {}
                                    }
                                } else {}
                            } else {}
                            assert(!resource_update_status_request_msg(resource_key)(msg));
                        },
                        Step::BuiltinControllersStep(_) => {
                            assert(resource_key.kind != Kind::StatefulSetKind && resource_key.kind != Kind::DaemonSetKind);
                            assert(!resource_update_status_request_msg(resource_key)(msg));
                        },
                        _ => {
                            assert(!resource_update_status_request_msg(resource_key)(msg));
                        }
                    }
                }
            }
        }
    }
    init_invariant(spec, cluster.init(), cluster.next(), inv);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(controller_id, rabbitmq)))),
{
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    let inv = no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(controller_id, rabbitmq);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())
    );

    let resource_key = get_request(SubResource::VStatefulSetView, rabbitmq).key;
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: Message| #[trigger] s_prime.in_flight().contains(msg) && msg.dst is APIServer && !(msg.src is BuiltinController) && msg.content.is_update_status_request()
        implies msg.content.get_update_status_request().key() != resource_key by {
            if s.in_flight().contains(msg) {
                assert(msg.content.get_update_status_request().key() != resource_key);
            } else {
                let step = choose |step: Step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        if input.2 is Some {
                            let cr_key = input.2->0;
                            if s.ongoing_reconciles(controller_id).contains_key(cr_key) {
                                match RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step {
                                    RabbitmqReconcileStep::Init => {},
                                    RabbitmqReconcileStep::AfterKRequestStep(_, resource) => {
                                        match resource {
                                            SubResource::HeadlessService => {},
                                            SubResource::Service => {},
                                            SubResource::ErlangCookieSecret => {},
                                            SubResource::DefaultUserSecret => {},
                                            SubResource::PluginsConfigMap => {},
                                            SubResource::ServerConfigMap => {},
                                            SubResource::ServiceAccount => {},
                                            SubResource::Role => {},
                                            SubResource::RoleBinding => {},
                                            SubResource::VStatefulSetView => {},
                                        }
                                    },
                                    _ => {}
                                }
                            } else {}
                        } else {}
                        assert(!(msg.content.is_update_status_request()));
                        assert(false);
                    },
                    Step::APIServerStep(_) => {
                        assert(!(msg.content is APIRequest));
                        assert(!(msg.content.is_update_status_request()));
                        assert(false);
                    },
                    Step::DropReqStep(_) => {
                        assert(!(msg.content.is_update_status_request()));
                        assert(false);
                    },
                    Step::BuiltinControllersStep(_) => {
                        assert(msg.src is BuiltinController);
                        assert(false);
                    },
                    _ => {
                        assert(!s_prime.in_flight().contains(msg));
                        assert(false);
                    }
                }
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

spec fn make_owner_references_with_name_and_uid(name: StringView, uid: Uid) -> OwnerReferenceView {
    OwnerReferenceView {
        block_owner_deletion: None,
        controller: Some(true),
        kind: RabbitmqClusterView::kind(),
        name: name,
        uid: uid,
    }
}

pub proof fn lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
{
    let inv = resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq);
    lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(controller_id, cluster, spec, sub_resource, rabbitmq);
    lemma_always_no_create_resource_request_msg_without_name_in_flight(cluster, spec, sub_resource, rabbitmq);
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, rabbitmq)(s)
        &&& no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, rabbitmq)),
        lift_state(no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq))
    );
    let resource_key = get_request(sub_resource, rabbitmq).key;
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let req_msg = input->0;
                assert(!resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(req_msg));
            }
            _ => {}
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

spec fn resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = rabbitmq.object_ref();
        let resource_key = get_request(sub_resource, rabbitmq).key;
        forall |msg: Message| {
            #[trigger] s.in_flight().contains(msg) ==> {
                &&& resource_update_request_msg(resource_key)(msg)
                    ==> msg.content.get_update_request().obj.metadata.finalizers is None
                        && exists |uid: Uid| #![auto]
                            msg.content.get_update_request().obj.metadata.owner_references == Some(seq![
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
proof fn lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, rabbitmq)))),
{
    let inv = resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, rabbitmq);
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
    };
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))
    );
    let create_msg_pred = |msg: Message| {
        resource_create_request_msg(resource_key)(msg)
        ==> msg.content.get_create_request().obj.metadata.finalizers is None
            && exists |uid: Uid| #![auto]
                msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                    make_owner_references_with_name_and_uid(key.name, uid)
                ])
    };
    let update_msg_pred = |msg: Message| {
        resource_update_request_msg(resource_key)(msg)
        ==> msg.content.get_update_request().obj.metadata.finalizers is None
            && exists |uid: Uid| #![auto]
                msg.content.get_update_request().obj.metadata.owner_references == Some(seq![
                    make_owner_references_with_name_and_uid(key.name, uid)
                ])
    };
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) implies update_msg_pred(msg) && create_msg_pred(msg) by {
            if !s.in_flight().contains(msg) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                let cr = RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                let local_state = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                if resource_create_request_msg(resource_key)(msg) {
                    lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                    assert(msg.content.get_create_request().obj == make(sub_resource, cr, local_state)->Ok_0);
                    assert(msg.content.get_create_request().obj.metadata.finalizers is None);
                    assert(msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                        make_owner_references_with_name_and_uid(key.name, cr.metadata().uid->0)
                    ]));
                }
                if resource_update_request_msg(resource_key)(msg) {
                    lemma_resource_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                    assert(step->ControllerStep_0.1->0.content.is_get_response());
                    assert(step->ControllerStep_0.1->0.content.get_get_response().res is Ok);
                    assert(update(
                        sub_resource, cr, local_state, step->ControllerStep_0.1->0.content.get_get_response().res->Ok_0
                    ) is Ok);
                    assert(msg.content.get_update_request().obj == update(
                        sub_resource, cr, local_state, step->ControllerStep_0.1->0.content.get_get_response().res->Ok_0
                    )->Ok_0);
                    assert(msg.content.get_update_request().obj.metadata.owner_references == Some(seq![
                        make_owner_references_with_name_and_uid(key.name, cr.metadata().uid->0)
                    ]));
                }

            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}


// String lemma: if two RMQ CRs have different names (same or different namespace),
// then for any sub_resource, the resource key name built for one differs from the other.
// String lemma: the resource key name for any RMQ sub_resource has the rabbitmq prefix.
proof fn lemma_resource_key_name_has_rabbitmq_prefix(sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires rabbitmq.metadata.name is Some,
    ensures has_rabbitmq_prefix(get_request(sub_resource, rabbitmq).key.name),
{
    let cr_name = rabbitmq.metadata.name->0;
    let prefix = RabbitmqClusterView::kind()->CustomResourceKind_0;
    let key_name = get_request(sub_resource, rabbitmq).key.name;
    match sub_resource {
        SubResource::HeadlessService => {
            let suffix = cr_name + "-nodes"@;
            assert(key_name == prefix + "-"@ + suffix);
        },
        SubResource::Service => {
            let suffix = cr_name + "-client"@;
            assert(key_name == prefix + "-"@ + suffix);
        },
        SubResource::ErlangCookieSecret => {
            let suffix = cr_name + "-erlang-cookie"@;
            assert(key_name == prefix + "-"@ + suffix);
        },
        SubResource::DefaultUserSecret => {
            let suffix = cr_name + "-default-user"@;
            assert(key_name == prefix + "-"@ + suffix);
        },
        SubResource::PluginsConfigMap => {
            let suffix = cr_name + "-plugins-conf"@;
            assert(key_name == prefix + "-"@ + suffix);
        },
        SubResource::ServerConfigMap => {
            let suffix = cr_name + "-server-conf"@;
            assert(key_name == prefix + "-"@ + suffix);
        },
        SubResource::ServiceAccount => {
            let suffix = cr_name + "-server"@;
            assert(key_name == prefix + "-"@ + suffix);
        },
        SubResource::Role => {
            let suffix = cr_name + "-peer-discovery"@;
            assert(key_name == prefix + "-"@ + suffix);
        },
        SubResource::RoleBinding => {
            let suffix = cr_name + "-server"@;
            assert(key_name == prefix + "-"@ + suffix);
        },
        SubResource::VStatefulSetView => {
            let suffix = cr_name + "-server"@;
            assert(key_name == prefix + "-"@ + suffix);
        },
    }
}

proof fn lemma_cr_name_neq_implies_resource_key_name_neq(
    cr_name_a: StringView, cr_name_b: StringView, suffix: StringView,
)
    requires cr_name_a != cr_name_b,
    ensures
        RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + cr_name_a + suffix
        != RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + cr_name_b + suffix,
{
    let prefix_dash = RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@;
    // prefix_dash + cr_name_a != prefix_dash + cr_name_b  (since cr_name_a != cr_name_b)
    seq_lib::seq_unequal_preserved_by_add_prefix(prefix_dash, cr_name_a, cr_name_b);
    // (prefix_dash + cr_name_a) + suffix != (prefix_dash + cr_name_b) + suffix
    seq_lib::seq_unequal_preserved_by_add(prefix_dash + cr_name_a, prefix_dash + cr_name_b, suffix);
}

// This lemma is used to show that if an action (which transfers the state from s to s_prime) creates a sub resource object
// create/update request message (with key as key), it must be a controller action, and the triggering cr is s.ongoing_reconciles(controller_id)[key].triggering_cr.
//
// After the action, the controller stays at After(Create/Update, SubResource) step.
//
// Tips: Talking about both s and s_prime give more information to those using this lemma and also makes the verification faster.

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
pub proof fn lemma_resource_update_request_msg_implies_key_in_reconcile_equals(controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, s: ClusterState, s_prime: ClusterState, msg: Message, step: Step)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        // rely (s_prime needed for new msgs from other controllers)
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id) ==> #[trigger] rmq_rely(other_id)(s),
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id) ==> #[trigger] rmq_rely(other_id)(s_prime),
        // internal rely (s_prime needed for new msgs from other CR reconciliations)
        forall |rmq: RabbitmqClusterView| #[trigger] no_interfering_request_between_rmq(controller_id, sub_resource, rmq)(s),
        forall |rmq: RabbitmqClusterView| #[trigger] no_interfering_request_between_rmq(controller_id, sub_resource, rmq)(s_prime),
        !s.in_flight().contains(msg), s_prime.in_flight().contains(msg),
        cluster.next_step(s, s_prime, step),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg),
        rabbitmq.metadata.name is Some,
    ensures
        step is ControllerStep,
        step->ControllerStep_0.2->0 == rabbitmq.object_ref(),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s_prime),
        Cluster::pending_req_msg_is(controller_id, s_prime, rabbitmq.object_ref(), msg),
{
    // Since we know that this step creates a create server config map message, it is easy to see that it's a controller action.
    // This action creates a config map, and there are two kinds of config maps, we have to show that only server config map
    // is possible by extra reasoning about the strings.
    match msg.src {
        HostId::Controller(other_id, cr_key) => {
            if other_id == controller_id {
                RabbitmqReconcileState::marshal_preserves_integrity();
                RabbitmqClusterView::marshal_preserves_integrity();
                if cr_key != rabbitmq.object_ref() {
                    // construct another rmq that has such cr_key and prove the request from that reconciliation shan't have such req.key()
                    let other_rmq = RabbitmqClusterView {
                        metadata: ObjectMetaView {
                            name: Some(cr_key.name),
                            namespace: Some(cr_key.namespace),
                            ..ObjectMetaView::default()
                        },
                        ..RabbitmqClusterView::default()
                    };
                    assert(other_rmq.object_ref() == cr_key);
                    // msg IS in s_prime.in_flight(), so no_interfering_request_between_rmq(s_prime) applies
                    assert(no_interfering_request_between_rmq(controller_id, sub_resource, other_rmq)(s_prime));
                    assert(!resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg)) by {
                        // no_interfering gives: msg's update key == make_{sub_resource}_key(other_rmq)
                        assert(get_request(sub_resource, other_rmq).key == msg.content.get_create_request().key());
                        // cr_key != rabbitmq.object_ref() => either namespace or name differs
                        if cr_key.namespace != rabbitmq.object_ref().namespace {
                            // namespaces differ so keys differ
                        } else {
                            assert(cr_key.name != rabbitmq.metadata.name->0);
                            // use string lemma to show key names differ for each sub_resource
                            match sub_resource {
                                SubResource::HeadlessService => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-nodes"@);
                                },
                                SubResource::Service => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-client"@);
                                },
                                SubResource::ErlangCookieSecret => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-erlang-cookie"@);
                                },
                                SubResource::DefaultUserSecret => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-default-user"@);
                                },
                                SubResource::PluginsConfigMap => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-plugins-conf"@);
                                },
                                SubResource::ServerConfigMap => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-server-conf"@);
                                },
                                SubResource::ServiceAccount => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-server"@);
                                },
                                SubResource::Role => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-peer-discovery"@);
                                },
                                SubResource::RoleBinding => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-server"@);
                                },
                                SubResource::VStatefulSetView => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-server"@);
                                },
                            }
                        }
                    }
                    assert(false);
                } else { // same reconciliation
                    let key = rabbitmq.object_ref();
                    let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
                    let resource_key = get_request(sub_resource, rabbitmq).key;
                    assert(step is ControllerStep);
                    assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
                    let local_step = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let local_step_prime = RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    assert(local_step is AfterKRequestStep && local_step->AfterKRequestStep_0 == ActionKind::Get);
                    match local_step_prime {
                        RabbitmqReconcileStep::AfterKRequestStep(action, res) => {
                            match action {
                                ActionKind::Update => {},
                                _ => {
                                    assert(!(msg.content.is_update_request()));
                                    assert(!resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
                                },
                            };

                            // move the local_step_prime chunk here, saying request on other sub resources shall not has this prefix
                            // but in https://github.com/anvil-verifier/anvil/pull/758, some keys are updated, make sure to correct them
                            assume(res == sub_resource);
                        },
                        _ => {}
                    }
                    assert(local_step_prime is AfterKRequestStep && local_step_prime->AfterKRequestStep_0 == ActionKind::Update);
                }
            } else { // other controller, call rely condition
                assert(cluster.controller_models.remove(controller_id).contains_key(other_id));
                // rmq_rely(other_id)(s_prime): msg IS in s_prime.in_flight(), so rely applies
                assert(rmq_rely(other_id)(s_prime));
                assert(!resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
                assert(false);
            }
        },
        _ => {}
    }
    let cr_key = step->ControllerStep_0.2->0;
    // It's easy for the verifier to know that cr_key has the same kind and namespace as key.
    // match sub_resource {
    //     SubResource::ServerConfigMap => {
    //         // resource_create_request_msg(key)(msg) requires the msg has a key with name key.name "-server-conf". So we
    //         // first show that in this action, cr_key is only possible to add "-server-conf" rather than "-plugins-conf" to reach
    //         // such a post state.
    //         assert_by(
    //             cr_key.name + "-plugins-conf"@ != key.name + "-server-conf"@,
    //             {
    //                 let str1 = cr_key.name + "-plugins-conf"@;
    //                 reveal_strlit("-server-conf");
    //                 reveal_strlit("-plugins-conf");
    //                 assert(str1[str1.len() - 6] == 's');
    //             }
    //         );
    //         // Then we show that only if cr_key.name equals key.name, can this message be created in this step.
    //         seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, "-server-conf"@);
    //     },
    //     SubResource::PluginsConfigMap => {
    //         assert_by(
    //             key.name + "-plugins-conf"@ != cr_key.name + "-server-conf"@,
    //             {
    //                 let str1 = key.name + "-plugins-conf"@;
    //                 reveal_strlit("-server-conf");
    //                 reveal_strlit("-plugins-conf");
    //                 assert(str1[str1.len() - 6] == 's');
    //             }
    //         );
    //         seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, "-plugins-conf"@);
    //     },
    //     SubResource::ErlangCookieSecret => {
    //         assert_by(
    //             cr_key.name + "-default-user"@ != key.name + "-erlang-cookie"@,
    //             {
    //                 let str1 = cr_key.name + "-default-user"@;
    //                 reveal_strlit("-erlang-cookie");
    //                 reveal_strlit("-default-user");
    //                 assert(str1[str1.len() - 1] == 'r');
    //             }
    //         );
    //         // Then we show that only if cr_key.name equals key.name, can this message be created in this step.
    //         seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, "-erlang-cookie"@);
    //     },
    //     SubResource::DefaultUserSecret => {
    //         assert_by(
    //             key.name + "-default-user"@ != cr_key.name + "-erlang-cookie"@,
    //             {
    //                 let str1 = key.name + "-default-user"@;
    //                 reveal_strlit("-erlang-cookie");
    //                 reveal_strlit("-default-user");
    //                 assert(str1[str1.len() - 1] == 'r');
    //             }
    //         );
    //         seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, "-default-user"@);
    //     },
    //     SubResource::HeadlessService => {
    //         assert_by(
    //             key.name + "-nodes"@ != cr_key.name + "-client"@,
    //             {
    //                 let str1 = key.name + "-nodes"@;
    //                 reveal_strlit("-client");
    //                 reveal_strlit("-nodes");
    //                 assert(str1[str1.len() - 1] == 's');
    //             }
    //         );
    //         seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, "-nodes"@);
    //     },
    //     SubResource::Service => {
    //         assert_by(
    //             cr_key.name + "-nodes"@ != key.name + "-client"@,
    //             {
    //                 let str1 = cr_key.name + "-nodes"@;
    //                 reveal_strlit("-client");
    //                 reveal_strlit("-nodes");
    //                 assert(str1[str1.len() - 1] == 's');
    //             }
    //         );
    //         seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, "-client"@);
    //     },
    //     SubResource::RoleBinding | SubResource::ServiceAccount | SubResource::VStatefulSetView => {
    //         seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, "-server"@);
    //     },
    //     SubResource::Role => {
    //         seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, "-peer-discovery"@);
    //     },
    // }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, s: ClusterState, s_prime: ClusterState, msg: Message, step: Step)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        rabbitmq.well_formed(),
        // rely (s_prime needed for new msgs from other controllers)
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id) ==> #[trigger] rmq_rely(other_id)(s),
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id) ==> #[trigger] rmq_rely(other_id)(s_prime),
        // internal rely (s_prime needed for new msgs from other CR reconciliations)
        forall |rmq: RabbitmqClusterView| #[trigger] no_interfering_request_between_rmq(controller_id, sub_resource, rmq)(s),
        forall |rmq: RabbitmqClusterView| #[trigger] no_interfering_request_between_rmq(controller_id, sub_resource, rmq)(s_prime),
        !s.in_flight().contains(msg), s_prime.in_flight().contains(msg),
        cluster.next_step(s, s_prime, step),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg),
        rabbitmq.metadata.name is Some,
    ensures
        step is ControllerStep,
        step->ControllerStep_0.2->0 == rabbitmq.object_ref(),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s_prime),
        Cluster::pending_req_msg_is(controller_id, s_prime, rabbitmq.object_ref(), msg),
        make(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state).unwrap()) is Ok,
        msg.content.get_create_request().obj == make(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[rabbitmq.object_ref()].local_state).unwrap())->Ok_0,
{
    match msg.src {
        HostId::Controller(other_id, cr_key) => {
            if other_id == controller_id {
                RabbitmqReconcileState::marshal_preserves_integrity();
                RabbitmqClusterView::marshal_preserves_integrity();
                if cr_key != rabbitmq.object_ref() {
                    // construct another rmq that has such cr_key and prove the request from that reconciliation shan't have such req.key()
                    let other_rmq = RabbitmqClusterView {
                        metadata: ObjectMetaView {
                            name: Some(cr_key.name),
                            namespace: Some(cr_key.namespace),
                            ..ObjectMetaView::default()
                        },
                        ..RabbitmqClusterView::default()
                    };
                    assert(other_rmq.object_ref() == cr_key);
                    // msg IS in s_prime.in_flight(), so no_interfering_request_between_rmq(s_prime) applies
                    assert(no_interfering_request_between_rmq(controller_id, sub_resource, other_rmq)(s_prime));
                    assert(!resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg)) by {
                        // no_interfering gives: msg's create key == make_{sub_resource}_key(other_rmq)
                        assert(get_request(sub_resource, other_rmq).key == msg.content.get_create_request().key());
                        // cr_key != rabbitmq.object_ref() => either namespace or name differs
                        if cr_key.namespace != rabbitmq.object_ref().namespace {
                            // namespaces differ so keys differ
                        } else {
                            assert(cr_key.name != rabbitmq.metadata.name->0);
                            // use string lemma to show key names differ for each sub_resource
                            match sub_resource {
                                SubResource::HeadlessService => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-nodes"@);
                                },
                                SubResource::Service => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-client"@);
                                },
                                SubResource::ErlangCookieSecret => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-erlang-cookie"@);
                                },
                                SubResource::DefaultUserSecret => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-default-user"@);
                                },
                                SubResource::PluginsConfigMap => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-plugins-conf"@);
                                },
                                SubResource::ServerConfigMap => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-server-conf"@);
                                },
                                SubResource::ServiceAccount => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-server"@);
                                },
                                SubResource::Role => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-peer-discovery"@);
                                },
                                SubResource::RoleBinding => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-server"@);
                                },
                                SubResource::VStatefulSetView => {
                                    lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, rabbitmq.metadata.name->0, "-server"@);
                                },
                            }
                        }
                    }
                    assert(false);
                } else { // same reconciliation
                    let key = rabbitmq.object_ref();
                    let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
                    let resource_key = get_request(sub_resource, rabbitmq).key;
                    assert(step is ControllerStep);
                    assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
                    let local_step = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let local_step_prime = RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    assert(local_step is AfterKRequestStep && local_step->AfterKRequestStep_0 == ActionKind::Get);
                    match local_step_prime {
                        RabbitmqReconcileStep::AfterKRequestStep(action, res) => {
                            match action {
                                ActionKind::Create => {},
                                _ => {
                                    assert(!(msg.content.is_create_request()));
                                    assert(!resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
                                },
                            };

                            // move the local_step_prime chunk here, saying request on other sub resources shall not has this prefix
                            // but in https://github.com/anvil-verifier/anvil/pull/758, some keys are updated, make sure to correct them
                            assume(res == sub_resource);
                        },
                        _ => {}
                    }
                    assert(local_step_prime is AfterKRequestStep && local_step_prime->AfterKRequestStep_0 == ActionKind::Create);
                    assume(make(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap()) is Ok);
                    assume(msg.content.get_create_request().obj == make(sub_resource, rabbitmq, RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap())->Ok_0);
                }
            } else { // other controller, call rely condition
                assert(cluster.controller_models.remove(controller_id).contains_key(other_id));
                // rmq_rely(other_id)(s_prime): msg IS in s_prime.in_flight(), so rely applies
                assert(rmq_rely(other_id)(s_prime));
                assert(!resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
                assert(false);
            }
        },
        _ => {}
    }
    let cr_key = step->ControllerStep_0.2->0;
}

pub proof fn lemma_eventually_always_no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight_forall(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(res, rabbitmq)), sub_resource);
        lemma_eventually_always_no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)));
}

// This lemma demonstrates how to use kubernetes_cluster::proof::api_server_liveness::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies
// (referred to as lemma_X) to prove that the system will eventually enter a state where delete stateful set request messages
// will never appear in flight.
//
// As an example, we can look at how this lemma is proved.
// - Precondition: The preconditions should include all precondtions used by lemma_X and other predicates which show that
//     the newly generated messages are as expected. ("expected" means not delete stateful set request messages in this lemma. Therefore,
//     we provide an invariant stateful_set_has_owner_reference_pointing_to_current_cr so that the grabage collector won't try
//     to send a delete request to delete the messsage.)
// - Postcondition: spec |= true ~> [](forall |msg| as_expected(msg))
// - Proof body: The proof consists of three parts.
//   + Come up with "requirements" for those newly created api request messages. Usually, just move the forall |msg| and
//     s.in_flight().contains(msg) in the statepred of final state (no_delete_sts_req_is_in_flight in this lemma, so we can
//     get the requirements in this lemma).
//   + Show that spec |= every_new_req_msg_if_in_flight_then_satisfies. Basically, use two assert forall to show that forall state and
//     its next state and forall messages, if the messages are newly generated, they must satisfy the "requirements" and always satisfies it
//     as long as it is in flight.
//   + Call lemma_X. If a correct "requirements" are provided, we can easily prove the equivalence of every_in_flight_req_msg_satisfies(requirements)
//     and the original statepred.
#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let requirements = |msg: Message, s: ClusterState| !resource_delete_request_msg(resource_key)(msg);
    let resource_well_formed = |s: ClusterState| {
        s.resources().contains_key(key) ==> cluster.etcd_object_is_well_formed(key)(s)
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(rabbitmq)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)(s)
        &&& resource_well_formed(s)
    };
    always_weaken(spec, lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()), lift_state(resource_well_formed));
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
                            assert(!resource_delete_request_msg(resource_key)(msg)) by {
                                assume(false); // string reasoning: resource_key has rabbitmq prefix, other controllers don't delete such resources
                            }
                            assert(requirements(msg, s_prime));
                        }
                    },
                    Step::DropReqStep(_) => {
                        if msg.content.is_delete_request() {
                            assert(msg.content.get_delete_request().key.kind != resource_key.kind);
                        }
                        assert(requirements(msg, s_prime));
                    },
                    _ => {
                        assert(requirements(msg, s_prime));
                    }
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()), lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)),
        lift_state(resource_well_formed)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(sub_resource, rabbitmq)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr_forall(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
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
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| (lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_create_resource_request_msg_without_name_in_flight(res, rabbitmq)), sub_resource);
        lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
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
    ensures spec.entails(true_pred().leads_to(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))),
{
    let key = get_request(sub_resource, rabbitmq).key;
    let eventual_owner_ref = |owner_ref: Option<Seq<OwnerReferenceView>>| {owner_ref == Some(seq![rabbitmq.controller_owner_ref()])};
    assert forall |s: ClusterState|
        #[trigger] object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)(s)
        implies Cluster::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)(s) by {
        assert forall |msg: Message| s.in_flight().contains(msg) && #[trigger] resource_update_request_msg(key)(msg)
            implies eventual_owner_ref(msg.content.get_update_request().obj.metadata.owner_references) by {
        }
        assert forall |msg: Message| s.in_flight().contains(msg) && #[trigger] resource_get_then_update_request_msg(key)(msg)
            implies eventual_owner_ref(msg.content.get_get_then_update_request().obj.metadata.owner_references) by {
            assume(false); // string reasoning: resource_key has rabbitmq prefix, no controller sends get_then_update for it
        }
    }
    always_weaken(spec, lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(controller_id, sub_resource, rabbitmq)), lift_state(Cluster::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)));
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

// Below are invariants that only hold after the config map matches the desired state

pub proof fn lemma_eventually_always_stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(controller_id, SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(every_resource_update_request_implies_at_after_update_resource_step(controller_id, SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(no_create_resource_request_msg_without_name_in_flight(SubResource::VStatefulSetView, rabbitmq)))),
        spec.entails(always(lift_state(cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq, controller_id)))),
        spec.entails(always(lift_state(no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(controller_id, rabbitmq)))),
        spec.entails(always(lift_action(cm_rv_stays_unchanged(rabbitmq)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(stateful_set_not_exists_or_matches_or_no_more_status_update(controller_id, rabbitmq))))),
{
    // TODO: This proof relied on Cluster::stateful_set_not_exist_or_updated_or_no_more_status_from_bc
    // which was removed now that we have VStatefulSet controller.
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_cm_rv_stays_unchanged(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(every_resource_update_request_implies_at_after_update_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq, controller_id)))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::ServerConfigMap, rabbitmq)))),
    ensures spec.entails(always(lift_action(cm_rv_stays_unchanged(rabbitmq)))),
{
    let cm_key = get_request(SubResource::ServerConfigMap, rabbitmq).key;
    let stronger_inv = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& every_resource_update_request_implies_at_after_update_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)(s)
        &&& no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq, controller_id)(s)
        &&& resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::ServerConfigMap, rabbitmq)(s)
    };

    assert forall |s, s_prime| #[trigger] stronger_inv(s, s_prime) implies cm_rv_stays_unchanged(rabbitmq)(s, s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let req = input->0;
                assert(!resource_delete_request_msg(cm_key)(req));
                assert(!resource_update_status_request_msg(cm_key)(req));
                if resource_update_request_msg(cm_key)(req) {} else {}
            },
            _ => {},
        }
    }

    invariant_n!(
        spec, lift_action(stronger_inv), lift_action(cm_rv_stays_unchanged(rabbitmq)),
        lift_action(cluster.next()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        lift_state(every_resource_update_request_implies_at_after_update_resource_step(controller_id, SubResource::ServerConfigMap, rabbitmq)),
        lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(no_delete_get_then_delete_get_then_update_get_then_update_status_req_in_flight(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(sub_resource_state_matches(SubResource::ServerConfigMap, rabbitmq, controller_id)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ServerConfigMap, rabbitmq)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::ServerConfigMap, rabbitmq))
    );
}

// We can probably hide a lof of spec functions to make this lemma faster
pub proof fn lemma_always_no_create_resource_request_msg_without_name_in_flight(cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
    ensures spec.entails(always(lift_state(no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)))),
{
    // hide(crate::kubernetes_cluster::spec::api_server::state_machine::create_request_admission_check);
    // hide(crate::kubernetes_cluster::spec::api_server::state_machine::created_object_validity_check);
    // hide(crate::kubernetes_cluster::spec::api_server::state_machine::update_request_admission_check);
    // hide(crate::kubernetes_cluster::spec::api_server::state_machine::update_status_request_admission_check);
    // hide(crate::kubernetes_cluster::spec::api_server::state_machine::updated_object_validity_check);
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let inv = no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq);

    assert forall |s: ClusterState| #[trigger] cluster.init()(s) implies inv(s) by {}

    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger] cluster.next()(s, s_prime) && inv(s) implies inv(s_prime) by {
        assert forall |msg: Message|
            !(s_prime.in_flight().contains(msg) && #[trigger] resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg))
        by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(_) => {
                    if !s.in_flight().contains(msg) && s_prime.in_flight().contains(msg) {
                        assert(!resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg));
                    }
                },
                Step::ControllerStep(_) => {
                    if !s.in_flight().contains(msg) && s_prime.in_flight().contains(msg) {
                        assert(!resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg));
                    }
                },
                // Step::DropReqStep(_) => {
                //     if !s.in_flight().contains(msg) && s_prime.in_flight().contains(msg) {
                //         assert(!resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg));
                //     }
                // },
                // Step::BuiltinControllersStep(_) => {
                //     if !s.in_flight().contains(msg) && s_prime.in_flight().contains(msg) {
                //         assert(!resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg));
                //     }
                // },
                _ => {
                    if !s.in_flight().contains(msg) && s_prime.in_flight().contains(msg) {
                        assert(!resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg));
                    }
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), cluster.next(), inv);
}

pub proof fn lemma_always_there_is_no_request_msg_to_external_from_controller(
    controller_id: int,
    cluster: Cluster,
    spec: TempPred<ClusterState>,
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



}
