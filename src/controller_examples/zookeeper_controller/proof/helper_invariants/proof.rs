// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::predicate::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use crate::zookeeper_controller::{
    model::resource::make_stateful_set,
    proof::{
        helper_invariants::stateful_set_in_etcd_satisfies_unchangeable, predicate::*, resource::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub proof fn lemma_always_zookeeper_is_well_formed(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_state(desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
    ensures spec.entails(always(lift_state(zookeeper_is_well_formed(zookeeper)))),
{
    let stronger_inv = |s: ZKCluster| {
        &&& desired_state_is(zookeeper)(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
    };

    invariant_n!(
        spec, lift_state(stronger_inv),
        lift_state(zookeeper_is_well_formed(zookeeper)),
        lift_state(desired_state_is(zookeeper)),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed())
    );
}

pub proof fn lemma_always_cr_objects_in_etcd_satisfy_state_validation(spec: TempPred<ZKCluster>)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(cr_objects_in_etcd_satisfy_state_validation()))),
{
    let inv = cr_objects_in_etcd_satisfy_state_validation();
    ZookeeperClusterView::marshal_status_preserves_integrity();
    init_invariant(spec, ZKCluster::init(), ZKCluster::next(), inv);
}

pub proof fn lemma_always_the_object_in_schedule_satisfies_state_validation(spec: TempPred<ZKCluster>)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(the_object_in_schedule_satisfies_state_validation()))),
{
    let inv = the_object_in_schedule_satisfies_state_validation();
    let stronger_next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& cr_objects_in_etcd_satisfy_state_validation()(s)
    };
    lemma_always_cr_objects_in_etcd_satisfy_state_validation(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(cr_objects_in_etcd_satisfy_state_validation())
    );
    init_invariant(spec, ZKCluster::init(), stronger_next, inv);
}

pub proof fn lemma_always_the_object_in_reconcile_satisfies_state_validation(spec: TempPred<ZKCluster>, key: ObjectRef)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(the_object_in_reconcile_satisfies_state_validation(key)))),
{
    let inv = the_object_in_reconcile_satisfies_state_validation(key);
    let stronger_next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& the_object_in_schedule_satisfies_state_validation()(s)
    };
    lemma_always_the_object_in_schedule_satisfies_state_validation(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(the_object_in_schedule_satisfies_state_validation())
    );
    init_invariant(spec, ZKCluster::init(), stronger_next, inv);
}

pub proof fn lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated_forall(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_delete_resource_request_msg_in_flight(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper))))),
        spec.entails(true_pred().leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper))))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(res, zookeeper)), SubResource::ConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_delete_resource_request_msg_in_flight(res, zookeeper)), SubResource::ConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper)), SubResource::ConfigMap);
    lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(spec, zookeeper);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(SubResource::ConfigMap, zookeeper)))),
        spec.entails(true_pred().leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper))))),
{
    let key = zookeeper.object_ref();
    let inv = cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper);
    let cm_key = get_request(SubResource::ConfigMap, zookeeper).key;
    let cm_well_formed = |s: ZKCluster| {
        s.resources().contains_key(cm_key) ==> ZKCluster::etcd_object_is_well_formed(cm_key)(s)
    };
    let next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& cm_well_formed(s_prime)
        &&& no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)(s)
        &&& no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)(s)
        &&& object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper)(s)
        &&& object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(SubResource::ConfigMap, zookeeper)(s)
    };
    always_to_always_later(spec, lift_state(ZKCluster::each_object_in_etcd_is_well_formed()));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        later(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())),
        lift_state(no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)),
        lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)),
        lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper)),
        lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(SubResource::ConfigMap, zookeeper))
    );
    leads_to_weaken_temp(
        spec, true_pred(), lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())),
        true_pred(), lift_state(inv)
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if s_prime.ongoing_reconciles().contains_key(key) {
            let step = choose |step| ZKCluster::next_step(s, s_prime, step);
            match step {
                Step::ApiServerStep(input) => {
                    let req = input.get_Some_0();
                    assert(!resource_delete_request_msg(get_request(SubResource::ConfigMap, zookeeper).key)(req));
                    assert(!resource_update_status_request_msg(get_request(SubResource::ConfigMap, zookeeper).key)(req));
                    if resource_update_request_msg(get_request(SubResource::ConfigMap, zookeeper).key)(req) {} else {}
                },
                _ => {},
            }
        }
    }
    leads_to_stable_temp(spec, lift_action(next), true_pred(), lift_state(inv));
}

pub proof fn lemma_eventually_always_object_in_response_at_after_create_resource_step_is_same_as_etcd_forall(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref())))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_delete_resource_request_msg_in_flight(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper))))),
        spec.entails(true_pred().leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, zookeeper))))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper))))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_delete_resource_request_msg_in_flight(res, zookeeper)), SubResource::ConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper)), SubResource::ConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(res, zookeeper)), SubResource::ConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, zookeeper)), SubResource::ConfigMap);
    lemma_eventually_always_object_in_response_at_after_create_resource_step_is_same_as_etcd(spec, zookeeper);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_object_in_response_at_after_create_resource_step_is_same_as_etcd(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref())))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)))),
        spec.entails(true_pred().leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ConfigMap, zookeeper)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper))))),
{
    let key = zookeeper.object_ref();
    let inv = object_in_response_at_after_create_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper);
    let next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& ZKCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(key)(s_prime)
        &&& no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)(s)
        &&& no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(SubResource::ConfigMap, zookeeper)(s)
        &&& resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ConfigMap, zookeeper)(s)
    };
    always_to_always_later(spec, lift_state(ZKCluster::each_object_in_etcd_is_well_formed()));
    always_to_always_later(spec, lift_state(ZKCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(key)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        later(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())),
        later(lift_state(ZKCluster::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(key))),
        lift_state(no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)),
        lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(SubResource::ConfigMap, zookeeper)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ConfigMap, zookeeper))
    );
    leads_to_weaken_temp(
        spec, true_pred(), lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())),
        true_pred(), lift_state(inv)
    );
    let resource_key = get_request(SubResource::ConfigMap, zookeeper).key;
    let key = zookeeper.object_ref();
    assert forall |s: ZKCluster, s_prime: ZKCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let pending_req = s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0();
        if at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Create, SubResource::ConfigMap))(s_prime) {
            assert_by(
                s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some()
                && resource_create_request_msg(resource_key)(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()),
                {
                    let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep(input) => {
                            let cr_key = input.1.get_Some_0();
                            if cr_key == key {
                                assert(s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some());
                                assert(resource_create_request_msg(resource_key)(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                            } else {
                                assert(s_prime.ongoing_reconciles()[key] == s.ongoing_reconciles()[key]);
                            }
                        },
                        Step::RestartController() => {
                            assert(false);
                        },
                        _ => {
                            assert(s_prime.ongoing_reconciles()[key] == s.ongoing_reconciles()[key]);
                        }
                    }
                }
            );
            assert forall |msg: ZKMessage| #[trigger] s_prime.in_flight().contains(msg) && Message::resp_msg_matches_req_msg(msg, pending_req) implies resource_create_response_msg(resource_key, s_prime)(msg) by {
                assert(msg.src.is_ApiServer());
                assert(msg.content.is_create_response());
                if msg.content.get_create_response().res.is_Ok() {
                    let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                    match step {
                        Step::ApiServerStep(input) => {
                            let req_msg = input.get_Some_0();
                            assert(!resource_delete_request_msg(resource_key)(req_msg));
                            assert(!resource_update_request_msg(resource_key)(req_msg));
                            assert(!resource_update_status_request_msg(resource_key)(req_msg));
                            match req_msg.content.get_APIRequest_0() {
                                APIRequest::CreateRequest(_) => {
                                    if !s.in_flight().contains(msg) {
                                        assert(msg.content.get_create_response().res.get_Ok_0().object_ref() == req_msg.content.get_create_request().key());
                                        assert(msg.content.get_create_response().res.get_Ok_0().object_ref() == resource_key);
                                        assert(msg.content.get_create_response().res.get_Ok_0() == s_prime.resources()[req_msg.content.get_create_request().key()]);
                                    } else {
                                        assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                                        assert(!s.in_flight().contains(pending_req));
                                    }
                                }
                                _ => {
                                    assert(s.in_flight().contains(msg));
                                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                                    assert(!s.in_flight().contains(pending_req));
                                }
                            }
                        },
                        _ => {
                            assert(s.in_flight().contains(msg));
                            assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                            assert(!s.in_flight().contains(pending_req));
                        }
                    }
                }
            }
        }
    }
    leads_to_stable_temp(spec, lift_action(next), true_pred(), lift_state(inv));
}

pub proof fn lemma_eventually_always_object_in_response_at_after_update_resource_step_is_same_as_etcd_forall(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref())))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_delete_resource_request_msg_in_flight(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper))))),
        spec.entails(true_pred().leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(res, zookeeper))))),
        spec.entails(always(tla_forall(|res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, zookeeper))))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper))))),
{
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_delete_resource_request_msg_in_flight(res, zookeeper)), SubResource::ConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper)), SubResource::ConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(res, zookeeper)), SubResource::ConfigMap);
    always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, zookeeper)), SubResource::ConfigMap);
    lemma_eventually_always_object_in_response_at_after_update_resource_step_is_same_as_etcd(spec, zookeeper);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_object_in_response_at_after_update_resource_step_is_same_as_etcd(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(zookeeper.object_ref())))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)))),
        spec.entails(true_pred().leads_to(lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ConfigMap, zookeeper)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper))))),
{
    let key = zookeeper.object_ref();
    let inv = object_in_response_at_after_update_resource_step_is_same_as_etcd(SubResource::ConfigMap, zookeeper);
    let next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& ZKCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(key)(s_prime)
        &&& no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)(s)
        &&& no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(SubResource::ConfigMap, zookeeper)(s)
        &&& resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ConfigMap, zookeeper)(s)
    };
    always_to_always_later(spec, lift_state(ZKCluster::each_object_in_etcd_is_well_formed()));
    always_to_always_later(spec, lift_state(ZKCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(key)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        later(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())),
        later(lift_state(ZKCluster::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(key))),
        lift_state(no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)),
        lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(SubResource::ConfigMap, zookeeper)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ConfigMap, zookeeper))
    );
    leads_to_weaken_temp(
        spec, true_pred(), lift_state(|s: ZKCluster| !s.ongoing_reconciles().contains_key(zookeeper.object_ref())),
        true_pred(), lift_state(inv)
    );
    let resource_key = get_request(SubResource::ConfigMap, zookeeper).key;
    let key = zookeeper.object_ref();
    assert forall |s: ZKCluster, s_prime: ZKCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let pending_req = s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0();
        if at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Update, SubResource::ConfigMap))(s_prime) {
            assert_by(
                s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some()
                && resource_update_request_msg(resource_key)(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()),
                {
                    let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep(input) => {
                            let cr_key = input.1.get_Some_0();
                            if cr_key == key {
                                assert(s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some());
                                assert(resource_update_request_msg(resource_key)(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                            } else {
                                assert(s_prime.ongoing_reconciles()[key] == s.ongoing_reconciles()[key]);
                            }
                        },
                        Step::RestartController() => {
                            assert(false);
                        },
                        _ => {
                            assert(s_prime.ongoing_reconciles()[key] == s.ongoing_reconciles()[key]);
                        }
                    }
                }
            );

            assert forall |msg: ZKMessage| #[trigger] s_prime.in_flight().contains(msg) && Message::resp_msg_matches_req_msg(msg, pending_req) implies resource_update_response_msg(resource_key, s_prime)(msg) by {
                assert(msg.src.is_ApiServer());
                assert(msg.content.is_update_response());
                if msg.content.get_update_response().res.is_Ok() {
                    let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                    match step {
                        Step::ApiServerStep(input) => {
                            let req_msg = input.get_Some_0();
                            assert(!resource_delete_request_msg(resource_key)(req_msg));
                            assert(!resource_update_status_request_msg(resource_key)(req_msg));
                            match req_msg.content.get_APIRequest_0() {
                                APIRequest::UpdateRequest(_) => {
                                    if !s.in_flight().contains(msg) {
                                        assert(msg.content.get_update_response().res.get_Ok_0().object_ref() == req_msg.content.get_update_request().key());
                                        assert(msg.content.get_update_response().res.get_Ok_0().object_ref() == resource_key);
                                        assert(msg.content.get_update_response().res.get_Ok_0() == s_prime.resources()[req_msg.content.get_update_request().key()]);
                                    } else {
                                        assert(!resource_update_request_msg(resource_key)(req_msg));
                                        assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                                        assert(!s.in_flight().contains(pending_req));
                                    }
                                }
                                _ => {
                                    assert(s.in_flight().contains(msg));
                                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                                    assert(!s.in_flight().contains(pending_req));
                                }
                            }
                        },
                        _ => {
                            assert(s.in_flight().contains(msg));
                            assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                            assert(!s.in_flight().contains(pending_req));
                        }
                    }
                }
            }
        }
    }
    leads_to_stable_temp(spec, lift_action(next), true_pred(), lift_state(inv));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)))),
{
    let inv = response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper);
    let key = zookeeper.object_ref();
    let resource_key = get_request(sub_resource, zookeeper).key;
    let next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)(s_prime)
    };
    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    ZKCluster::lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(spec, key);
    always_to_always_later(spec, lift_state(ZKCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        later(lift_state(ZKCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)))
    );
    assert forall |s: ZKCluster, s_prime: ZKCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s_prime) {
            let step = choose |step| ZKCluster::next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    let cr_key = input.1.get_Some_0();
                    if cr_key == key {
                        assert(s_prime.ongoing_reconciles()[key].pending_req_msg.is_Some());
                        assert(resource_get_request_msg(resource_key)(s_prime.ongoing_reconciles()[key].pending_req_msg.get_Some_0()));
                    } else {
                        assert(s_prime.ongoing_reconciles()[key] == s.ongoing_reconciles()[key]);
                    }
                },
                Step::RestartController() => {
                    assert(false);
                },
                _ => {
                    assert(s_prime.ongoing_reconciles()[key] == s.ongoing_reconciles()[key]);
                }
            }
        }
    }
    init_invariant(spec, ZKCluster::init(), next, inv);
}

pub proof fn lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step_forall(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)))),
        spec.entails(always(lift_state(ZKCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, zookeeper).key))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, zookeeper))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, zookeeper).key)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(response_at_after_get_resource_step_is_resource_get_response(res, zookeeper)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_delete_resource_request_msg_in_flight(res, zookeeper)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(res, zookeeper)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(res, zookeeper)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(res, zookeeper)), sub_resource);
        lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step(spec, sub_resource, zookeeper);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step(
    spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)))),
        spec.entails(always(lift_state(ZKCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, zookeeper).key)))),
        spec.entails(always(lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper))))),
{
    let key = zookeeper.object_ref();
    let resource_key = get_request(sub_resource, zookeeper).key;
    let requirements = |msg: ZKMessage, s: ZKCluster| {
        resource_update_request_msg(resource_key)(msg) ==> {
            &&& at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& ZKCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.resource_version.is_Some()
            &&& msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
            &&& (
                s.resources().contains_key(resource_key)
                && msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
            ) ==> (
                update(sub_resource, zookeeper, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).is_Ok()
                && msg.content.get_update_request().obj == update(sub_resource, zookeeper, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).get_Ok_0()
            )
        }
    };
    let stronger_next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)(s)
        &&& ZKCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, zookeeper).key)(s)
        &&& response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)(s)
        &&& no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)(s)
        &&& no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: ZKMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_update_request_msg(resource_key)(msg) {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, zookeeper, s, s_prime, msg, step);
                    let resp = step.get_ControllerStep_0().0.get_Some_0();
                    assert(ZKCluster::is_ok_get_response_msg()(resp));
                    assert(s.in_flight().contains(resp));
                    assert(resp.content.get_get_response().res.get_Ok_0().metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version);
                    if s.resources().contains_key(resource_key) && resp.content.get_get_response().res.get_Ok_0().metadata.resource_version == s.resources()[resource_key].metadata.resource_version {
                        assert(resp.content.get_get_response().res.get_Ok_0() == s.resources()[resource_key]);
                        assert(s_prime.resources()[resource_key] == s.resources()[resource_key]);
                    }
                    if sub_resource == SubResource::StatefulSet {
                        let cm_key = get_request(SubResource::ConfigMap, zookeeper).key;
                        assert(s.resources()[cm_key] == s_prime.resources()[cm_key]);
                        assert(s.ongoing_reconciles()[key].local_state.latest_config_map_rv_opt == s_prime.ongoing_reconciles()[key].local_state.latest_config_map_rv_opt)
                    }
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(ZKCluster::each_object_in_etcd_is_well_formed()));
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(ZKCluster::next()), lift_state(ZKCluster::crash_disabled()), lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)),
        lift_state(ZKCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())),
        lift_state(ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, zookeeper).key)),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)),
        lift_state(no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)),
        lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper))
    );

    ZKCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, zookeeper)),
        lift_state(ZKCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub proof fn lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr_forall(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)))),
    ensures
        spec.entails(true_pred().leads_to(
            always(tla_forall(|sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper))))) by {
        lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(spec, sub_resource, zookeeper);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(
    spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper))))),
{
    let key = zookeeper.object_ref();
    let resource_key = get_request(sub_resource, zookeeper).key;
    let requirements = |msg: ZKMessage, s: ZKCluster| {
        resource_update_request_msg(resource_key)(msg) ==> {
            &&& at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& ZKCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.owner_references_only_contains(zookeeper.controller_owner_ref())
        }
    };
    let stronger_next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: ZKMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_update_request_msg(resource_key)(msg) {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, zookeeper, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(ZKCluster::next()), lift_state(ZKCluster::crash_disabled()), lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper))
    );

    ZKCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper)),
        lift_state(ZKCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub proof fn lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step_forall(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)))),
        spec.entails(always(lift_state(zookeeper_is_well_formed(zookeeper)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper))))) by {
        lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step(spec, sub_resource, zookeeper);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step(
    spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)))),
        spec.entails(always(lift_state(zookeeper_is_well_formed(zookeeper)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper))))),
{
    let key = zookeeper.object_ref();
    let resource_key = get_request(sub_resource, zookeeper).key;
    let requirements = |msg: ZKMessage, s: ZKCluster| {
        resource_create_request_msg(resource_key)(msg) ==> {
            &&& at_zk_step(key, ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
            &&& ZKCluster::pending_req_msg_is(s, key, msg)
            &&& make(sub_resource, zookeeper, s.ongoing_reconciles()[key].local_state).is_Ok()
            &&& msg.content.get_create_request().obj == make(sub_resource, zookeeper, s.ongoing_reconciles()[key].local_state).get_Ok_0()
        }
    };
    let stronger_next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
        &&& ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)(s)
        &&& zookeeper_is_well_formed(zookeeper)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: ZKMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_create_request_msg(resource_key)(msg) {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, zookeeper, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(ZKCluster::next()), lift_state(ZKCluster::crash_disabled()), lift_state(ZKCluster::busy_disabled()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id()),
        lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zookeeper)),
        lift_state(zookeeper_is_well_formed(zookeeper))
    );

    ZKCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)),
        lift_state(ZKCluster::every_in_flight_req_msg_satisfies(requirements)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_no_update_status_request_msg_in_flight_of_except_stateful_set(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper)))),
{
    ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    let inv = no_update_status_request_msg_in_flight_of_except_stateful_set(sub_resource, zookeeper);
    let stronger_next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed())
    );

    let resource_key = get_request(sub_resource, zookeeper).key;
    assert forall |s, s_prime: ZKCluster| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        if sub_resource != SubResource::StatefulSet {
            assert forall |msg: ZKMessage| s_prime.in_flight().contains(msg) implies !(#[trigger] resource_update_status_request_msg(resource_key)(msg)) by {
                if s.in_flight().contains(msg) {
                    assert(!resource_update_status_request_msg(resource_key)(msg));
                } else {
                    let step = choose |step: ZKStep| ZKCluster::next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep(input) => {
                            if input.1.is_Some() {
                                let cr_key = input.1.get_Some_0();
                                if s.ongoing_reconciles().contains_key(cr_key) {
                                    match s.ongoing_reconciles()[cr_key].local_state.reconcile_step {
                                        ZookeeperReconcileStep::Init => {},
                                        ZookeeperReconcileStep::AfterKRequestStep(_, resource) => {
                                            match resource {
                                                SubResource::HeadlessService => {},
                                                SubResource::ClientService => {},
                                                SubResource::AdminServerService => {},
                                                SubResource::ConfigMap => {},
                                                SubResource::StatefulSet => {},
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
    init_invariant(spec, ZKCluster::init(), stronger_next, inv);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(zookeeper)))),
{
    ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    let inv = no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(zookeeper);
    let stronger_next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed())
    );

    let resource_key = get_request(SubResource::StatefulSet, zookeeper).key;
    assert forall |s, s_prime: ZKCluster| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: ZKMessage| #[trigger] s_prime.in_flight().contains(msg) && msg.dst.is_ApiServer() && !msg.src.is_BuiltinController() && msg.content.is_update_status_request()
        implies msg.content.get_update_status_request().key() != resource_key by {
            if s.in_flight().contains(msg) {
                assert(msg.content.get_update_status_request().key() != resource_key);
            } else {
                let step = choose |step: ZKStep| ZKCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        if input.1.is_Some() {
                            let cr_key = input.1.get_Some_0();
                            if s.ongoing_reconciles().contains_key(cr_key) {
                                match s.ongoing_reconciles()[cr_key].local_state.reconcile_step {
                                    ZookeeperReconcileStep::Init => {},
                                    ZookeeperReconcileStep::AfterKRequestStep(_, resource) => {
                                        match resource {
                                            SubResource::HeadlessService => {},
                                            SubResource::ClientService => {},
                                            SubResource::AdminServerService => {},
                                            SubResource::ConfigMap => {},
                                            SubResource::StatefulSet => {},
                                        }
                                    },
                                    _ => {}
                                }
                            } else {}
                        } else {}
                        assert(msg.content.get_update_status_request().key() != resource_key);
                    },
                    Step::ApiServerStep(_) => {
                        assert(!msg.content.is_APIRequest());
                        assert(!msg.content.is_update_status_request());
                        assert(false);
                    },
                    Step::ClientStep() => {
                        assert(!msg.content.is_update_status_request());
                        assert(false);
                    },
                    Step::BuiltinControllersStep(_) => {
                        assert(msg.src.is_BuiltinController());
                        assert(false);
                    },
                    Step::FailTransientlyStep(_) => {
                        assert(!msg.content.is_APIRequest());
                        assert(!msg.content.is_update_status_request());
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
    init_invariant(spec, ZKCluster::init(), stronger_next, inv);
}

spec fn make_owner_references_with_name_and_uid(name: StringView, uid: Uid) -> OwnerReferenceView {
    OwnerReferenceView {
        block_owner_deletion: None,
        controller: Some(true),
        kind: ZookeeperClusterView::kind(),
        name: name,
        uid: uid,
    }
}

pub proof fn lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)))),
{
    let inv = resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper);
    lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(spec, sub_resource, zookeeper);
    let stronger_next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, zookeeper)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, zookeeper))
    );
    init_invariant(spec, ZKCluster::init(), stronger_next, inv);
}

spec fn resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(
    sub_resource: SubResource, zookeeper: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let key = zookeeper.object_ref();
        let resource_key = get_request(sub_resource, zookeeper).key;
        forall |msg: ZKMessage| {
            #[trigger] s.in_flight().contains(msg) ==> {
                &&& resource_update_request_msg(resource_key)(msg)
                    ==> msg.content.get_update_request().obj.metadata.finalizers.is_None()
                        && exists |uid: Uid| #![auto]
                            msg.content.get_update_request().obj.metadata.owner_references == Some(seq![
                                make_owner_references_with_name_and_uid(key.name, uid)
                            ])
                &&& resource_create_request_msg(resource_key)(msg)
                    ==> msg.content.get_create_request().obj.metadata.finalizers.is_None()
                        && exists |uid: Uid| #![auto]
                            msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                                make_owner_references_with_name_and_uid(key.name, uid)
                            ])
            }
        }
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, zookeeper)))),
{
    let inv = resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, zookeeper);
    let stronger_next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };
    let key = zookeeper.object_ref();
    let resource_key = get_request(sub_resource, zookeeper).key;
    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    let create_msg_pred = |msg: ZKMessage| {
        resource_create_request_msg(resource_key)(msg)
        ==> msg.content.get_create_request().obj.metadata.finalizers.is_None()
            && exists |uid: Uid| #![auto]
                msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                    make_owner_references_with_name_and_uid(key.name, uid)
                ])
    };
    let update_msg_pred = |msg: ZKMessage| {
        resource_update_request_msg(resource_key)(msg)
        ==> msg.content.get_update_request().obj.metadata.finalizers.is_None()
            && exists |uid: Uid| #![auto]
                msg.content.get_update_request().obj.metadata.owner_references == Some(seq![
                    make_owner_references_with_name_and_uid(key.name, uid)
                ])
    };
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) implies update_msg_pred(msg) && create_msg_pred(msg) by {
            if !s.in_flight().contains(msg) {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, zookeeper, s, s_prime, msg, step);
                let cr = s.ongoing_reconciles()[key].triggering_cr;
                if resource_create_request_msg(resource_key)(msg) {
                    assert(msg.content.get_create_request().obj == make(sub_resource, cr, s.ongoing_reconciles()[key].local_state).get_Ok_0());
                    assert(msg.content.get_create_request().obj.metadata.finalizers.is_None());
                    assert(msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                        make_owner_references_with_name_and_uid(key.name, cr.metadata.uid.get_Some_0())
                    ]));
                }
                if resource_update_request_msg(resource_key)(msg) {
                    assert(step.get_ControllerStep_0().0.get_Some_0().content.is_get_response());
                    assert(step.get_ControllerStep_0().0.get_Some_0().content.get_get_response().res.is_Ok());
                    assert(update(
                        sub_resource, cr, s.ongoing_reconciles()[key].local_state, step.get_ControllerStep_0().0.get_Some_0().content.get_get_response().res.get_Ok_0()
                    ).is_Ok());
                    assert(msg.content.get_update_request().obj == update(
                        sub_resource, cr, s.ongoing_reconciles()[key].local_state, step.get_ControllerStep_0().0.get_Some_0().content.get_get_response().res.get_Ok_0()
                    ).get_Ok_0());
                    assert(msg.content.get_update_request().obj.metadata.owner_references == Some(seq![
                        make_owner_references_with_name_and_uid(key.name, cr.metadata.uid.get_Some_0())
                    ]));
                }

            }
        }
    }
    init_invariant(spec, ZKCluster::init(), stronger_next, inv);
}

/// This lemma is used to show that if an action (which transfers the state from s to s_prime) creates a sub resource object
/// create/update request message (with key as key), it must be a controller action, and the triggering cr is s.ongoing_reconciles()[key].triggering_cr.
///
/// After the action, the controller stays at After(Create/Update, SubResource) step.
///
/// Tips: Talking about both s and s_prime give more information to those using this lemma and also makes the verification faster.
#[verifier(spinoff_prover)]
pub proof fn lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource: SubResource, zookeeper: ZookeeperClusterView, s: ZKCluster, s_prime: ZKCluster, msg: ZKMessage, step: ZKStep)
    requires
        !s.in_flight().contains(msg), s_prime.in_flight().contains(msg),
        ZKCluster::next_step(s, s_prime, step),
        ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
    ensures
        resource_create_request_msg(get_request(sub_resource, zookeeper).key)(msg)
        ==> step.is_ControllerStep() && step.get_ControllerStep_0().1.get_Some_0() == zookeeper.object_ref()
            && at_zk_step(zookeeper.object_ref(), ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
            && at_zk_step(zookeeper.object_ref(), ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s_prime)
            && ZKCluster::pending_req_msg_is(s_prime, zookeeper.object_ref(), msg),
        resource_update_request_msg(get_request(sub_resource, zookeeper).key)(msg)
        ==> step.is_ControllerStep() && step.get_ControllerStep_0().1.get_Some_0() == zookeeper.object_ref()
            && at_zk_step(zookeeper.object_ref(), ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
            && at_zk_step(zookeeper.object_ref(), ZookeeperReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s_prime)
            && ZKCluster::pending_req_msg_is(s_prime, zookeeper.object_ref(), msg),
{
    // Since we know that this step creates a create server config map message, it is easy to see that it's a controller action.
    // This action creates a config map, and there are two kinds of config maps, we have to show that only server config map
    // is possible by extra reasoning about the strings.
    let cr_key = step.get_ControllerStep_0().1.get_Some_0();
    let key = zookeeper.object_ref();
    let cr = s.ongoing_reconciles()[key].triggering_cr;
    let resource_key = get_request(sub_resource, zookeeper).key;
    if resource_create_request_msg(get_request(sub_resource, zookeeper).key)(msg) || resource_update_request_msg(get_request(sub_resource, zookeeper).key)(msg) {
        assert(step.is_ControllerStep());
        assert(s.ongoing_reconciles().contains_key(cr_key));
        let local_step = s.ongoing_reconciles()[cr_key].local_state.reconcile_step;
        let local_step_prime = s_prime.ongoing_reconciles()[cr_key].local_state.reconcile_step;
        assert(local_step_prime.is_AfterKRequestStep());
        assert(local_step.is_AfterKRequestStep() && local_step.get_AfterKRequestStep_0() == ActionKind::Get);
        if resource_create_request_msg(get_request(sub_resource, zookeeper).key)(msg) {
            assert(local_step_prime.get_AfterKRequestStep_0() == ActionKind::Create);
        }
        if resource_update_request_msg(get_request(sub_resource, zookeeper).key)(msg) {
            assert(local_step_prime.get_AfterKRequestStep_0() == ActionKind::Update);
        }
        assert_by(
            cr_key == zookeeper.object_ref() && local_step.get_AfterKRequestStep_1() == sub_resource && ZKCluster::pending_req_msg_is(s_prime, cr_key, msg),
            {
                // It's easy for the verifier to know that cr_key has the same kind and namespace as key.
                match sub_resource {
                    SubResource::HeadlessService => {
                        assert_by(
                            key.name + new_strlit("-headless")@ != cr_key.name + new_strlit("-client")@,
                            {
                                let str1 = key.name + new_strlit("-headless")@;
                                let str2 = cr_key.name + new_strlit("-client")@;
                                reveal_strlit("-headless");
                                reveal_strlit("-client");
                                if str1.len() == str2.len() {
                                    assert(str1[str1.len() - 1] == 's');
                                    assert(str2[str1.len() - 1] == 't');
                                }
                            }
                        );
                        assert_by(
                            key.name + new_strlit("-headless")@ != cr_key.name + new_strlit("-admin-server")@,
                            {
                                let str1 = key.name + new_strlit("-headless")@;
                                let str2 = cr_key.name + new_strlit("-admin-server")@;
                                reveal_strlit("-headless");
                                reveal_strlit("-admin-server");
                                if str1.len() == str2.len() {
                                    assert(str1[str1.len() - 1] == 's');
                                    assert(str2[str1.len() - 1] == 'r');
                                }
                            }
                        );
                        seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-headless")@);
                    },
                    SubResource::ClientService => {
                        assert_by(
                            key.name + new_strlit("-client")@ != cr_key.name + new_strlit("-headless")@,
                            {
                                let str1 = key.name + new_strlit("-client")@;
                                let str2 = cr_key.name + new_strlit("-headless")@;
                                reveal_strlit("-client");
                                reveal_strlit("-headless");
                                if str1.len() == str2.len() {
                                    assert(str1[str1.len() - 1] == 't');
                                    assert(str2[str1.len() - 1] == 's');
                                }
                            }
                        );
                        assert_by(
                            key.name + new_strlit("-client")@ != cr_key.name + new_strlit("-admin-server")@,
                            {
                                let str1 = key.name + new_strlit("-client")@;
                                let str2 = cr_key.name + new_strlit("-admin-server")@;
                                reveal_strlit("-client");
                                reveal_strlit("-admin-server");
                                if str1.len() == str2.len() {
                                    assert(str1[str1.len() - 1] == 't');
                                    assert(str2[str1.len() - 1] == 'r');
                                }
                            }
                        );
                        seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-client")@);
                    },
                    SubResource::AdminServerService => {
                        assert_by(
                            key.name + new_strlit("-admin-server")@ != cr_key.name + new_strlit("-headless")@,
                            {
                                let str1 = key.name + new_strlit("-admin-server")@;
                                let str2 = cr_key.name + new_strlit("-headless")@;
                                reveal_strlit("-admin-server");
                                reveal_strlit("-headless");
                                if str1.len() == str2.len() {
                                    assert(str1[str1.len() - 1] == 'r');
                                    assert(str2[str1.len() - 1] == 's');
                                }
                            }
                        );
                        assert_by(
                            key.name + new_strlit("-admin-server")@ != cr_key.name + new_strlit("-client")@,
                            {
                                let str1 = key.name + new_strlit("-admin-server")@;
                                let str2 = cr_key.name + new_strlit("-client")@;
                                reveal_strlit("-admin-server");
                                reveal_strlit("-client");
                                if str1.len() == str2.len() {
                                    assert(str1[str1.len() - 1] == 'r');
                                    assert(str2[str1.len() - 1] == 't');
                                }
                            }
                        );
                        seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-admin-server")@);
                    },
                    SubResource::ConfigMap => {
                        // Then we show that only if cr_key.name equals key.name, can this message be created in this step.
                        seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-configmap")@);
                    },
                    _ => {},
                }
            }
        )
    }
}

pub proof fn lemma_eventually_always_no_delete_resource_request_msg_in_flight_forall(
    spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] no_delete_resource_request_msg_in_flight(sub_resource, zookeeper))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(res, zookeeper)), sub_resource);
        lemma_eventually_always_no_delete_resource_request_msg_in_flight(spec, sub_resource, zookeeper);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)));
}

/// This lemma demonstrates how to use kubernetes_cluster::proof::api_server_liveness::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies
/// (referred to as lemma_X) to prove that the system will eventually enter a state where delete stateful set request messages
/// will never appear in flight.
///
/// As an example, we can look at how this lemma is proved.
/// - Precondition: The preconditions should include all precondtions used by lemma_X and other predicates which show that
///     the newly generated messages are as expected. ("expected" means not delete stateful set request messages in this lemma. Therefore,
///     we provide an invariant stateful_set_has_owner_reference_pointing_to_current_cr so that the grabage collector won't try
///     to send a delete request to delete the messsage.)
/// - Postcondition: spec |= true ~> [](forall |msg| as_expected(msg))
/// - Proof body: The proof consists of three parts.
///   + Come up with "requirements" for those newly created api request messages. Usually, just move the forall |msg| and
///     s.in_flight().contains(msg) in the statepred of final state (no_delete_sts_req_is_in_flight in this lemma, so we can
///     get the requirements in this lemma).
///   + Show that spec |= every_new_req_msg_if_in_flight_then_satisfies. Basically, use two assert forall to show that forall state and
///     its next state and forall messages, if the messages are newly generated, they must satisfy the "requirements" and always satisfies it
///     as long as it is in flight.
///   + Call lemma_X. If a correct "requirements" are provided, we can easily prove the equivalence of every_in_flight_req_msg_satisfies(requirements)
///     and the original statepred.
#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_no_delete_resource_request_msg_in_flight(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper))))
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_delete_resource_request_msg_in_flight(sub_resource, zookeeper))))),
{
    let key = zookeeper.object_ref();
    let resource_key = get_request(sub_resource, zookeeper).key;
    let requirements = |msg: ZKMessage, s: ZKCluster| !resource_delete_request_msg(resource_key)(msg);

    let resource_well_formed = |s: ZKCluster| {
        &&& s.resources().contains_key(resource_key) ==> ZKCluster::etcd_object_is_well_formed(resource_key)(s)
        &&& s.resources().contains_key(key) ==> ZKCluster::etcd_object_is_well_formed(key)(s)
    };
    let stronger_next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::desired_state_is(zookeeper)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)(s)
        &&& resource_well_formed(s)
    };
    always_weaken_temp(spec, lift_state(ZKCluster::each_object_in_etcd_is_well_formed()), lift_state(resource_well_formed));
    assert forall |s: ZKCluster, s_prime: ZKCluster| #[trigger] stronger_next(s, s_prime) implies ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: ZKMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.in_flight().contains(msg) {
                assert(requirements(msg, s));
                assert(requirements(msg, s_prime));
            } else {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                match step {
                    Step::BuiltinControllersStep(_) => {
                        if s.resources().contains_key(resource_key) {
                            let owner_refs = s.resources()[resource_key].metadata.owner_references;
                            assert(owner_refs == Some(seq![zookeeper.controller_owner_ref()]));
                            assert(owner_reference_to_object_reference(owner_refs.get_Some_0()[0], key.namespace) == key);
                        }
                    },
                    Step::ControllerStep(input) => {
                        let cr_key = input.1.get_Some_0();
                        if s_prime.ongoing_reconciles()[cr_key].pending_req_msg.is_Some() {
                            assert(msg == s_prime.ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0());
                            assert(!s_prime.ongoing_reconciles()[cr_key].pending_req_msg.get_Some_0().content.is_delete_request());
                        }
                    },
                    Step::ClientStep() => {
                        if msg.content.is_delete_request() {
                            assert(msg.content.get_delete_request().key.kind != resource_key.kind);
                        }
                    },
                    _ => {
                        assert(requirements(msg, s_prime));
                    }
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(ZKCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(ZKCluster::next()), lift_state(ZKCluster::desired_state_is(zookeeper)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)),
        lift_state(resource_well_formed)
    );

    ZKCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_delete_resource_request_msg_in_flight(sub_resource, zookeeper)),
        lift_state(ZKCluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr_forall(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource|lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| (lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper))))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, zookeeper)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(every_resource_create_request_implies_at_after_create_resource_step(res, zookeeper)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(res, zookeeper)), sub_resource);
        lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(spec, sub_resource, zookeeper);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper))))),
{
    let key = get_request(sub_resource, zookeeper).key;
    let eventual_owner_ref = |owner_ref: Option<Seq<OwnerReferenceView>>| {owner_ref == Some(seq![zookeeper.controller_owner_ref()])};
    always_weaken_temp(spec, lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, zookeeper)), lift_state(ZKCluster::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)));
    always_weaken_temp(spec, lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, zookeeper)), lift_state(ZKCluster::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)));
    always_weaken_temp(spec, lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)), lift_state(ZKCluster::object_has_no_finalizers(key)));

    let state = |s: ZKCluster| {
        ZKCluster::desired_state_is(zookeeper)(s)
        && resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper)(s)
    };
    invariant_n!(
        spec, lift_state(state), lift_state(ZKCluster::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(ZKCluster::garbage_collector_deletion_enabled(key))),
        lift_state(ZKCluster::desired_state_is(zookeeper)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, zookeeper))
    );
    ZKCluster::lemma_eventually_objects_owner_references_satisfies(spec, key, eventual_owner_ref);
    temp_pred_equality(
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, zookeeper)),
        lift_state(ZKCluster::objects_owner_references_satisfies(key, eventual_owner_ref))
    );
}

pub proof fn leads_to_always_tla_forall_subresource(spec: TempPred<ZKCluster>, p: TempPred<ZKCluster>, a_to_p: spec_fn(SubResource)->TempPred<ZKCluster>)
    requires forall |a: SubResource| spec.entails(p.leads_to(always(#[trigger] a_to_p(a)))),
    ensures spec.entails(p.leads_to(always(tla_forall(a_to_p)))),
{
    leads_to_always_tla_forall(
        spec, p, a_to_p,
        set![SubResource::HeadlessService, SubResource::ClientService, SubResource::AdminServerService,
        SubResource::ConfigMap, SubResource::StatefulSet]
    );
}

// Below are invariants that only hold after the config map matches the desired state

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_stateful_set_not_exists_or_matches_or_no_more_status_update(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(tla_forall(|i| ZKCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| ZKCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::desired_state_is(zookeeper)))),
        spec.entails(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(object_in_etcd_satisfies_unchangeable(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(stateful_set_in_etcd_satisfies_unchangeable(zookeeper)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)))),
        spec.entails(always(lift_state(cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)))),
        spec.entails(always(lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(zookeeper)))),
        spec.entails(always(lift_action(cm_rv_stays_unchanged(zookeeper)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper))))),
{
    let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
    let cm_key = get_request(SubResource::ConfigMap, zookeeper).key;
    let make_fn = |rv: StringView| make_stateful_set(zookeeper, rv);
    let inv_for_create = |s: ZKCluster| {
        &&& every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
    };
    invariant_n!(
        spec, lift_state(inv_for_create), lift_state(ZKCluster::every_in_flight_create_req_msg_for_this_sts_matches(sts_key, cm_key, make_fn)),
        lift_state(every_resource_create_request_implies_at_after_create_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper))
    );
    let inv_for_update = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::desired_state_is(zookeeper)(s)
        &&& every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)(s)
        &&& stateful_set_in_etcd_satisfies_unchangeable(zookeeper)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)(s)
        &&& cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)(s)
        &&& sub_resource_state_matches(SubResource::ConfigMap, zookeeper)(s)
        &&& cm_rv_stays_unchanged(zookeeper)(s, s_prime)
    };
    StatefulSetView::marshal_spec_preserves_integrity();
    StatefulSetView::marshal_status_preserves_integrity();
    invariant_n!(
        spec, lift_action(inv_for_update), lift_state(ZKCluster::every_in_flight_update_req_msg_for_this_sts_matches(sts_key, cm_key, make_fn)),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(ZKCluster::desired_state_is(zookeeper)),
        lift_state(every_resource_update_request_implies_at_after_update_resource_step(SubResource::StatefulSet, zookeeper)),
        lift_state(stateful_set_in_etcd_satisfies_unchangeable(zookeeper)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)),
        lift_state(cm_rv_is_the_same_as_etcd_server_cm_if_cm_updated(zookeeper)),
        lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper)),
        lift_action(cm_rv_stays_unchanged(zookeeper))
    );

    temp_pred_equality(lift_action(cm_rv_stays_unchanged(zookeeper)), lift_action(ZKCluster::obj_rv_stays_unchanged(cm_key)));

    ZKCluster::lemma_true_leads_to_always_stateful_set_not_exist_or_updated_or_no_more_pending_req(spec, sts_key, cm_key, make_fn);

    let stronger_inv = |s: ZKCluster| {
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::desired_state_is(zookeeper)(s)
        &&& stateful_set_in_etcd_satisfies_unchangeable(zookeeper)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)(s)
        &&& sub_resource_state_matches(SubResource::ConfigMap, zookeeper)(s)
        &&& no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(zookeeper)(s)
    };

    assert forall |s| #[trigger] stronger_inv(s) && ZKCluster::stateful_set_not_exist_or_updated_or_no_more_status_from_bc(sts_key, cm_key, make_fn)(s)
    implies stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper)(s) by {
        if !s.resources().contains_key(sts_key) {}
        else if sub_resource_state_matches(SubResource::StatefulSet, zookeeper)(s) {}
        else {
            assert forall |msg: ZKMessage| s.in_flight().contains(msg) implies !(#[trigger] resource_update_status_request_msg(get_request(SubResource::StatefulSet, zookeeper).key)(msg)) by {
                if update_status_msg_from_bc_for(get_request(SubResource::StatefulSet, zookeeper).key)(msg) {} else {}
            }
        }
    }
    combine_spec_entails_always_n!(
        spec, lift_state(stronger_inv), lift_state(ZKCluster::each_object_in_etcd_is_well_formed()), lift_state(ZKCluster::desired_state_is(zookeeper)),
        lift_state(stateful_set_in_etcd_satisfies_unchangeable(zookeeper)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::StatefulSet, zookeeper)),
        lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper)),
        lift_state(no_update_status_request_msg_not_from_bc_in_flight_of_stateful_set(zookeeper))
    );

    leads_to_always_enhance(spec, lift_state(stronger_inv), true_pred(),
        lift_state(ZKCluster::stateful_set_not_exist_or_updated_or_no_more_status_from_bc(sts_key, cm_key, make_fn)),
        lift_state(stateful_set_not_exists_or_matches_or_no_more_status_update(zookeeper))
    );
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_cm_rv_stays_unchanged(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(every_resource_update_request_implies_at_after_update_resource_step(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ConfigMap, zookeeper)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::ConfigMap, zookeeper)))),
    ensures spec.entails(always(lift_action(cm_rv_stays_unchanged(zookeeper)))),
{
    let sts_key = get_request(SubResource::StatefulSet, zookeeper).key;
    let cm_key = get_request(SubResource::ConfigMap, zookeeper).key;
    let make_fn = |rv: StringView| make_stateful_set(zookeeper, rv);
    let stronger_inv = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& every_resource_update_request_implies_at_after_update_resource_step(SubResource::ConfigMap, zookeeper)(s)
        &&& no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)(s)
        &&& no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)(s)
        &&& sub_resource_state_matches(SubResource::ConfigMap, zookeeper)(s)
        &&& resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ConfigMap, zookeeper)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::ConfigMap, zookeeper)(s)
    };

    assert forall |s, s_prime| #[trigger] stronger_inv(s, s_prime) implies cm_rv_stays_unchanged(zookeeper)(s, s_prime) by {
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                assert(!resource_delete_request_msg(cm_key)(req));
                assert(!resource_update_status_request_msg(cm_key)(req));
                if resource_update_request_msg(cm_key)(req) {} else {}
            },
            _ => {},
        }
    }

    invariant_n!(
        spec, lift_action(stronger_inv), lift_action(cm_rv_stays_unchanged(zookeeper)),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        lift_state(every_resource_update_request_implies_at_after_update_resource_step(SubResource::ConfigMap, zookeeper)),
        lift_state(no_update_status_request_msg_in_flight_of_except_stateful_set(SubResource::ConfigMap, zookeeper)),
        lift_state(no_delete_resource_request_msg_in_flight(SubResource::ConfigMap, zookeeper)),
        lift_state(sub_resource_state_matches(SubResource::ConfigMap, zookeeper)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(SubResource::ConfigMap, zookeeper)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::ConfigMap, zookeeper))
    );
}

}
