// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::predicate::*;
use crate::fluent_controller::fluentbit_config::{
    model::resource::*,
    proof::{predicate::*, resource::*},
    trusted::{liveness_theorem::desired_state_is, spec_types::*, step::*},
};
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
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub proof fn lemma_always_fbc_is_well_formed(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_state(desired_state_is(fbc)))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
    ensures spec.entails(always(lift_state(fbc_is_well_formed(fbc)))),
{
    let stronger_inv = |s: FBCCluster| {
        &&& desired_state_is(fbc)(s)
        &&& FBCCluster::each_object_in_etcd_is_well_formed()(s)
    };

    invariant_n!(
        spec, lift_state(stronger_inv),
        lift_state(fbc_is_well_formed(fbc)),
        lift_state(desired_state_is(fbc)),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed())
    );
}

pub proof fn lemma_always_cr_objects_in_etcd_satisfy_state_validation(spec: TempPred<FBCCluster>)
    requires
        spec.entails(lift_state(FBCCluster::init())),
        spec.entails(always(lift_action(FBCCluster::next()))),
    ensures spec.entails(always(lift_state(cr_objects_in_etcd_satisfy_state_validation()))),
{
    let inv = cr_objects_in_etcd_satisfy_state_validation();
    FluentBitConfigView::marshal_status_preserves_integrity();
    init_invariant(spec, FBCCluster::init(), FBCCluster::next(), inv);
}

pub proof fn lemma_always_the_object_in_schedule_satisfies_state_validation(spec: TempPred<FBCCluster>)
    requires
        spec.entails(lift_state(FBCCluster::init())),
        spec.entails(always(lift_action(FBCCluster::next()))),
    ensures spec.entails(always(lift_state(the_object_in_schedule_satisfies_state_validation()))),
{
    let inv = the_object_in_schedule_satisfies_state_validation();
    let stronger_next = |s: FBCCluster, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& cr_objects_in_etcd_satisfy_state_validation()(s)
    };
    lemma_always_cr_objects_in_etcd_satisfy_state_validation(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(cr_objects_in_etcd_satisfy_state_validation())
    );
    init_invariant(spec, FBCCluster::init(), stronger_next, inv);
}

pub proof fn lemma_always_the_object_in_reconcile_satisfies_state_validation(spec: TempPred<FBCCluster>, key: ObjectRef)
    requires
        spec.entails(lift_state(FBCCluster::init())),
        spec.entails(always(lift_action(FBCCluster::next()))),
    ensures spec.entails(always(lift_state(the_object_in_reconcile_satisfies_state_validation(key)))),
{
    let inv = the_object_in_reconcile_satisfies_state_validation(key);
    let stronger_next = |s: FBCCluster, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& the_object_in_schedule_satisfies_state_validation()(s)
    };
    lemma_always_the_object_in_schedule_satisfies_state_validation(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(the_object_in_schedule_satisfies_state_validation())
    );
    init_invariant(spec, FBCCluster::init(), stronger_next, inv);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        spec.entails(lift_state(FBCCluster::init())),
        spec.entails(always(lift_action(FBCCluster::next()))),
    ensures spec.entails(always(lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, fbc)))),
{
    let inv = response_at_after_get_resource_step_is_resource_get_response(sub_resource, fbc);
    let key = fbc.object_ref();
    let resource_key = get_request(sub_resource, fbc).key;
    let next = |s, s_prime| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)(s_prime)
    };
    FBCCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    FBCCluster::lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(spec, key);
    always_to_always_later(spec, lift_state(FBCCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(FBCCluster::next()),
        lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        later(lift_state(FBCCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)))
    );
    assert forall |s: FBCCluster, s_prime: FBCCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if at_fbc_step(key, FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s_prime) {
            let step = choose |step| FBCCluster::next_step(s, s_prime, step);
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
    init_invariant(spec, FBCCluster::init(), next, inv);
}

pub proof fn lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step_forall(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)))),
        spec.entails(always(lift_state(FBCCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(FBCCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, fbc).key))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, fbc))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fbc))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(no_update_status_request_msg_in_flight(sub_resource, fbc))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(FBCCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, fbc).key)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(response_at_after_get_resource_step_is_resource_get_response(res, fbc)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_delete_resource_request_msg_in_flight(res, fbc)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_update_status_request_msg_in_flight(res, fbc)), sub_resource);
        lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step(spec, sub_resource, fbc);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)))),
        spec.entails(always(lift_state(FBCCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, fbc).key)))),
        spec.entails(always(lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, fbc)))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fbc)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight(sub_resource, fbc)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc))))),
{
    let key = fbc.object_ref();
    let resource_key = get_request(sub_resource, fbc).key;
    let requirements = |msg: FBCMessage, s: FBCCluster| {
        resource_update_request_msg(resource_key)(msg) ==> {
            &&& at_fbc_step(key, FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& FBCCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.resource_version.is_Some()
            &&& msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
            &&& (
                s.resources().contains_key(resource_key)
                && msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
            ) ==> (
                update(sub_resource, fbc, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).is_Ok()
                && msg.content.get_update_request().obj == update(sub_resource, fbc, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).get_Ok_0()
            )
        }
    };
    let stronger_next = |s: FBCCluster, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
        &&& FBCCluster::busy_disabled()(s)
        &&& FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCCluster::every_in_flight_msg_has_unique_id()(s)
        &&& FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)(s)
        &&& FBCCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
        &&& FBCCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& FBCCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, fbc).key)(s)
        &&& response_at_after_get_resource_step_is_resource_get_response(sub_resource, fbc)(s)
        &&& no_delete_resource_request_msg_in_flight(sub_resource, fbc)(s)
        &&& no_update_status_request_msg_in_flight(sub_resource, fbc)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies FBCCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: FBCMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_update_request_msg(resource_key)(msg) {
                let step = choose |step| FBCCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fbc, s, s_prime, msg, step);
                    let resp = step.get_ControllerStep_0().0.get_Some_0();
                    assert(FBCCluster::is_ok_get_response_msg()(resp));
                    assert(s.in_flight().contains(resp));
                    assert(resp.content.get_get_response().res.get_Ok_0().metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version);
                    if s.resources().contains_key(resource_key) && resp.content.get_get_response().res.get_Ok_0().metadata.resource_version == s.resources()[resource_key].metadata.resource_version {
                        assert(resp.content.get_get_response().res.get_Ok_0() == s.resources()[resource_key]);
                        assert(s_prime.resources()[resource_key] == s.resources()[resource_key]);
                    }
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(FBCCluster::each_object_in_etcd_is_well_formed()));
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(FBCCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(FBCCluster::next()), lift_state(FBCCluster::crash_disabled()), lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)),
        lift_state(FBCCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(FBCCluster::each_object_in_etcd_is_well_formed())),
        lift_state(FBCCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, fbc).key)),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, fbc)),
        lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fbc)),
        lift_state(no_update_status_request_msg_in_flight(sub_resource, fbc))
    );

    FBCCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fbc)),
        lift_state(FBCCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub proof fn lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr_forall(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)))),
    ensures
        spec.entails(true_pred().leads_to(
            always(tla_forall(|sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fbc)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fbc))))) by {
        lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(spec, sub_resource, fbc);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fbc)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fbc))))),
{
    let key = fbc.object_ref();
    let resource_key = get_request(sub_resource, fbc).key;
    let requirements = |msg: FBCMessage, s: FBCCluster| {
        resource_update_request_msg(resource_key)(msg) ==> {
            &&& at_fbc_step(key, FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& FBCCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.owner_references_only_contains(fbc.controller_owner_ref())
        }
    };
    let stronger_next = |s: FBCCluster, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
        &&& FBCCluster::busy_disabled()(s)
        &&& FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCCluster::every_in_flight_msg_has_unique_id()(s)
        &&& FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies FBCCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: FBCMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_update_request_msg(resource_key)(msg) {
                let step = choose |step| FBCCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fbc, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(FBCCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(FBCCluster::next()), lift_state(FBCCluster::crash_disabled()), lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc))
    );

    FBCCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fbc)),
        lift_state(FBCCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub proof fn lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step_forall(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)))),
        spec.entails(always(lift_state(fbc_is_well_formed(fbc)))),
    ensures
        spec.entails(true_pred().leads_to(
            always(tla_forall(|sub_resource: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc))))) by {
        lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step(spec, sub_resource, fbc);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)))),
        spec.entails(always(lift_state(fbc_is_well_formed(fbc)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc))))),
{
    let key = fbc.object_ref();
    let resource_key = get_request(sub_resource, fbc).key;
    let requirements = |msg: FBCMessage, s: FBCCluster| {
        resource_create_request_msg(resource_key)(msg) ==> {
            &&& at_fbc_step(key, FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
            &&& FBCCluster::pending_req_msg_is(s, key, msg)
            &&& make(sub_resource, fbc, s.ongoing_reconciles()[key].local_state).is_Ok()
            &&& msg.content.get_create_request().obj == make(sub_resource, fbc, s.ongoing_reconciles()[key].local_state).get_Ok_0()
        }
    };
    let stronger_next = |s: FBCCluster, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::crash_disabled()(s)
        &&& FBCCluster::busy_disabled()(s)
        &&& FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCCluster::every_in_flight_msg_has_unique_id()(s)
        &&& FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)(s)
        &&& fbc_is_well_formed(fbc)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies FBCCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: FBCMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_create_request_msg(resource_key)(msg) {
                let step = choose |step| FBCCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fbc, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(FBCCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(FBCCluster::next()), lift_state(FBCCluster::crash_disabled()), lift_state(FBCCluster::busy_disabled()),
        lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCCluster::the_object_in_reconcile_has_spec_and_uid_as(fbc)),
        lift_state(fbc_is_well_formed(fbc))
    );

    FBCCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)),
        lift_state(FBCCluster::every_in_flight_req_msg_satisfies(requirements)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_no_update_status_request_msg_in_flight(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        spec.entails(lift_state(FBCCluster::init())),
        spec.entails(always(lift_action(FBCCluster::next()))),
    ensures spec.entails(always(lift_state(no_update_status_request_msg_in_flight(sub_resource, fbc)))),
{
    FBCCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    let inv = no_update_status_request_msg_in_flight(sub_resource, fbc);
    let stronger_next = |s: FBCCluster, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::each_object_in_etcd_is_well_formed()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed())
    );

    let resource_key = get_request(sub_resource, fbc).key;
    assert forall |s, s_prime: FBCCluster| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: FBCMessage| #[trigger] s_prime.in_flight().contains(msg) && msg.content.is_update_status_request()
        implies msg.content.get_update_status_request().key() != resource_key by {
            if s.in_flight().contains(msg) {
                assert(msg.content.get_update_status_request().key() != resource_key);
            } else {
                let step = choose |step: FBCStep| FBCCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        if input.1.is_Some() {
                            let cr_key = input.1.get_Some_0();
                            if s.ongoing_reconciles().contains_key(cr_key) {
                                match s.ongoing_reconciles()[cr_key].local_state.reconcile_step {
                                    FluentBitConfigReconcileStep::Init => {},
                                    FluentBitConfigReconcileStep::AfterKRequestStep(_, resource) => {
                                        match resource {
                                            SubResource::Secret => {},
                                        }
                                    },
                                    _ => {}
                                }
                            } else {}
                        } else {}
                        assert(!msg.content.is_update_status_request());
                        assert(false);
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
                        assert(msg.content.get_update_status_request().key().kind == Kind::StatefulSetKind
                            || msg.content.get_update_status_request().key().kind == Kind::DaemonSetKind);
                        assert(msg.content.get_update_status_request().key() != resource_key);
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
    init_invariant(spec, FBCCluster::init(), stronger_next, inv);
}

spec fn make_owner_references_with_name_and_uid(name: StringView, uid: Uid) -> OwnerReferenceView {
    OwnerReferenceView {
        block_owner_deletion: None,
        controller: Some(true),
        kind: FluentBitConfigView::kind(),
        name: name,
        uid: uid,
    }
}

pub proof fn lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        spec.entails(lift_state(FBCCluster::init())),
        spec.entails(always(lift_action(FBCCluster::next()))),
    ensures spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)))),
{
    let inv = resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc);
    lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(spec, sub_resource, fbc);
    let stronger_next = |s, s_prime| {
        &&& FBCCluster::next()(s, s_prime)
        &&& resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, fbc)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, fbc))
    );
    init_invariant(spec, FBCCluster::init(), stronger_next, inv);
}

spec fn resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(
    sub_resource: SubResource, fbc: FluentBitConfigView
) -> StatePred<FBCCluster> {
    |s: FBCCluster| {
        let key = fbc.object_ref();
        let resource_key = get_request(sub_resource, fbc).key;
        forall |msg: FBCMessage| {
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
proof fn lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        spec.entails(lift_state(FBCCluster::init())),
        spec.entails(always(lift_action(FBCCluster::next()))),
    ensures spec.entails(always(lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, fbc)))),
{
    let inv = resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, fbc);
    let stronger_next = |s, s_prime| {
        &&& FBCCluster::next()(s, s_prime)
        &&& FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };
    let key = fbc.object_ref();
    let resource_key = get_request(sub_resource, fbc).key;
    FBCCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCCluster::next()),
        lift_state(FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    let create_msg_pred = |msg: FBCMessage| {
        resource_create_request_msg(resource_key)(msg)
        ==> msg.content.get_create_request().obj.metadata.finalizers.is_None()
            && exists |uid: Uid| #![auto]
                msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                    make_owner_references_with_name_and_uid(key.name, uid)
                ])
    };
    let update_msg_pred = |msg: FBCMessage| {
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
                let step = choose |step| FBCCluster::next_step(s, s_prime, step);
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fbc, s, s_prime, msg, step);
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
    init_invariant(spec, FBCCluster::init(), stronger_next, inv);
}

/// This lemma is used to show that if an action (which transfers the state from s to s_prime) creates a sub resource object
/// create/update request message (with key as key), it must be a controller action, and the triggering cr is s.ongoing_reconciles()[key].triggering_cr.
///
/// After the action, the controller stays at After(Create/Update, SubResource) step.
///
/// Tips: Talking about both s and s_prime give more information to those using this lemma and also makes the verification faster.
#[verifier(spinoff_prover)]
pub proof fn lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource: SubResource, fbc: FluentBitConfigView, s: FBCCluster, s_prime: FBCCluster, msg: FBCMessage, step: FBCStep)
    requires
        !s.in_flight().contains(msg), s_prime.in_flight().contains(msg),
        FBCCluster::next_step(s, s_prime, step),
        FBCCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
    ensures
        resource_create_request_msg(get_request(sub_resource, fbc).key)(msg)
        ==> step.is_ControllerStep() && step.get_ControllerStep_0().1.get_Some_0() == fbc.object_ref()
            && at_fbc_step(fbc.object_ref(), FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
            && at_fbc_step(fbc.object_ref(), FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s_prime)
            && FBCCluster::pending_req_msg_is(s_prime, fbc.object_ref(), msg),
        resource_update_request_msg(get_request(sub_resource, fbc).key)(msg)
        ==> step.is_ControllerStep() && step.get_ControllerStep_0().1.get_Some_0() == fbc.object_ref()
            && at_fbc_step(fbc.object_ref(), FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
            && at_fbc_step(fbc.object_ref(), FluentBitConfigReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s_prime)
            && FBCCluster::pending_req_msg_is(s_prime, fbc.object_ref(), msg),
{
    // Since we know that this step creates a create server config map message, it is easy to see that it's a controller action.
    // This action creates a config map, and there are two kinds of config maps, we have to show that only server config map
    // is possible by extra reasoning about the strings.
    let cr_key = step.get_ControllerStep_0().1.get_Some_0();
    let key = fbc.object_ref();
    let cr = s.ongoing_reconciles()[key].triggering_cr;
    let resource_key = get_request(sub_resource, fbc).key;
    if resource_create_request_msg(get_request(sub_resource, fbc).key)(msg) || resource_update_request_msg(get_request(sub_resource, fbc).key)(msg) {
        assert(step.is_ControllerStep());
        assert(s.ongoing_reconciles().contains_key(cr_key));
        let local_step = s.ongoing_reconciles()[cr_key].local_state.reconcile_step;
        let local_step_prime = s_prime.ongoing_reconciles()[cr_key].local_state.reconcile_step;
        assert(local_step_prime.is_AfterKRequestStep());
        assert(local_step.is_AfterKRequestStep() && local_step.get_AfterKRequestStep_0() == ActionKind::Get);
        if resource_create_request_msg(get_request(sub_resource, fbc).key)(msg) {
            assert(local_step_prime.get_AfterKRequestStep_0() == ActionKind::Create);
        }
        if resource_update_request_msg(get_request(sub_resource, fbc).key)(msg) {
            assert(local_step_prime.get_AfterKRequestStep_0() == ActionKind::Update);
        }
        assert_by(
            cr_key == fbc.object_ref() && local_step.get_AfterKRequestStep_1() == sub_resource && FBCCluster::pending_req_msg_is(s_prime, cr_key, msg),
            {
                // It's easy for the verifier to know that cr_key has the same kind and namespace as key.
                match sub_resource {
                    _ => {}
                }
            }
        )
    }
}

pub proof fn lemma_eventually_always_no_delete_resource_request_msg_in_flight_forall(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fbc)))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fbc)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] no_delete_resource_request_msg_in_flight(sub_resource, fbc))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(res, fbc)), sub_resource);
        lemma_eventually_always_no_delete_resource_request_msg_in_flight(spec, sub_resource, fbc);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fbc)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_no_delete_resource_request_msg_in_flight(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_state(FBCCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fbc)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fbc))))),
{
    let key = fbc.object_ref();
    let resource_key = get_request(sub_resource, fbc).key;
    let requirements = |msg: FBCMessage, s: FBCCluster| !{
        &&& msg.dst.is_ApiServer()
        &&& msg.content.is_delete_request()
        &&& msg.content.get_delete_request().key == resource_key
    };

    let stronger_next = |s: FBCCluster, s_prime: FBCCluster| {
        &&& FBCCluster::next()(s, s_prime)
        &&& desired_state_is(fbc)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc)(s)
        &&& FBCCluster::each_object_in_etcd_is_well_formed()(s)
    };
    assert forall |s: FBCCluster, s_prime: FBCCluster| #[trigger] stronger_next(s, s_prime) implies FBCCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: FBCMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.in_flight().contains(msg) {
                assert(requirements(msg, s));
                assert(requirements(msg, s_prime));
            } else {
                let step = choose |step| FBCCluster::next_step(s, s_prime, step);
                match step {
                    Step::BuiltinControllersStep(_) => {
                        if s.resources().contains_key(resource_key) {
                            let owner_refs = s.resources()[resource_key].metadata.owner_references;
                            assert(owner_refs == Some(seq![fbc.controller_owner_ref()]));
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
        spec, lift_action(stronger_next), lift_action(FBCCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(FBCCluster::next()), lift_state(desired_state_is(fbc)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc)),
        lift_state(FBCCluster::each_object_in_etcd_is_well_formed())
    );

    FBCCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fbc)),
        lift_state(FBCCluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr_forall(spec: TempPred<FBCCluster>, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fbc)))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource|lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fbc))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| (lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc))))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, fbc)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(every_resource_create_request_implies_at_after_create_resource_step(res, fbc)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(res, fbc)), sub_resource);
        lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(spec, sub_resource, fbc);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(spec: TempPred<FBCCluster>, sub_resource: SubResource, fbc: FluentBitConfigView)
    requires
        spec.entails(always(lift_state(FBCCluster::busy_disabled()))),
        spec.entails(always(lift_action(FBCCluster::next()))),
        spec.entails(tla_forall(|i| FBCCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fbc)))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)))),
        spec.entails(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fbc)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc))))),
{
    let key = get_request(sub_resource, fbc).key;
    let eventual_owner_ref = |owner_ref: Option<Seq<OwnerReferenceView>>| {owner_ref == Some(seq![fbc.controller_owner_ref()])};
    always_weaken_temp(spec, lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fbc)), lift_state(FBCCluster::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)));
    always_weaken_temp(spec, lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fbc)), lift_state(FBCCluster::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)));
    always_weaken_temp(spec, lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)), lift_state(FBCCluster::object_has_no_finalizers(key)));

    let state = |s: FBCCluster| {
        desired_state_is(fbc)(s)
        && resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc)(s)
    };
    invariant_n!(
        spec, lift_state(state), lift_state(FBCCluster::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(FBCCluster::garbage_collector_deletion_enabled(key))),
        lift_state(desired_state_is(fbc)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fbc))
    );
    FBCCluster::lemma_eventually_objects_owner_references_satisfies(spec, key, eventual_owner_ref);
    temp_pred_equality(
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fbc)),
        lift_state(FBCCluster::objects_owner_references_satisfies(key, eventual_owner_ref))
    );
}

pub proof fn leads_to_always_tla_forall_subresource(spec: TempPred<FBCCluster>, p: TempPred<FBCCluster>, a_to_p: spec_fn(SubResource)->TempPred<FBCCluster>)
    requires forall |a: SubResource| spec.entails(p.leads_to(always(#[trigger] a_to_p(a)))),
    ensures spec.entails(p.leads_to(always(tla_forall(a_to_p)))),
{
    leads_to_always_tla_forall(
        spec, p, a_to_p,
        set![SubResource::Secret]
    );
}

}
