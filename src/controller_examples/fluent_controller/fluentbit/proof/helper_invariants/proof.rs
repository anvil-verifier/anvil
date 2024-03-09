// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::predicate::*;
use crate::fluent_controller::fluentbit::{
    model::resource::*,
    proof::{
        helper_invariants::daemon_set_in_etcd_satisfies_unchangeable, predicate::*, resource::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*},
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

pub proof fn lemma_always_fb_is_well_formed(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_state(desired_state_is(fb)))),
        spec.entails(always(lift_state(FBCluster::each_object_in_etcd_is_well_formed()))),
    ensures spec.entails(always(lift_state(fb_is_well_formed(fb)))),
{
    let stronger_inv = |s: FBCluster| {
        &&& desired_state_is(fb)(s)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
    };

    invariant_n!(
        spec, lift_state(stronger_inv),
        lift_state(fb_is_well_formed(fb)),
        lift_state(desired_state_is(fb)),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed())
    );
}

pub proof fn lemma_always_cr_objects_in_etcd_satisfy_state_validation(spec: TempPred<FBCluster>)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(cr_objects_in_etcd_satisfy_state_validation()))),
{
    let inv = cr_objects_in_etcd_satisfy_state_validation();
    FluentBitView::marshal_status_preserves_integrity();
    init_invariant(spec, FBCluster::init(), FBCluster::next(), inv);
}

pub proof fn lemma_always_the_object_in_schedule_satisfies_state_validation(spec: TempPred<FBCluster>)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(the_object_in_schedule_satisfies_state_validation()))),
{
    let inv = the_object_in_schedule_satisfies_state_validation();
    let stronger_next = |s: FBCluster, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& cr_objects_in_etcd_satisfy_state_validation()(s)
    };
    lemma_always_cr_objects_in_etcd_satisfy_state_validation(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(cr_objects_in_etcd_satisfy_state_validation())
    );
    init_invariant(spec, FBCluster::init(), stronger_next, inv);
}

pub proof fn lemma_always_the_object_in_reconcile_satisfies_state_validation(spec: TempPred<FBCluster>, key: ObjectRef)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(the_object_in_reconcile_satisfies_state_validation(key)))),
{
    let inv = the_object_in_reconcile_satisfies_state_validation(key);
    let stronger_next = |s: FBCluster, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& the_object_in_schedule_satisfies_state_validation()(s)
    };
    lemma_always_the_object_in_schedule_satisfies_state_validation(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(the_object_in_schedule_satisfies_state_validation())
    );
    init_invariant(spec, FBCluster::init(), stronger_next, inv);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, fb)))),
{
    let inv = response_at_after_get_resource_step_is_resource_get_response(sub_resource, fb);
    let key = fb.object_ref();
    let resource_key = get_request(sub_resource, fb).key;
    let next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)(s_prime)
    };
    FBCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    FBCluster::lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(spec, key);
    always_to_always_later(spec, lift_state(FBCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(FBCluster::next()),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        later(lift_state(FBCluster::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(key)))
    );
    assert forall |s: FBCluster, s_prime: FBCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if at_fb_step(key, FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s_prime) {
            let step = choose |step| FBCluster::next_step(s, s_prime, step);
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
    init_invariant(spec, FBCluster::init(), next, inv);
}

pub proof fn lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step_forall(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)))),
        spec.entails(always(lift_state(FBCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(FBCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, fb).key))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, fb))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fb))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(no_update_status_request_msg_in_flight_of_except_daemon_set(sub_resource, fb))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fb)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fb))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(res, fb).key)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(response_at_after_get_resource_step_is_resource_get_response(res, fb)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_delete_resource_request_msg_in_flight(res, fb)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(no_update_status_request_msg_in_flight_of_except_daemon_set(res, fb)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(res, fb)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(res, fb)), sub_resource);
        lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step(spec, sub_resource, fb);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fb)));
}

#[verifier(spinoff_prover)]
pub proof fn make_fluentbit_pod_spec_determined_by_spec_and_name(fb1: FluentBitView, fb2: FluentBitView)
    requires
        fb1.metadata.name.get_Some_0() == fb2.metadata.name.get_Some_0(),
        fb1.spec == fb2.spec,
    ensures make_fluentbit_pod_spec(fb1) == make_fluentbit_pod_spec(fb2),
{}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_every_resource_update_request_implies_at_after_update_resource_step(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)))),
        spec.entails(always(lift_state(FBCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
        spec.entails(always(lift_state(FBCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, fb).key)))),
        spec.entails(always(lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, fb)))),
        spec.entails(always(lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fb)))),
        spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_daemon_set(sub_resource, fb)))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fb))))),
{
    hide(make_fluentbit_pod_spec);
    let key = fb.object_ref();
    let resource_key = get_request(sub_resource, fb).key;
    let requirements = |msg: FBMessage, s: FBCluster| {
        resource_update_request_msg(resource_key)(msg) ==> {
            &&& at_fb_step(key, FluentBitReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& FBCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.resource_version.is_Some()
            &&& msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
            &&& (
                s.resources().contains_key(resource_key)
                && msg.content.get_update_request().obj.metadata.resource_version == s.resources()[resource_key].metadata.resource_version
            ) ==> (
                update(sub_resource, fb, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).is_Ok()
                && msg.content.get_update_request().obj == update(sub_resource, fb, s.ongoing_reconciles()[key].local_state, s.resources()[resource_key]).get_Ok_0()
            )
        }
    };
    let well_formed = |s: FBCluster| {
        s.resources().contains_key(resource_key) ==> FBCluster::etcd_object_is_well_formed(resource_key)(s)
    };
    let stronger_next = |s: FBCluster, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::crash_disabled()(s)
        &&& FBCluster::busy_disabled()(s)
        &&& FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCluster::every_in_flight_msg_has_unique_id()(s)
        &&& FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)(s)
        &&& FBCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
        &&& well_formed(s)
        &&& well_formed(s_prime)
        &&& FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, fb).key)(s)
        &&& response_at_after_get_resource_step_is_resource_get_response(sub_resource, fb)(s)
        &&& no_delete_resource_request_msg_in_flight(sub_resource, fb)(s)
        &&& no_update_status_request_msg_in_flight_of_except_daemon_set(sub_resource, fb)(s)
        &&& object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies FBCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: FBMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_update_request_msg(resource_key)(msg) {
                let step = choose |step| FBCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fb, s, s_prime, msg, step);
                    make_fluentbit_pod_spec_determined_by_spec_and_name(fb, s.ongoing_reconciles()[key].triggering_cr);
                    let resp = step.get_ControllerStep_0().0.get_Some_0();
                    assert(FBCluster::is_ok_get_response_msg()(resp));
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
    always_to_always_later(spec, lift_state(FBCluster::each_object_in_etcd_is_well_formed()));
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(FBCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(FBCluster::next()), lift_state(FBCluster::crash_disabled()), lift_state(FBCluster::busy_disabled()),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)),
        lift_state(FBCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(FBCluster::each_object_in_etcd_is_well_formed())),
        lift_state(FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, fb).key)),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, fb)),
        lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fb)),
        lift_state(no_update_status_request_msg_in_flight_of_except_daemon_set(sub_resource, fb)),
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb))
    );

    FBCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_resource_update_request_implies_at_after_update_resource_step(sub_resource, fb)),
        lift_state(FBCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub proof fn lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr_forall(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb))))) by {
        lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(spec, sub_resource, fb);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb))))),
{
    let key = fb.object_ref();
    let resource_key = get_request(sub_resource, fb).key;
    let requirements = |msg: FBMessage, s: FBCluster| {
        resource_update_request_msg(resource_key)(msg) ==> {
            &&& at_fb_step(key, FluentBitReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& FBCluster::pending_req_msg_is(s, key, msg)
            &&& msg.content.get_update_request().obj.metadata.owner_references_only_contains(fb.controller_owner_ref())
        }
    };
    let stronger_next = |s: FBCluster, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::crash_disabled()(s)
        &&& FBCluster::busy_disabled()(s)
        &&& FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCluster::every_in_flight_msg_has_unique_id()(s)
        &&& FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies FBCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: FBMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_update_request_msg(resource_key)(msg) {
                let step = choose |step| FBCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fb, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(FBCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(FBCluster::next()), lift_state(FBCluster::crash_disabled()), lift_state(FBCluster::busy_disabled()),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb))
    );

    FBCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb)),
        lift_state(FBCluster::every_in_flight_req_msg_satisfies(requirements)));
}

pub proof fn lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step_forall(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)))),
        spec.entails(always(lift_state(fb_is_well_formed(fb)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb))))) by {
        lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step(spec, sub_resource, fb);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_every_resource_create_request_implies_at_after_create_resource_step(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCluster::crash_disabled()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)))),
        spec.entails(always(lift_state(fb_is_well_formed(fb)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb))))),
{
    hide(make_fluentbit_pod_spec);
    let key = fb.object_ref();
    let resource_key = get_request(sub_resource, fb).key;
    let requirements = |msg: FBMessage, s: FBCluster| {
        resource_create_request_msg(resource_key)(msg) ==> {
            &&& at_fb_step(key, FluentBitReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s)
            &&& FBCluster::pending_req_msg_is(s, key, msg)
            &&& make(sub_resource, fb, s.ongoing_reconciles()[key].local_state).is_Ok()
            &&& msg.content.get_create_request().obj == make(sub_resource, fb, s.ongoing_reconciles()[key].local_state).get_Ok_0()
        }
    };
    let stronger_next = |s: FBCluster, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::crash_disabled()(s)
        &&& FBCluster::busy_disabled()(s)
        &&& FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCluster::every_in_flight_msg_has_unique_id()(s)
        &&& FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)(s)
        &&& fb_is_well_formed(fb)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies FBCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: FBMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if resource_create_request_msg(resource_key)(msg) {
                let step = choose |step| FBCluster::next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fb, s, s_prime, msg, step);
                    make_fluentbit_pod_spec_determined_by_spec_and_name(fb, s.ongoing_reconciles()[key].triggering_cr);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles()[key] == s_prime.ongoing_reconciles()[key]);
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(stronger_next), lift_action(FBCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(FBCluster::next()), lift_state(FBCluster::crash_disabled()), lift_state(FBCluster::busy_disabled()),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCluster::every_in_flight_msg_has_unique_id()),
        lift_state(FBCluster::the_object_in_reconcile_has_spec_and_uid_as(fb)),
        lift_state(fb_is_well_formed(fb))
    );

    FBCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb)),
        lift_state(FBCluster::every_in_flight_req_msg_satisfies(requirements)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_no_update_status_request_msg_in_flight_of_except_daemon_set(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(no_update_status_request_msg_in_flight_of_except_daemon_set(sub_resource, fb)))),
{
    FBCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    let inv = no_update_status_request_msg_in_flight_of_except_daemon_set(sub_resource, fb);
    let stronger_next = |s: FBCluster, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed())
    );

    let resource_key = get_request(sub_resource, fb).key;
    assert forall |s, s_prime: FBCluster| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        if sub_resource != SubResource::DaemonSet {
            assert forall |msg: FBMessage| s_prime.in_flight().contains(msg) implies !(#[trigger] resource_update_status_request_msg(resource_key)(msg)) by {
                if s.in_flight().contains(msg) {
                    assert(!resource_update_status_request_msg(resource_key)(msg));
                } else {
                    let step = choose |step: FBStep| FBCluster::next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep(input) => {
                            if input.1.is_Some() {
                                let cr_key = input.1.get_Some_0();
                                if s.ongoing_reconciles().contains_key(cr_key) {
                                    match s.ongoing_reconciles()[cr_key].local_state.reconcile_step {
                                        FluentBitReconcileStep::Init => {},
                                        FluentBitReconcileStep::AfterKRequestStep(_, resource) => {
                                            match resource {
                                                SubResource::ServiceAccount => {},
                                                SubResource::Role => {},
                                                SubResource::RoleBinding => {},
                                                SubResource::Service => {},
                                                SubResource::DaemonSet => {},
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
    init_invariant(spec, FBCluster::init(), stronger_next, inv);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_no_update_status_request_msg_not_from_bc_in_flight_of_daemon_set(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(no_update_status_request_msg_not_from_bc_in_flight_of_daemon_set(fb)))),
{
    FBCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    let inv = no_update_status_request_msg_not_from_bc_in_flight_of_daemon_set(fb);
    let stronger_next = |s: FBCluster, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed())
    );

    let resource_key = get_request(SubResource::DaemonSet, fb).key;
    assert forall |s, s_prime: FBCluster| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: FBMessage| #[trigger] s_prime.in_flight().contains(msg) && msg.dst.is_ApiServer() && !msg.src.is_BuiltinController() && msg.content.is_update_status_request()
        implies msg.content.get_update_status_request().key() != resource_key by {
            if s.in_flight().contains(msg) {
                assert(msg.content.get_update_status_request().key() != resource_key);
            } else {
                let step = choose |step: FBStep| FBCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        if input.1.is_Some() {
                            let cr_key = input.1.get_Some_0();
                            if s.ongoing_reconciles().contains_key(cr_key) {
                                match s.ongoing_reconciles()[cr_key].local_state.reconcile_step {
                                    FluentBitReconcileStep::Init => {},
                                    FluentBitReconcileStep::AfterKRequestStep(_, resource) => {
                                        match resource {
                                            SubResource::ServiceAccount => {},
                                            SubResource::Role => {},
                                            SubResource::RoleBinding => {},
                                            SubResource::Service => {},
                                            SubResource::DaemonSet => {},
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
    init_invariant(spec, FBCluster::init(), stronger_next, inv);
}

spec fn make_owner_references_with_name_and_uid(name: StringView, uid: Uid) -> OwnerReferenceView {
    OwnerReferenceView {
        block_owner_deletion: None,
        controller: Some(true),
        kind: FluentBitView::kind(),
        name: name,
        uid: uid,
    }
}

pub proof fn lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fb)))),
{
    let inv = resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fb);
    lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(spec, sub_resource, fb);
    let stronger_next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, fb)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, fb))
    );
    init_invariant(spec, FBCluster::init(), stronger_next, inv);
}

spec fn resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(
    sub_resource: SubResource, fb: FluentBitView
) -> StatePred<FBCluster> {
    |s: FBCluster| {
        let key = fb.object_ref();
        let resource_key = get_request(sub_resource, fb).key;
        forall |msg: FBMessage| {
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
proof fn lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, fb)))),
{
    let inv = resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers(sub_resource, fb);
    let stronger_next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };
    let key = fb.object_ref();
    let resource_key = get_request(sub_resource, fb).key;
    FBCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(FBCluster::next()),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    let create_msg_pred = |msg: FBMessage| {
        resource_create_request_msg(resource_key)(msg)
        ==> msg.content.get_create_request().obj.metadata.finalizers.is_None()
            && exists |uid: Uid| #![auto]
                msg.content.get_create_request().obj.metadata.owner_references == Some(seq![
                    make_owner_references_with_name_and_uid(key.name, uid)
                ])
    };
    let update_msg_pred = |msg: FBMessage| {
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
                let step = choose |step| FBCluster::next_step(s, s_prime, step);
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fb, s, s_prime, msg, step);
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
    init_invariant(spec, FBCluster::init(), stronger_next, inv);
}

/// This lemma is used to show that if an action (which transfers the state from s to s_prime) creates a sub resource object
/// create/update request message (with key as key), it must be a controller action, and the triggering cr is s.ongoing_reconciles()[key].triggering_cr.
///
/// After the action, the controller stays at After(Create/Update, SubResource) step.
///
/// Tips: Talking about both s and s_prime give more information to those using this lemma and also makes the verification faster.
#[verifier(spinoff_prover)]
pub proof fn lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource: SubResource, fb: FluentBitView, s: FBCluster, s_prime: FBCluster, msg: FBMessage, step: FBStep)
    requires
        !s.in_flight().contains(msg), s_prime.in_flight().contains(msg),
        FBCluster::next_step(s, s_prime, step),
        FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
    ensures
        resource_create_request_msg(get_request(sub_resource, fb).key)(msg)
        ==> step.is_ControllerStep() && step.get_ControllerStep_0().1.get_Some_0() == fb.object_ref()
            && at_fb_step(fb.object_ref(), FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
            && at_fb_step(fb.object_ref(), FluentBitReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s_prime)
            && FBCluster::pending_req_msg_is(s_prime, fb.object_ref(), msg),
        resource_update_request_msg(get_request(sub_resource, fb).key)(msg)
        ==> step.is_ControllerStep() && step.get_ControllerStep_0().1.get_Some_0() == fb.object_ref()
            && at_fb_step(fb.object_ref(), FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s)
            && at_fb_step(fb.object_ref(), FluentBitReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s_prime)
            && FBCluster::pending_req_msg_is(s_prime, fb.object_ref(), msg),
{
    hide(make_fluentbit_pod_spec);
    // Since we know that this step creates a create server config map message, it is easy to see that it's a controller action.
    // This action creates a config map, and there are two kinds of config maps, we have to show that only server config map
    // is possible by extra reasoning about the strings.
    let cr_key = step.get_ControllerStep_0().1.get_Some_0();
    let key = fb.object_ref();
    let cr = s.ongoing_reconciles()[key].triggering_cr;
    let resource_key = get_request(sub_resource, fb).key;
    if resource_create_request_msg(get_request(sub_resource, fb).key)(msg) || resource_update_request_msg(get_request(sub_resource, fb).key)(msg) {
        assert(step.is_ControllerStep());
        assert(s.ongoing_reconciles().contains_key(cr_key));
        let local_step = s.ongoing_reconciles()[cr_key].local_state.reconcile_step;
        let local_step_prime = s_prime.ongoing_reconciles()[cr_key].local_state.reconcile_step;
        assert(local_step_prime.is_AfterKRequestStep());
        assert(local_step.is_AfterKRequestStep() && local_step.get_AfterKRequestStep_0() == ActionKind::Get);
        if resource_create_request_msg(get_request(sub_resource, fb).key)(msg) {
            assert(local_step_prime.get_AfterKRequestStep_0() == ActionKind::Create);
        }
        if resource_update_request_msg(get_request(sub_resource, fb).key)(msg) {
            assert(local_step_prime.get_AfterKRequestStep_0() == ActionKind::Update);
        }
        assert_by(
            cr_key == fb.object_ref() && local_step.get_AfterKRequestStep_1() == sub_resource && FBCluster::pending_req_msg_is(s_prime, cr_key, msg),
            {
                // It's easy for the verifier to know that cr_key has the same kind and namespace as key.
                match sub_resource {
                    SubResource::RoleBinding => {
                        seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-role-binding")@);
                    },
                    SubResource::Role => {
                        seq_lib::seq_equal_preserved_by_add(key.name, cr_key.name, new_strlit("-role")@);
                    },
                    _ => {}
                }
            }
        )
    }
}

pub proof fn lemma_eventually_always_no_delete_resource_request_msg_in_flight_forall(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_state(FBCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fb)))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fb)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] no_delete_resource_request_msg_in_flight(sub_resource, fb))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(res, fb)), sub_resource);
        lemma_eventually_always_no_delete_resource_request_msg_in_flight(spec, sub_resource, fb);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fb)));
}

/// This lemma demonstrates how to use kubernetes_cluster::proof::api_server_liveness::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies
/// (referred to as lemma_X) to prove that the system will eventually enter a state where delete daemon set request messages
/// will never appear in flight.
///
/// As an example, we can look at how this lemma is proved.
/// - Precondition: The preconditions should include all precondtions used by lemma_X and other predicates which show that
///     the newly generated messages are as expected. ("expected" means not delete daemon set request messages in this lemma. Therefore,
///     we provide an invariant daemon_set_has_owner_reference_pointing_to_current_cr so that the grabage collector won't try
///     to send a delete request to delete the messsage.)
/// - Postcondition: spec |= true ~> [](forall |msg| as_expected(msg))
/// - Proof body: The proof consists of three parts.
///   + Come up with "requirements" for those newly created api request messages. Usually, just move the forall |msg| and
///     s.in_flight().contains(msg) in the statepred of final state (no_delete_ds_req_is_in_flight in this lemma, so we can
///     get the requirements in this lemma).
///   + Show that spec |= every_new_req_msg_if_in_flight_then_satisfies. Basically, use two assert forall to show that forall state and
///     its next state and forall messages, if the messages are newly generated, they must satisfy the "requirements" and always satisfies it
///     as long as it is in flight.
///   + Call lemma_X. If a correct "requirements" are provided, we can easily prove the equivalence of every_in_flight_req_msg_satisfies(requirements)
///     and the original statepred.
#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_no_delete_resource_request_msg_in_flight(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(always(lift_state(FBCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(FBCluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::external_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fb)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb))))
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fb))))),
{
    let key = fb.object_ref();
    let resource_key = get_request(sub_resource, fb).key;
    let requirements = |msg: FBMessage, s: FBCluster| !resource_delete_request_msg(resource_key)(msg);
    let resource_well_formed = |s: FBCluster| {
        &&& s.resources().contains_key(resource_key) ==> FBCluster::etcd_object_is_well_formed(resource_key)(s)
        &&& s.resources().contains_key(key) ==> FBCluster::etcd_object_is_well_formed(key)(s)
    };
    let stronger_next = |s: FBCluster, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& desired_state_is(fb)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb)(s)
        &&& resource_well_formed(s)
    };
    assert forall |s: FBCluster, s_prime: FBCluster| #[trigger] stronger_next(s, s_prime) implies FBCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: FBMessage| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.in_flight().contains(msg) {
                assert(requirements(msg, s));
                assert(requirements(msg, s_prime));
            } else {
                let step = choose |step| FBCluster::next_step(s, s_prime, step);
                match step {
                    Step::BuiltinControllersStep(_) => {
                        if s.resources().contains_key(resource_key) {
                            let owner_refs = s.resources()[resource_key].metadata.owner_references;
                            assert(owner_refs == Some(seq![fb.controller_owner_ref()]));
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
        spec, lift_action(stronger_next), lift_action(FBCluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(FBCluster::next()), lift_state(desired_state_is(fb)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb)),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed())
    );

    FBCluster::lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_delete_resource_request_msg_in_flight(sub_resource, fb)),
        lift_state(FBCluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr_forall(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fb)))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fb))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource|lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| (lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb))))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, fb)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(every_resource_create_request_implies_at_after_create_resource_step(res, fb)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource|lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(res, fb)), sub_resource);
        lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(spec, sub_resource, fb);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb)));
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(always(lift_state(FBCluster::busy_disabled()))),
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(fb)))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fb)))),
        spec.entails(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb)))),
        spec.entails(always(lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb))))),
{
    let key = get_request(sub_resource, fb).key;
    let eventual_owner_ref = |owner_ref: Option<Seq<OwnerReferenceView>>| {owner_ref == Some(seq![fb.controller_owner_ref()])};
    always_weaken_temp(spec, lift_state(object_in_every_resource_update_request_only_has_owner_references_pointing_to_current_cr(sub_resource, fb)), lift_state(FBCluster::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)));
    always_weaken_temp(spec, lift_state(every_resource_create_request_implies_at_after_create_resource_step(sub_resource, fb)), lift_state(FBCluster::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)));
    always_weaken_temp(spec, lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fb)), lift_state(FBCluster::object_has_no_finalizers(key)));

    let state = |s: FBCluster| {
        desired_state_is(fb)(s)
        && resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fb)(s)
    };
    invariant_n!(
        spec, lift_state(state), lift_state(FBCluster::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(FBCluster::garbage_collector_deletion_enabled(key))),
        lift_state(desired_state_is(fb)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, fb))
    );
    FBCluster::lemma_eventually_objects_owner_references_satisfies(spec, key, eventual_owner_ref);
    temp_pred_equality(
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, fb)),
        lift_state(FBCluster::objects_owner_references_satisfies(key, eventual_owner_ref))
    );
}

pub proof fn leads_to_always_tla_forall_subresource(spec: TempPred<FBCluster>, p: TempPred<FBCluster>, a_to_p: spec_fn(SubResource)->TempPred<FBCluster>)
    requires forall |a: SubResource| spec.entails(p.leads_to(always(#[trigger] a_to_p(a)))),
    ensures spec.entails(p.leads_to(always(tla_forall(a_to_p)))),
{
    leads_to_always_tla_forall(
        spec, p, a_to_p, set![SubResource::ServiceAccount, SubResource::Role, SubResource::RoleBinding, SubResource::Service, SubResource::DaemonSet]
    );
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_daemon_set_not_exists_or_matches_or_no_more_status_update(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(always(lift_action(FBCluster::next()))),
        spec.entails(tla_forall(|i| FBCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| FBCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(FBCluster::each_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(desired_state_is(fb)))),
        spec.entails(always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(SubResource::DaemonSet, fb)))),
        spec.entails(always(lift_state(every_resource_update_request_implies_at_after_update_resource_step(SubResource::DaemonSet, fb)))),
        spec.entails(always(lift_state(daemon_set_in_etcd_satisfies_unchangeable(fb)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::DaemonSet, fb)))),
        spec.entails(always(lift_state(no_update_status_request_msg_not_from_bc_in_flight_of_daemon_set(fb)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(daemon_set_not_exists_or_matches_or_no_more_status_update(fb))))),
{
    let ds_key = get_request(SubResource::DaemonSet, fb).key;
    let make_fn = || make_daemon_set(fb);
    implies_preserved_by_always_temp(
        lift_state(every_resource_create_request_implies_at_after_create_resource_step(SubResource::DaemonSet, fb)),
        lift_state(FBCluster::every_in_flight_create_req_msg_for_this_ds_matches(ds_key, make_fn))
    );
    valid_implies_trans(
        spec,
        always(lift_state(every_resource_create_request_implies_at_after_create_resource_step(SubResource::DaemonSet, fb))),
        always(lift_state(FBCluster::every_in_flight_create_req_msg_for_this_ds_matches(ds_key, make_fn)))
    );
    let inv_for_update = |s: FBCluster| {
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
        &&& desired_state_is(fb)(s)
        &&& every_resource_update_request_implies_at_after_update_resource_step(SubResource::DaemonSet, fb)(s)
        &&& daemon_set_in_etcd_satisfies_unchangeable(fb)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::DaemonSet, fb)(s)
    };
    DaemonSetView::marshal_spec_preserves_integrity();
    DaemonSetView::marshal_status_preserves_integrity();
    invariant_n!(
        spec, lift_state(inv_for_update), lift_state(FBCluster::every_in_flight_update_req_msg_for_this_ds_matches(ds_key, make_fn)),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed()),
        lift_state(desired_state_is(fb)),
        lift_state(every_resource_update_request_implies_at_after_update_resource_step(SubResource::DaemonSet, fb)),
        lift_state(daemon_set_in_etcd_satisfies_unchangeable(fb)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::DaemonSet, fb))
    );

    FBCluster::lemma_true_leads_to_always_daemon_set_not_exist_or_updated_or_no_more_pending_req(spec, ds_key, make_fn);

    let stronger_inv = |s: FBCluster| {
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
        &&& desired_state_is(fb)(s)
        &&& daemon_set_in_etcd_satisfies_unchangeable(fb)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::DaemonSet, fb)(s)
        &&& no_update_status_request_msg_not_from_bc_in_flight_of_daemon_set(fb)(s)
    };

    assert forall |s| #[trigger] stronger_inv(s) && FBCluster::daemon_set_not_exist_or_updated_or_no_more_status_from_bc(ds_key, make_fn)(s)
    implies daemon_set_not_exists_or_matches_or_no_more_status_update(fb)(s) by {
        if !s.resources().contains_key(ds_key) {}
        else if sub_resource_state_matches(SubResource::DaemonSet, fb)(s) {}
        else {
            assert forall |msg: FBMessage| s.in_flight().contains(msg) implies !(#[trigger] resource_update_status_request_msg(get_request(SubResource::DaemonSet, fb).key)(msg)) by {
                if update_status_msg_from_bc_for(get_request(SubResource::DaemonSet, fb).key)(msg) {} else {}
            }
        }
    }
    combine_spec_entails_always_n!(
        spec, lift_state(stronger_inv), lift_state(FBCluster::each_object_in_etcd_is_well_formed()), lift_state(desired_state_is(fb)),
        lift_state(daemon_set_in_etcd_satisfies_unchangeable(fb)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(SubResource::DaemonSet, fb)),
        lift_state(no_update_status_request_msg_not_from_bc_in_flight_of_daemon_set(fb))
    );

    leads_to_always_enhance(spec, lift_state(stronger_inv), true_pred(),
        lift_state(FBCluster::daemon_set_not_exist_or_updated_or_no_more_status_from_bc(ds_key, make_fn)),
        lift_state(daemon_set_not_exists_or_matches_or_no_more_status_update(fb))
    );
}

}
