// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::fluent_controller::fluentbit::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants::{owner_ref::*, predicate::*, proof::*},
        predicate::*,
        resource::*,
    },
    trusted::{spec_types::*, step::*},
};
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, daemon_set::*, dynamic::*, owner_reference::*,
    resource::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::{reconciler::*, resource_builder::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

/// We need such a spec for daemon set because certain fields are determined by the spec of custom resource object and won't
/// be updated. So we need the transition validation of custom resource (fb) to show some fields of fb won't change
/// by the update request. Therefore, though updating daemon set won't update those fields, the daemon set will still match
/// the desired state.
///
/// We don't need this for other subresources because they don't have such fields: (1) those fields are determined by the fb
/// object (except the key of fb); and (2) these fields won't be updated during update.
pub open spec fn certain_fields_of_daemon_set_stay_unchanged(obj: DynamicObjectView, fb: FluentBitView) -> bool {
    let made_spec = make_daemon_set(fb).spec.get_Some_0();
    let ds = DaemonSetView::unmarshal(obj).get_Ok_0();

    obj.metadata.owner_references_only_contains(fb.controller_owner_ref()) ==> made_spec == DaemonSetSpecView {
        template: made_spec.template,
        ..ds.spec.get_Some_0()
    }
}

pub open spec fn daemon_set_in_etcd_satisfies_unchangeable(fb: FluentBitView) -> StatePred<FBCluster> {
    let key = fb.object_ref();
    let ds_key = DaemonSetBuilder::get_request(fb).key;
    |s: FBCluster| {
        s.resources().contains_key(key)
        && s.resources().contains_key(ds_key)
        ==> certain_fields_of_daemon_set_stay_unchanged(s.resources()[ds_key], FluentBitView::unmarshal(s.resources()[key]).get_Ok_0())
    }
}

pub proof fn lemma_always_daemon_set_in_etcd_satisfies_unchangeable(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(daemon_set_in_etcd_satisfies_unchangeable(fb)))),
{
    hide(make_fluentbit_pod_spec);
    let inv = daemon_set_in_etcd_satisfies_unchangeable(fb);
    let ds_res = SubResource::DaemonSet;
    let next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(ds_res, fb)(s)
        &&& daemon_set_in_create_request_msg_satisfies_unchangeable(fb)(s)
        &&& daemon_set_update_request_msg_does_not_change_owner_reference(fb)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::DaemonSet, fb)(s)
    };
    FBCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(FBCluster::each_object_in_etcd_is_well_formed()));
    lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(spec, ds_res, fb);
    lemma_always_daemon_set_in_create_request_msg_satisfies_unchangeable(spec, fb);
    lemma_always_daemon_set_update_request_msg_does_not_change_owner_reference(spec, fb);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(spec, ds_res, fb);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(FBCluster::next()), lift_state(FBCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(FBCluster::each_object_in_etcd_is_well_formed())),
        lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(ds_res, fb)),
        lift_state(daemon_set_in_create_request_msg_satisfies_unchangeable(fb)),
        lift_state(daemon_set_update_request_msg_does_not_change_owner_reference(fb)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::DaemonSet, fb))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = fb.object_ref();
        let ds_key = make_daemon_set_key(fb);
        if s_prime.resources().contains_key(key) && s_prime.resources().contains_key(ds_key) {
            if s.resources().contains_key(ds_key) && s.resources()[ds_key] == s_prime.resources()[ds_key] {
                if !s.resources().contains_key(key) {
                    assert(s_prime.resources()[key].metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                    let owner_refs = s.resources()[ds_key].metadata.owner_references;
                    if owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1 {
                        assert(owner_refs.get_Some_0()[0].uid != s.kubernetes_api_state.uid_counter);
                        assert(owner_refs.get_Some_0()[0] != FluentBitView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref());
                    }
                } else if s.resources()[key] != s_prime.resources()[key] {
                    assert(s.resources()[key].metadata.uid == s_prime.resources()[key].metadata.uid);
                    assert(FluentBitView::unmarshal(s.resources()[key]).get_Ok_0().controller_owner_ref() == FluentBitView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref());
                    assert(FluentBitView::unmarshal(s_prime.resources()[key]).get_Ok_0()
                        .transition_validation(FluentBitView::unmarshal(s.resources()[key]).get_Ok_0()));
                }
                assert(certain_fields_of_daemon_set_stay_unchanged(s_prime.resources()[ds_key], FluentBitView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
            } else {
                let step = choose |step| FBCluster::next_step(s, s_prime, step);
                match step {
                    Step::ApiServerStep(input) => {
                        let req = input.get_Some_0();
                        if resource_create_request_msg(ds_key)(req) {} else {}
                        if resource_update_request_msg(ds_key)(req) {} else {}
                    },
                    _ => {}
                }
            }
        }
    }
    init_invariant(spec, FBCluster::init(), next, inv);
}

pub open spec fn daemon_set_update_request_msg_does_not_change_owner_reference(fb: FluentBitView) -> StatePred<FBCluster> {
    let key = fb.object_ref();
    let ds_key = DaemonSetBuilder::get_request(fb).key;
    |s: FBCluster| {
        forall |msg: FBMessage|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(DaemonSetBuilder::get_request(fb).key)(msg)
            && s.resources().contains_key(ds_key)
            && s.resources()[ds_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
            ==> s.resources()[ds_key].metadata.owner_references == msg.content.get_update_request().obj.metadata.owner_references
    }
}

pub proof fn lemma_always_daemon_set_update_request_msg_does_not_change_owner_reference(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(daemon_set_update_request_msg_does_not_change_owner_reference(fb)))),
{
    let key = fb.object_ref();
    let ds_key = DaemonSetBuilder::get_request(fb).key;
    let inv = daemon_set_update_request_msg_does_not_change_owner_reference(fb);
    let next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& response_at_after_get_resource_step_is_resource_get_response(SubResource::DaemonSet, fb)(s)
        &&& FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(ds_key)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::DaemonSet, fb)(s)
    };
    FBCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, SubResource::DaemonSet, fb);
    always_to_always_later(spec, lift_state(FBCluster::each_object_in_etcd_is_well_formed()));
    FBCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    FBCluster::lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, ds_key);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(spec, SubResource::DaemonSet, fb);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(FBCluster::next()),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(FBCluster::each_object_in_etcd_is_well_formed())),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(SubResource::DaemonSet, fb)),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(ds_key)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::DaemonSet, fb))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| s_prime.in_flight().contains(msg) && #[trigger] resource_update_request_msg(ds_key)(msg)
        && s_prime.resources().contains_key(ds_key)
        && s_prime.resources()[ds_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
        implies s_prime.resources()[ds_key].metadata.owner_references == msg.content.get_update_request().obj.metadata.owner_references by {
            let step = choose |step| FBCluster::next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                if s.resources().contains_key(ds_key) {
                    assert(s_prime.resources()[ds_key].metadata.owner_references == s.resources()[ds_key].metadata.owner_references);
                } else {
                    assert(msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s_prime.resources()[ds_key].metadata.resource_version.get_Some_0());
                }
            } else if resource_update_request_msg(ds_key)(msg) {
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(SubResource::DaemonSet, fb, s, s_prime, msg, step);
            }
        }
    }
    init_invariant(spec, FBCluster::init(), next, inv);
}

pub open spec fn object_in_resource_update_request_msg_has_smaller_rv_than_etcd(
    sub_resource: SubResource, fb: FluentBitView
) -> StatePred<FBCluster> {
    |s: FBCluster| {
        let resource_key = get_request(sub_resource, fb).key;
        let etcd_rv = s.resources()[resource_key].metadata.resource_version.get_Some_0();
        forall |msg: FBMessage|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(get_request(sub_resource, fb).key)(msg)
            ==> msg.content.get_update_request().obj.metadata.resource_version.is_Some()
                && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
    }
}

pub proof fn lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, fb)))),
{
    hide(make_daemon_set);
    let key = fb.object_ref();
    let ds_key = get_request(sub_resource, fb).key;
    let inv = object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, fb);
    let next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& response_at_after_get_resource_step_is_resource_get_response(sub_resource, fb)(s)
        &&& FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
    };
    FBCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, sub_resource, fb);
    always_to_always_later(spec, lift_state(FBCluster::each_object_in_etcd_is_well_formed()));
    FBCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    FBCluster::lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(FBCluster::next()),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(FBCluster::each_object_in_etcd_is_well_formed())),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, fb)),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCluster::object_in_ok_get_response_has_smaller_rv_than_etcd())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| s_prime.in_flight().contains(msg) && #[trigger] resource_update_request_msg(ds_key)(msg) implies
        msg.content.get_update_request().obj.metadata.resource_version.is_Some()
        && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s_prime.kubernetes_api_state.resource_version_counter by {
            let step = choose |step| FBCluster::next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                assert(s.kubernetes_api_state.resource_version_counter <= s_prime.kubernetes_api_state.resource_version_counter);
            } else if resource_update_request_msg(ds_key)(msg) {
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fb, s, s_prime, msg, step);
                let resp = step.get_ControllerStep_0().0.get_Some_0();
                assert(FBCluster::is_ok_get_response_msg()(resp));
            }
        }
    }
    init_invariant(spec, FBCluster::init(), next, inv);
}

pub open spec fn daemon_set_in_create_request_msg_satisfies_unchangeable(fb: FluentBitView) -> StatePred<FBCluster> {
    let key = fb.object_ref();
    |s: FBCluster| {
        forall |msg: FBMessage|
            s.in_flight().contains(msg)
            && s.resources().contains_key(key)
            && #[trigger] resource_create_request_msg(DaemonSetBuilder::get_request(fb).key)(msg)
            ==> certain_fields_of_daemon_set_stay_unchanged(msg.content.get_create_request().obj, FluentBitView::unmarshal(s.resources()[key]).get_Ok_0())
    }
}

proof fn lemma_always_daemon_set_in_create_request_msg_satisfies_unchangeable(spec: TempPred<FBCluster>, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(daemon_set_in_create_request_msg_satisfies_unchangeable(fb)))),
{
    hide(make_fluentbit_pod_spec);
    let inv = daemon_set_in_create_request_msg_satisfies_unchangeable(fb);
    let ds_res = SubResource::DaemonSet;
    let next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(fb)(s)
        &&& object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(ds_res, fb)(s)
    };
    FBCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(FBCluster::each_object_in_etcd_is_well_formed()));
    FBCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    FBCluster::lemma_always_transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(spec, fb);
    lemma_always_object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(spec, ds_res, fb);
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(FBCluster::next()),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(FBCluster::each_object_in_etcd_is_well_formed())),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(fb)),
        lift_state(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(ds_res, fb))
    );
    assert forall |s: FBCluster, s_prime: FBCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = fb.object_ref();
        let ds_key = make_daemon_set_key(fb);
        assert forall |msg| s_prime.in_flight().contains(msg) && s_prime.resources().contains_key(key) && #[trigger] resource_create_request_msg(ds_key)(msg)
        implies certain_fields_of_daemon_set_stay_unchanged(msg.content.get_create_request().obj, FluentBitView::unmarshal(s_prime.resources()[key]).get_Ok_0()) by {
            let step = choose |step| FBCluster::next_step(s, s_prime, step);
            match step {
                Step::ApiServerStep(input) => {
                    assert(s.controller_state == s_prime.controller_state);
                    assert(s.in_flight().contains(msg));
                    if s.resources().contains_key(key) {
                        assert(FluentBitView::unmarshal(s_prime.resources()[key]).get_Ok_0()
                        .transition_validation(FluentBitView::unmarshal(s.resources()[key]).get_Ok_0()));
                    } else {
                        assert(s_prime.resources()[key].metadata.uid.is_Some());
                        assert(s_prime.resources()[key].metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                        let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
                        assert(owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1);
                        assert(owner_refs.get_Some_0()[0].uid != s.kubernetes_api_state.uid_counter);
                        assert(owner_refs.get_Some_0()[0] != FluentBitView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref());
                        assert(certain_fields_of_daemon_set_stay_unchanged(msg.content.get_create_request().obj, FluentBitView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
                    }
                },
                Step::ControllerStep(input) => {
                    if !s.in_flight().contains(msg) {
                        DaemonSetView::marshal_preserves_integrity();
                        DaemonSetView::marshal_spec_preserves_integrity();
                        lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(ds_res, fb, s, s_prime, msg, step);
                        let triggering_cr = s.ongoing_reconciles()[key].triggering_cr;
                        let etcd_cr = FluentBitView::unmarshal(s_prime.resources()[key]).get_Ok_0();
                        assert(msg.content.get_create_request().obj.metadata.owner_references_only_contains(triggering_cr.controller_owner_ref()));
                        assert(certain_fields_of_daemon_set_stay_unchanged(msg.content.get_create_request().obj, triggering_cr));
                        if triggering_cr.metadata.uid.is_None() || triggering_cr.metadata.uid.get_Some_0() != etcd_cr.metadata.uid.get_Some_0() {
                            assert(!msg.content.get_create_request().obj.metadata.owner_references_only_contains(etcd_cr.controller_owner_ref()));
                        } else {
                            assert(etcd_cr.transition_validation(triggering_cr));
                        }
                        assert(certain_fields_of_daemon_set_stay_unchanged(msg.content.get_create_request().obj, FluentBitView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
                    }
                    assert(certain_fields_of_daemon_set_stay_unchanged(msg.content.get_create_request().obj, FluentBitView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
                },
                Step::BuiltinControllersStep(_) => {
                    assert(s.in_flight().contains(msg));
                    assert(s.resources().contains_key(key) == s_prime.resources().contains_key(key));
                    if s.resources().contains_key(key) {
                        s.resources()[key] == s_prime.resources()[key];
                    }
                }
                _ => {
                    assert(s.in_flight().contains(msg));
                    assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
                },
            }
        }
    }
    init_invariant(spec, FBCluster::init(), next, inv);
}

}
