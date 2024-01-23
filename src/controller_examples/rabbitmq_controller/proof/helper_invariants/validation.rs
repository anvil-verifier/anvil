// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants::{owner_ref::*, predicate::*, proof::*},
        predicate::*,
        resource::*,
    },
    trusted::{spec_types::*, step::*},
};
use crate::reconciler::spec::{reconciler::*, resource_builder::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

/// We need such a spec for stateful set because certain fields are determined by the spec of custom resource object and won't
/// be updated. So we need the transition validation of custom resource (rabbitmq) to show some fields of rabbitmq won't change
/// by the update request. Therefore, though updating stateful set won't update those fields, the stateful set will still match
/// the desired state.
///
/// We don't need this for other subresources because they don't have such fields: (1) those fields are determined by the rabbitmq
/// object (except the key of rabbitmq); and (2) these fields won't be updated during update.
pub open spec fn certain_fields_of_stateful_set_stay_unchanged(obj: DynamicObjectView, rabbitmq: RabbitmqClusterView) -> bool {
    let made_spec = make_stateful_set(rabbitmq, new_strlit("")@).spec.get_Some_0();
    let sts = StatefulSetView::unmarshal(obj).get_Ok_0();

    obj.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref()) ==> made_spec == StatefulSetSpecView {
        replicas: made_spec.replicas,
        template: made_spec.template,
        persistent_volume_claim_retention_policy: made_spec.persistent_volume_claim_retention_policy,
        ..sts.spec.get_Some_0()
    }
}

pub open spec fn stateful_set_in_etcd_satisfies_unchangeable(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    let key = rabbitmq.object_ref();
    let sts_key = StatefulSetBuilder::get_request(rabbitmq).key;
    |s: RMQCluster| {
        s.resources().contains_key(key)
        && s.resources().contains_key(sts_key)
        ==> certain_fields_of_stateful_set_stay_unchanged(s.resources()[sts_key], RabbitmqClusterView::unmarshal(s.resources()[key]).get_Ok_0())
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_stateful_set_in_etcd_satisfies_unchangeable(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures spec.entails(always(lift_state(stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)))),
{
    let inv = stateful_set_in_etcd_satisfies_unchangeable(rabbitmq);
    let sts_res = SubResource::StatefulSet;
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(rabbitmq);
    let resource_well_formed = |s: RMQCluster| {
        &&& s.resources().contains_key(sts_key) ==> RMQCluster::etcd_object_is_well_formed(sts_key)(s)
        &&& s.resources().contains_key(key) ==> RMQCluster::etcd_object_is_well_formed(key)(s)
    };
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& resource_well_formed(s)
        &&& resource_well_formed(s_prime)
        &&& every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sts_res, rabbitmq)(s)
        &&& stateful_set_in_create_request_msg_satisfies_unchangeable(rabbitmq)(s)
        &&& stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, rabbitmq)(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_weaken_temp(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()), lift_state(resource_well_formed));
    always_to_always_later(spec, lift_state(resource_well_formed));
    lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(spec, sts_res, rabbitmq);
    lemma_always_stateful_set_in_create_request_msg_satisfies_unchangeable(spec, rabbitmq);
    lemma_always_stateful_set_update_request_msg_does_not_change_owner_reference(spec, rabbitmq);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(spec, sts_res, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(resource_well_formed), later(lift_state(resource_well_formed)),
        lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sts_res, rabbitmq)),
        lift_state(stateful_set_in_create_request_msg_satisfies_unchangeable(rabbitmq)),
        lift_state(stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if s_prime.resources().contains_key(key) && s_prime.resources().contains_key(sts_key) {
            if s.resources().contains_key(sts_key) && s.resources()[sts_key] == s_prime.resources()[sts_key] {
                if !s.resources().contains_key(key) {
                    assert(s_prime.resources()[key].metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                    let owner_refs = s.resources()[sts_key].metadata.owner_references;
                    if owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1 {
                        assert(owner_refs.get_Some_0()[0].uid != s.kubernetes_api_state.uid_counter);
                        assert(owner_refs.get_Some_0()[0] != RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref());
                    }
                } else if s.resources()[key] != s_prime.resources()[key] {
                    assert(s.resources()[key].metadata.uid == s_prime.resources()[key].metadata.uid);
                    assert(RabbitmqClusterView::unmarshal(s.resources()[key]).get_Ok_0().controller_owner_ref() == RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref());
                    assert(RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()
                        .transition_validation(RabbitmqClusterView::unmarshal(s.resources()[key]).get_Ok_0()));
                }
                assert(certain_fields_of_stateful_set_stay_unchanged(s_prime.resources()[sts_key], RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
            } else {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                match step {
                    Step::ApiServerStep(input) => {
                        let req = input.get_Some_0();
                        if resource_create_request_msg(sts_key)(req) {} else {}
                        if resource_update_request_msg(sts_key)(req) {} else {}
                    },
                    _ => {}
                }
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

pub open spec fn stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    let key = rabbitmq.object_ref();
    let sts_key = StatefulSetBuilder::get_request(rabbitmq).key;
    |s: RMQCluster| {
        forall |msg: RMQMessage|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(sts_key)(msg)
            && s.resources().contains_key(sts_key)
            && s.resources()[sts_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
            ==> s.resources()[sts_key].metadata.owner_references == msg.content.get_update_request().obj.metadata.owner_references
    }
}

pub proof fn lemma_always_stateful_set_update_request_msg_does_not_change_owner_reference(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures spec.entails(always(lift_state(stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq)))),
{
    let key = rabbitmq.object_ref();
    let sts_key = StatefulSetBuilder::get_request(rabbitmq).key;
    let inv = stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& response_at_after_get_resource_step_is_resource_get_response(SubResource::StatefulSet, rabbitmq)(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, rabbitmq)(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, SubResource::StatefulSet, rabbitmq);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    RMQCluster::lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, sts_key);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(spec, SubResource::StatefulSet, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(SubResource::StatefulSet, rabbitmq)),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && resource_update_request_msg(sts_key)(msg)
        && s_prime.resources().contains_key(sts_key)
        && s_prime.resources()[sts_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
        implies s_prime.resources()[sts_key].metadata.owner_references == msg.content.get_update_request().obj.metadata.owner_references by {
            let step = choose |step| RMQCluster::next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                if s.resources().contains_key(sts_key) {
                    assert(s_prime.resources()[sts_key].metadata.owner_references == s.resources()[sts_key].metadata.owner_references);
                } else {
                    assert(msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s_prime.resources()[sts_key].metadata.resource_version.get_Some_0());
                }
            } else if resource_update_request_msg(sts_key)(msg) {
                lemma_resource_update_request_msg_implies_key_in_reconcile_equals(SubResource::StatefulSet, rabbitmq, s, s_prime, msg, step);
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

pub open spec fn object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let resource_key = get_request(sub_resource, rabbitmq).key;
        let etcd_rv = s.resources()[resource_key].metadata.resource_version.get_Some_0();
        forall |msg: RMQMessage|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
            ==> msg.content.get_update_request().obj.metadata.resource_version.is_Some()
                && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures spec.entails(always(lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, rabbitmq)))),
{
    let key = rabbitmq.object_ref();
    let sts_key = get_request(sub_resource, rabbitmq).key;
    let inv = object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, rabbitmq);
    let resource_well_formed = |s: RMQCluster| {
        s.resources().contains_key(sts_key) ==> RMQCluster::etcd_object_is_well_formed(sts_key)(s)
    };
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& resource_well_formed(s)
        &&& resource_well_formed(s_prime)
        &&& response_at_after_get_resource_step_is_resource_get_response(sub_resource, rabbitmq)(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, sub_resource, rabbitmq);
    always_weaken_temp(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()), lift_state(resource_well_formed));
    always_to_always_later(spec, lift_state(resource_well_formed));
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    RMQCluster::lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()),
        lift_state(resource_well_formed), later(lift_state(resource_well_formed)),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, rabbitmq)),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::object_in_ok_get_response_has_smaller_rv_than_etcd())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && resource_update_request_msg(sts_key)(msg) implies
        msg.content.get_update_request().obj.metadata.resource_version.is_Some()
        && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s_prime.kubernetes_api_state.resource_version_counter by {
            let step = choose |step| RMQCluster::next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                assert(s.kubernetes_api_state.resource_version_counter <= s_prime.kubernetes_api_state.resource_version_counter);
            } else if resource_update_request_msg(sts_key)(msg) {
                lemma_resource_update_request_msg_implies_key_in_reconcile_equals(sub_resource, rabbitmq, s, s_prime, msg, step);
                let resp = step.get_ControllerStep_0().0.get_Some_0();
                assert(RMQCluster::is_ok_get_response_msg()(resp));
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

pub open spec fn stateful_set_in_create_request_msg_satisfies_unchangeable(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    let key = rabbitmq.object_ref();
    |s: RMQCluster| {
        forall |msg: RMQMessage|
            s.in_flight().contains(msg)
            && s.resources().contains_key(key)
            && #[trigger] resource_create_request_msg(StatefulSetBuilder::get_request(rabbitmq).key)(msg)
            ==> certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, RabbitmqClusterView::unmarshal(s.resources()[key]).get_Ok_0())
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_always_stateful_set_in_create_request_msg_satisfies_unchangeable(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures spec.entails(always(lift_state(stateful_set_in_create_request_msg_satisfies_unchangeable(rabbitmq)))),
{
    let inv = stateful_set_in_create_request_msg_satisfies_unchangeable(rabbitmq);
    let sts_res = SubResource::StatefulSet;
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(rabbitmq)(s)
        &&& object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sts_res, rabbitmq)(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    RMQCluster::lemma_always_transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(spec, rabbitmq);
    lemma_always_object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(spec, sts_res, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(rabbitmq)),
        lift_state(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sts_res, rabbitmq))
    );
    assert forall |s: RMQCluster, s_prime: RMQCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = rabbitmq.object_ref();
        let sts_key = make_stateful_set_key(rabbitmq);
        assert forall |msg| s_prime.in_flight().contains(msg) && s_prime.resources().contains_key(key) && #[trigger] resource_create_request_msg(sts_key)(msg)
        implies certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()) by {
            let step = choose |step| RMQCluster::next_step(s, s_prime, step);
            match step {
                Step::ApiServerStep(input) => {
                    assert(s.controller_state == s_prime.controller_state);
                    assert(s.in_flight().contains(msg));
                    if s.resources().contains_key(key) {
                        assert(RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()
                        .transition_validation(RabbitmqClusterView::unmarshal(s.resources()[key]).get_Ok_0()));
                    } else {
                        assert(s_prime.resources()[key].metadata.uid.is_Some());
                        assert(s_prime.resources()[key].metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                        let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
                        assert(owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1);
                        assert(owner_refs.get_Some_0()[0].uid != s.kubernetes_api_state.uid_counter);
                        assert(owner_refs.get_Some_0()[0] != RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref());
                        assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
                    }
                },
                Step::ControllerStep(input) => {
                    if !s.in_flight().contains(msg) {
                        StatefulSetView::marshal_preserves_integrity();
                        StatefulSetView::marshal_spec_preserves_integrity();
                        lemma_resource_create_request_msg_implies_key_in_reconcile_equals(sts_res, rabbitmq, s, s_prime, msg, step);
                        let triggering_cr = s.ongoing_reconciles()[key].triggering_cr;
                        let etcd_cr = RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0();
                        assert(msg.content.get_create_request().obj.metadata.owner_references_only_contains(triggering_cr.controller_owner_ref()));
                        assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, triggering_cr));
                        if triggering_cr.metadata.uid.is_None() || triggering_cr.metadata.uid.get_Some_0() != etcd_cr.metadata.uid.get_Some_0() {
                            assert(!msg.content.get_create_request().obj.metadata.owner_references_only_contains(etcd_cr.controller_owner_ref()));
                        } else {
                            assert(etcd_cr.transition_validation(triggering_cr));
                        }
                        assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
                    }
                    assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, RabbitmqClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
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
    init_invariant(spec, RMQCluster::init(), next, inv);
}

}
