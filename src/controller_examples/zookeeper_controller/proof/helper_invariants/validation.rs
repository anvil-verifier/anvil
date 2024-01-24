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
use crate::reconciler::spec::{reconciler::*, resource_builder::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use crate::zookeeper_controller::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants::{owner_ref::*, predicate::*, proof::*},
        predicate::*,
        resource::*,
    },
    trusted::{spec_types::*, step::*},
};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

/// We need such a spec for stateful set because certain fields are determined by the spec of custom resource object and won't
/// be updated. So we need the transition validation of custom resource (zookeeper) to show some fields of zookeeper won't change
/// by the update request. Therefore, though updating stateful set won't update those fields, the stateful set will still match
/// the desired state.
///
/// We don't need this for other subresources because they don't have such fields: (1) those fields are determined by the zookeeper
/// object (except the key of zookeeper); and (2) these fields won't be updated during update.
pub open spec fn certain_fields_of_stateful_set_stay_unchanged(obj: DynamicObjectView, zookeeper: ZookeeperClusterView) -> bool {
    let made_spec = make_stateful_set(zookeeper, new_strlit("")@).spec.get_Some_0();
    let sts = StatefulSetView::unmarshal(obj).get_Ok_0();

    obj.metadata.owner_references_only_contains(zookeeper.controller_owner_ref()) ==> made_spec == StatefulSetSpecView {
        replicas: made_spec.replicas,
        template: made_spec.template,
        persistent_volume_claim_retention_policy: made_spec.persistent_volume_claim_retention_policy,
        ..sts.spec.get_Some_0()
    }
}

pub open spec fn stateful_set_in_etcd_satisfies_unchangeable(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    let key = zookeeper.object_ref();
    let sts_key = StatefulSetBuilder::get_request(zookeeper).key;
    |s: ZKCluster| {
        s.resources().contains_key(key)
        && s.resources().contains_key(sts_key)
        ==> certain_fields_of_stateful_set_stay_unchanged(s.resources()[sts_key], ZookeeperClusterView::unmarshal(s.resources()[key]).get_Ok_0())
    }
}

pub proof fn lemma_always_stateful_set_in_etcd_satisfies_unchangeable(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(stateful_set_in_etcd_satisfies_unchangeable(zookeeper)))),
{
    let inv = stateful_set_in_etcd_satisfies_unchangeable(zookeeper);
    let sts_res = SubResource::StatefulSet;
    let next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sts_res, zookeeper)(s)
        &&& stateful_set_in_create_request_msg_satisfies_unchangeable(zookeeper)(s)
        &&& stateful_set_update_request_msg_does_not_change_owner_reference(zookeeper)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, zookeeper)(s)
    };
    ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(ZKCluster::each_object_in_etcd_is_well_formed()));
    lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(spec, sts_res, zookeeper);
    lemma_always_stateful_set_in_create_request_msg_satisfies_unchangeable(spec, zookeeper);
    lemma_always_stateful_set_update_request_msg_does_not_change_owner_reference(spec, zookeeper);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(spec, sts_res, zookeeper);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()), lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())),
        lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sts_res, zookeeper)),
        lift_state(stateful_set_in_create_request_msg_satisfies_unchangeable(zookeeper)),
        lift_state(stateful_set_update_request_msg_does_not_change_owner_reference(zookeeper)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, zookeeper))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = zookeeper.object_ref();
        let sts_key = make_stateful_set_key(zookeeper);
        if s_prime.resources().contains_key(key) && s_prime.resources().contains_key(sts_key) {
            if s.resources().contains_key(sts_key) && s.resources()[sts_key] == s_prime.resources()[sts_key] {
                if !s.resources().contains_key(key) {
                    assert(s_prime.resources()[key].metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                    let owner_refs = s.resources()[sts_key].metadata.owner_references;
                    if owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1 {
                        assert(owner_refs.get_Some_0()[0].uid != s.kubernetes_api_state.uid_counter);
                        assert(owner_refs.get_Some_0()[0] != ZookeeperClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref());
                    }
                } else if s.resources()[key] != s_prime.resources()[key] {
                    assert(s.resources()[key].metadata.uid == s_prime.resources()[key].metadata.uid);
                    assert(ZookeeperClusterView::unmarshal(s.resources()[key]).get_Ok_0().controller_owner_ref() == ZookeeperClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref());
                    assert(ZookeeperClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()
                        .transition_validation(ZookeeperClusterView::unmarshal(s.resources()[key]).get_Ok_0()));
                }
                assert(certain_fields_of_stateful_set_stay_unchanged(s_prime.resources()[sts_key], ZookeeperClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
            } else {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
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
    init_invariant(spec, ZKCluster::init(), next, inv);
}

pub open spec fn stateful_set_update_request_msg_does_not_change_owner_reference(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    let key = zookeeper.object_ref();
    let sts_key = StatefulSetBuilder::get_request(zookeeper).key;
    |s: ZKCluster| {
        forall |msg: ZKMessage|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(sts_key)(msg)
            && s.resources().contains_key(sts_key)
            && s.resources()[sts_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
            ==> s.resources()[sts_key].metadata.owner_references == msg.content.get_update_request().obj.metadata.owner_references
    }
}

pub proof fn lemma_always_stateful_set_update_request_msg_does_not_change_owner_reference(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(stateful_set_update_request_msg_does_not_change_owner_reference(zookeeper)))),
{
    let key = zookeeper.object_ref();
    let sts_key = StatefulSetBuilder::get_request(zookeeper).key;
    let inv = stateful_set_update_request_msg_does_not_change_owner_reference(zookeeper);
    let next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& response_at_after_get_resource_step_is_resource_get_response(SubResource::StatefulSet, zookeeper)(s)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, zookeeper)(s)
    };
    ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, SubResource::StatefulSet, zookeeper);
    always_to_always_later(spec, lift_state(ZKCluster::each_object_in_etcd_is_well_formed()));
    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    ZKCluster::lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, sts_key);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(spec, SubResource::StatefulSet, zookeeper);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(SubResource::StatefulSet, zookeeper)),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, zookeeper))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| s_prime.in_flight().contains(msg) && #[trigger] resource_update_request_msg(sts_key)(msg)
        && s_prime.resources().contains_key(sts_key)
        && s_prime.resources()[sts_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
        implies s_prime.resources()[sts_key].metadata.owner_references == msg.content.get_update_request().obj.metadata.owner_references by {
            let step = choose |step| ZKCluster::next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                if s.resources().contains_key(sts_key) {
                    assert(s_prime.resources()[sts_key].metadata.owner_references == s.resources()[sts_key].metadata.owner_references);
                } else {
                    assert(msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s_prime.resources()[sts_key].metadata.resource_version.get_Some_0());
                }
            } else if resource_update_request_msg(sts_key)(msg) {
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(SubResource::StatefulSet, zookeeper, s, s_prime, msg, step);
            }
        }
    }
    init_invariant(spec, ZKCluster::init(), next, inv);
}

pub open spec fn object_in_resource_update_request_msg_has_smaller_rv_than_etcd(
    sub_resource: SubResource, zookeeper: ZookeeperClusterView
) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        let resource_key = get_request(sub_resource, zookeeper).key;
        let etcd_rv = s.resources()[resource_key].metadata.resource_version.get_Some_0();
        forall |msg: ZKMessage|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(get_request(sub_resource, zookeeper).key)(msg)
            ==> msg.content.get_update_request().obj.metadata.resource_version.is_Some()
                && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
    }
}

pub proof fn lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(
    spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView
)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, zookeeper)))),
{
    let key = zookeeper.object_ref();
    let sts_key = get_request(sub_resource, zookeeper).key;
    let inv = object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, zookeeper);
    let next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)(s)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
    };
    ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, sub_resource, zookeeper);
    always_to_always_later(spec, lift_state(ZKCluster::each_object_in_etcd_is_well_formed()));
    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    ZKCluster::lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::object_in_ok_get_response_has_smaller_rv_than_etcd())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| s_prime.in_flight().contains(msg) && #[trigger] resource_update_request_msg(sts_key)(msg) implies
        msg.content.get_update_request().obj.metadata.resource_version.is_Some()
        && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s_prime.kubernetes_api_state.resource_version_counter by {
            let step = choose |step| ZKCluster::next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                assert(s.kubernetes_api_state.resource_version_counter <= s_prime.kubernetes_api_state.resource_version_counter);
            } else if resource_update_request_msg(sts_key)(msg) {
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, zookeeper, s, s_prime, msg, step);
                let resp = step.get_ControllerStep_0().0.get_Some_0();
                assert(ZKCluster::is_ok_get_response_msg()(resp));
            }
        }
    }
    init_invariant(spec, ZKCluster::init(), next, inv);
}

pub open spec fn stateful_set_in_create_request_msg_satisfies_unchangeable(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    let key = zookeeper.object_ref();
    let sts_key = StatefulSetBuilder::get_request(zookeeper).key;
    |s: ZKCluster| {
        forall |msg: ZKMessage|
            s.in_flight().contains(msg)
            && s.resources().contains_key(key)
            && #[trigger] resource_create_request_msg(sts_key)(msg)
            ==> certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, ZookeeperClusterView::unmarshal(s.resources()[key]).get_Ok_0())
    }
}

proof fn lemma_always_stateful_set_in_create_request_msg_satisfies_unchangeable(spec: TempPred<ZKCluster>, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(stateful_set_in_create_request_msg_satisfies_unchangeable(zookeeper)))),
{
    let inv = stateful_set_in_create_request_msg_satisfies_unchangeable(zookeeper);
    let sts_res = SubResource::StatefulSet;
    let next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(zookeeper)(s)
        &&& object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sts_res, zookeeper)(s)
    };
    ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(ZKCluster::each_object_in_etcd_is_well_formed()));
    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    ZKCluster::lemma_always_transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(spec, zookeeper);
    lemma_always_object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(spec, sts_res, zookeeper);
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(zookeeper)),
        lift_state(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sts_res, zookeeper))
    );
    assert forall |s: ZKCluster, s_prime: ZKCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = zookeeper.object_ref();
        let sts_key = make_stateful_set_key(zookeeper);
        assert forall |msg| s_prime.in_flight().contains(msg) && s_prime.resources().contains_key(key) && #[trigger] resource_create_request_msg(sts_key)(msg)
        implies certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, ZookeeperClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()) by {
            let step = choose |step| ZKCluster::next_step(s, s_prime, step);
            match step {
                Step::ApiServerStep(input) => {
                    assert(s.controller_state == s_prime.controller_state);
                    assert(s.in_flight().contains(msg));
                    if s.resources().contains_key(key) {
                        assert(ZookeeperClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()
                        .transition_validation(ZookeeperClusterView::unmarshal(s.resources()[key]).get_Ok_0()));
                    } else {
                        assert(s_prime.resources()[key].metadata.uid.is_Some());
                        assert(s_prime.resources()[key].metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                        let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
                        assert(owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1);
                        assert(owner_refs.get_Some_0()[0].uid != s.kubernetes_api_state.uid_counter);
                        assert(owner_refs.get_Some_0()[0] != ZookeeperClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0().controller_owner_ref());
                        assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, ZookeeperClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
                    }
                },
                Step::ControllerStep(input) => {
                    if !s.in_flight().contains(msg) {
                        StatefulSetView::marshal_preserves_integrity();
                        StatefulSetView::marshal_spec_preserves_integrity();
                        lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sts_res, zookeeper, s, s_prime, msg, step);
                        let triggering_cr = s.ongoing_reconciles()[key].triggering_cr;
                        let etcd_cr = ZookeeperClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0();
                        assert(msg.content.get_create_request().obj.metadata.owner_references_only_contains(triggering_cr.controller_owner_ref()));
                        assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, triggering_cr));
                        if triggering_cr.metadata.uid.is_None() || triggering_cr.metadata.uid.get_Some_0() != etcd_cr.metadata.uid.get_Some_0() {
                            assert(!msg.content.get_create_request().obj.metadata.owner_references_only_contains(etcd_cr.controller_owner_ref()));
                        } else {
                            assert(etcd_cr.transition_validation(triggering_cr));
                        }
                        assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, ZookeeperClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
                    }
                    assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, ZookeeperClusterView::unmarshal(s_prime.resources()[key]).get_Ok_0()));
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
    init_invariant(spec, ZKCluster::init(), next, inv);
}

}
