// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::vstatefulset_controller::trusted::spec_types::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
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

// We need such a spec for stateful set because certain fields are determined by the spec of custom resource object and won't
// be updated. So we need the transition validation of custom resource (rabbitmq) to show some fields of rabbitmq won't change
// by the update request. Therefore, though updating stateful set won't update those fields, the stateful set will still match
// the desired state.
//
// We don't need this for other subresources because they don't have such fields: (1) those fields are determined by the rabbitmq
// object (except the key of rabbitmq); and (2) these fields won't be updated during update.
pub open spec fn certain_fields_of_stateful_set_stay_unchanged(obj: DynamicObjectView, rabbitmq: RabbitmqClusterView) -> bool {
    let made_spec = make_stateful_set(rabbitmq, ""@).spec;
    let sts = VStatefulSetView::unmarshal(obj)->Ok_0;

    obj.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref()) ==> made_spec == VStatefulSetSpecView {
        replicas: made_spec.replicas,
        template: made_spec.template,
        persistent_volume_claim_retention_policy: made_spec.persistent_volume_claim_retention_policy,
        ..sts.spec
    }
}

pub open spec fn stateful_set_in_etcd_satisfies_unchangeable(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    let key = rabbitmq.object_ref();
    let sts_key = StatefulSetBuilder::get_request(rabbitmq).key;
    |s: ClusterState| {
        s.resources().contains_key(key)
        && s.resources().contains_key(sts_key)
        ==> certain_fields_of_stateful_set_stay_unchanged(s.resources()[sts_key], RabbitmqClusterView::unmarshal(s.resources()[key])->Ok_0)
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_stateful_set_in_etcd_satisfies_unchangeable(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
    ensures spec.entails(always(lift_state(stateful_set_in_etcd_satisfies_unchangeable(rabbitmq)))),
{
    let inv = stateful_set_in_etcd_satisfies_unchangeable(rabbitmq);
    let sts_res = SubResource::StatefulSet;
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sts_res, rabbitmq)(s)
        &&& stateful_set_in_create_request_msg_satisfies_unchangeable(rabbitmq)(s)
        &&& stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, rabbitmq)(s)
        &&& no_create_resource_request_msg_without_name_in_flight(SubResource::StatefulSet, rabbitmq)(s)
    };
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(controller_id, cluster, spec, sts_res, rabbitmq);
    lemma_always_stateful_set_in_create_request_msg_satisfies_unchangeable(controller_id, cluster, spec, rabbitmq);
    lemma_always_stateful_set_update_request_msg_does_not_change_owner_reference(controller_id, cluster, spec, rabbitmq);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(controller_id, cluster, spec, sts_res, rabbitmq);
    lemma_always_no_create_resource_request_msg_without_name_in_flight(cluster, spec, sts_res, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()), lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sts_res, rabbitmq)),
        lift_state(stateful_set_in_create_request_msg_satisfies_unchangeable(rabbitmq)),
        lift_state(stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, rabbitmq)),
        lift_state(no_create_resource_request_msg_without_name_in_flight(SubResource::StatefulSet, rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = rabbitmq.object_ref();
        let sts_key = make_stateful_set_key(rabbitmq);
        if s_prime.resources().contains_key(key) && s_prime.resources().contains_key(sts_key) {
            if s.resources().contains_key(sts_key) && s.resources()[sts_key] == s_prime.resources()[sts_key] {
                if !s.resources().contains_key(key) {
                    assert(s_prime.resources()[key].metadata.uid->0 == s.api_server.uid_counter);
                    let owner_refs = s.resources()[sts_key].metadata.owner_references;
                    if owner_refs is Some && owner_refs->0.len() == 1 {
                        assert(owner_refs->0[0].uid != s.api_server.uid_counter);
                        assert(owner_refs->0[0] != RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0.controller_owner_ref());
                    }
                } else if s.resources()[key] != s_prime.resources()[key] {
                    assert(s.resources()[key].metadata.uid == s_prime.resources()[key].metadata.uid);
                    assert(RabbitmqClusterView::unmarshal(s.resources()[key])->Ok_0.controller_owner_ref() == RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0.controller_owner_ref());
                    assert(RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0
                        .transition_validation(RabbitmqClusterView::unmarshal(s.resources()[key])->Ok_0));
                }
                assert(certain_fields_of_stateful_set_stay_unchanged(s_prime.resources()[sts_key], RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0));
            } else {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        let req = input->0;
                        if resource_create_request_msg(sts_key)(req) {} else {}
                        if resource_update_request_msg(sts_key)(req) {} else {}
                        if resource_create_request_msg_without_name(sts_key.kind, sts_key.namespace)(req) {} else {}
                    },
                    _ => {}
                }
                assert(inv(s_prime));
            }
        }
    }
    init_invariant(spec, cluster.init(), next, inv);
}

pub open spec fn stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    let key = rabbitmq.object_ref();
    let sts_key = StatefulSetBuilder::get_request(rabbitmq).key;
    |s: ClusterState| {
        forall |msg: Message|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(sts_key)(msg)
            && s.resources().contains_key(sts_key)
            && s.resources()[sts_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
            ==> s.resources()[sts_key].metadata.owner_references == msg.content.get_update_request().obj.metadata.owner_references
    }
}

#[verifier(external_body)]
pub proof fn lemma_always_stateful_set_update_request_msg_does_not_change_owner_reference(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
    ensures spec.entails(always(lift_state(stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq)))),
{
    let key = rabbitmq.object_ref();
    let sts_key = StatefulSetBuilder::get_request(rabbitmq).key;
    let inv = stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq);
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& response_at_after_get_resource_step_is_resource_get_response(controller_id, SubResource::StatefulSet, rabbitmq)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, rabbitmq)(s)
    };
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(controller_id, cluster, spec, SubResource::StatefulSet, rabbitmq);
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, sts_key);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(controller_id, cluster, spec, SubResource::StatefulSet, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, SubResource::StatefulSet, rabbitmq)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::StatefulSet, rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && resource_update_request_msg(sts_key)(msg)
        && s_prime.resources().contains_key(sts_key)
        && s_prime.resources()[sts_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
        implies s_prime.resources()[sts_key].metadata.owner_references == msg.content.get_update_request().obj.metadata.owner_references by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                if s.resources().contains_key(sts_key) {
                    assert(s_prime.resources()[sts_key].metadata.owner_references == s.resources()[sts_key].metadata.owner_references);
                } else {
                    assert(msg.content.get_update_request().obj.metadata.resource_version->0 < s_prime.resources()[sts_key].metadata.resource_version->0);
                }
            } else if resource_update_request_msg(sts_key)(msg) {
                lemma_resource_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, SubResource::StatefulSet, rabbitmq, s, s_prime, msg, step);
            }
        }
    }
    init_invariant(spec, cluster.init(), next, inv);
}

pub open spec fn object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let resource_key = get_request(sub_resource, rabbitmq).key;
        let etcd_rv = s.resources()[resource_key].metadata.resource_version->0;
        forall |msg: Message|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
            ==> msg.content.get_update_request().obj.metadata.resource_version is Some
                && msg.content.get_update_request().obj.metadata.resource_version->0 < s.api_server.resource_version_counter
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
    ensures spec.entails(always(lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, rabbitmq)))),
{
    let key = rabbitmq.object_ref();
    let sts_key = get_request(sub_resource, rabbitmq).key;
    let inv = object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, rabbitmq);
    let resource_well_formed = |s: ClusterState| {
        s.resources().contains_key(sts_key) ==> cluster.etcd_object_is_well_formed(sts_key)(s)
    };
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& resource_well_formed(s)
        &&& resource_well_formed(s_prime)
        &&& response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
    };
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(controller_id, cluster, spec, sub_resource, rabbitmq);
    always_weaken(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()), lift_state(resource_well_formed));
    always_to_always_later(spec, lift_state(resource_well_formed));
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        lift_state(resource_well_formed), later(lift_state(resource_well_formed)),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && resource_update_request_msg(sts_key)(msg) implies
        msg.content.get_update_request().obj.metadata.resource_version is Some
        && msg.content.get_update_request().obj.metadata.resource_version->0 < s_prime.api_server.resource_version_counter by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                assert(s.api_server.resource_version_counter <= s_prime.api_server.resource_version_counter);
            } else if resource_update_request_msg(sts_key)(msg) {
                lemma_resource_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                let resp = step->ControllerStep_0.1->0;
                assert(is_ok_get_response_msg()(resp));
            }
        }
    }
    init_invariant(spec, cluster.init(), next, inv);
}

pub open spec fn stateful_set_in_create_request_msg_satisfies_unchangeable(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    let key = rabbitmq.object_ref();
    |s: ClusterState| {
        forall |msg: Message|
            s.in_flight().contains(msg)
            && s.resources().contains_key(key)
            && #[trigger] resource_create_request_msg(StatefulSetBuilder::get_request(rabbitmq).key)(msg)
            ==> certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, RabbitmqClusterView::unmarshal(s.resources()[key])->Ok_0)
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_always_stateful_set_in_create_request_msg_satisfies_unchangeable(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
    ensures spec.entails(always(lift_state(stateful_set_in_create_request_msg_satisfies_unchangeable(rabbitmq)))),
{
    let inv = stateful_set_in_create_request_msg_satisfies_unchangeable(rabbitmq);
    let sts_res = SubResource::StatefulSet;
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(controller_id, rabbitmq)(s)
        &&& object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sts_res, rabbitmq)(s)
    };
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(spec, controller_id, rabbitmq);
    lemma_always_object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(controller_id, cluster, spec, sts_res, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(cluster.next()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(controller_id, rabbitmq)),
        lift_state(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sts_res, rabbitmq))
    );
    assert forall |s: ClusterState, s_prime: ClusterState| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let key = rabbitmq.object_ref();
        let sts_key = make_stateful_set_key(rabbitmq);
        assert forall |msg| s_prime.in_flight().contains(msg) && s_prime.resources().contains_key(key) && #[trigger] resource_create_request_msg(sts_key)(msg)
        implies certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    assert(s.controller_and_externals == s_prime.controller_and_externals);
                    assert(s.in_flight().contains(msg));
                    if s.resources().contains_key(key) {
                        assert(RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0
                        .transition_validation(RabbitmqClusterView::unmarshal(s.resources()[key])->Ok_0));
                    } else {
                        assert(s_prime.resources()[key].metadata.uid is Some);
                        assert(s_prime.resources()[key].metadata.uid->0 == s.api_server.uid_counter);
                        let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
                        assert(owner_refs is Some && owner_refs->0.len() == 1);
                        assert(owner_refs->0[0].uid != s.api_server.uid_counter);
                        assert(owner_refs->0[0] != RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0.controller_owner_ref());
                        assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0));
                    }
                },
                Step::ControllerStep(input) => {
                    if !s.in_flight().contains(msg) {
                        VStatefulSetView::marshal_preserves_integrity();
                        VStatefulSetView::marshal_spec_preserves_integrity();
                        lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sts_res, rabbitmq, s, s_prime, msg, step);
                        let triggering_cr_dynamic = s.ongoing_reconciles(controller_id)[key].triggering_cr;
                        let triggering_cr = RabbitmqClusterView::unmarshal(triggering_cr_dynamic).unwrap();
                        let etcd_cr = RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0;
                        assert(msg.content.get_create_request().obj.metadata.owner_references_only_contains(triggering_cr.controller_owner_ref()));
                        assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, triggering_cr));
                        if triggering_cr.metadata().uid is None || triggering_cr.metadata().uid->0 != etcd_cr.metadata().uid->0 {
                            assert(!msg.content.get_create_request().obj.metadata.owner_references_only_contains(etcd_cr.controller_owner_ref()));
                        } else {
                            assert(etcd_cr.transition_validation(triggering_cr));
                        }
                        assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0));
                    }
                    assert(certain_fields_of_stateful_set_stay_unchanged(msg.content.get_create_request().obj, RabbitmqClusterView::unmarshal(s_prime.resources()[key])->Ok_0));
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
                    assert(s.api_server == s_prime.api_server);
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), next, inv);
}

}
