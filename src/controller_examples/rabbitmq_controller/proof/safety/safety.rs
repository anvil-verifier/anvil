// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::{common::*, helper_invariants::*},
    spec::{rabbitmqcluster::*, reconciler::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

/// To prove the safety property about stateful set, we need to first specify what the property is.
/// 
/// Previously, we planned to use Message to describe the possible update/deletion/creation actions, and also specify the 
/// relevant properties. However, it is better not to include Message in the description the high-level safety property 
/// because Message is just a tool and a detail of the system. For update action, one way to circumvent using Message is 
/// to talk about the previous and current state: an object being updated means that it exists in both states but changes 
/// in current state.
spec fn stateful_set_not_scaled_down(rabbitmq: RabbitmqClusterView) -> ActionPred<RMQCluster> {
    |s: RMQCluster, s_prime: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        s.resource_key_exists(sts_key)
        && s_prime.resource_key_exists(sts_key)
        ==> replicas_of_stateful_set(s_prime.resource_obj_of(sts_key)) >= replicas_of_stateful_set(s.resource_obj_of(sts_key))
    }
}

proof fn lemma_stateful_set_never_scaled_down_for_all(spec: TempPred<RMQCluster>)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        forall |rabbitmq: RabbitmqClusterView|
            spec.entails(always(lift_action(#[trigger] stateful_set_not_scaled_down(rabbitmq)))),
{
    assert forall |rabbitmq| spec.entails(always(lift_action(#[trigger] stateful_set_not_scaled_down(rabbitmq)))) by {
        lemma_stateful_set_never_scaled_down_for_rabbitmq(spec, rabbitmq);
    }
}

/// This invariant is exactly the high-level property. The proof of this invariant is where we talk about update Message. It requires another two invariants to hold all the time:
/// - replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd
/// - object_in_sts_update_request_has_smaller_rv_than_etcd
/// 
/// Invariant 2 is to show that every stateful set update request must specify the resource version because stateful set is allowed to update unconditionally. If resource version can be none, we can't rule out invalid update request through resource version. Invariant 3 is quite obvious.
proof fn lemma_stateful_set_never_scaled_down_for_rabbitmq(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_action(stateful_set_not_scaled_down(rabbitmq)))),
{
    let inv = stateful_set_not_scaled_down(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)(s)
        &&& object_in_sts_update_request_has_smaller_rv_than_etcd(rabbitmq)(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
    };
    lemma_always_replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(spec, rabbitmq);
    lemma_always_object_in_sts_update_request_has_smaller_rv_than_etcd(spec, rabbitmq);
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    assert forall |s, s_prime| #[trigger] next(s, s_prime) implies stateful_set_not_scaled_down(rabbitmq)(s, s_prime) by {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        if s.resource_key_exists(sts_key) && s_prime.resource_key_exists(sts_key) {
            if s.resource_obj_of(sts_key) != s_prime.resource_obj_of(sts_key) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                let input = step.get_KubernetesAPIStep_0().get_Some_0();
                if input.content.is_delete_request() {
                    assert(StatefulSetView::from_dynamic_object(s.resource_obj_of(sts_key)).get_Ok_0().spec == StatefulSetView::from_dynamic_object(s_prime.resource_obj_of(sts_key)).get_Ok_0().spec);
                } else {
                    assert(input.content.is_update_request());
                    assert(s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == input.content.get_update_request().obj.metadata.resource_version.get_Some_0());
                    assert(replicas_of_stateful_set(s_prime.resource_obj_of(sts_key)) == replicas_of_stateful_set(input.content.get_update_request().obj));
                    assert(replicas_of_stateful_set(s_prime.resource_obj_of(sts_key)) >= replicas_of_stateful_set(s.resource_obj_of(sts_key)));
                }
            }
        }
    }
    invariant_n!(
        spec, lift_action(next), lift_action(inv),
        lift_action(RMQCluster::next()), lift_state(replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)),
        lift_state(object_in_sts_update_request_has_smaller_rv_than_etcd(rabbitmq)),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()), later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed()))
    );
}

spec fn replicas_of_rabbitmq(obj: DynamicObjectView) -> int
    recommends
        obj.kind.is_CustomResourceKind(),
{
    RabbitmqClusterView::from_dynamic_object(obj).get_Ok_0().spec.replicas
}

spec fn replicas_of_stateful_set(obj: DynamicObjectView) -> int
    recommends
        obj.kind.is_StatefulSetKind(),
{
    StatefulSetView::from_dynamic_object(obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0()
}

spec fn object_in_sts_update_request_has_smaller_rv_than_etcd(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        let etcd_rv = s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0();
        forall |msg: RMQMessage|
            #[trigger] s.message_in_flight(msg)
            && sts_update_request_msg(rabbitmq.object_ref())(msg)
            ==> msg.content.get_update_request().obj.metadata.resource_version.is_Some()
                && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
    }
}

proof fn lemma_always_object_in_sts_update_request_has_smaller_rv_than_etcd(
    spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(object_in_sts_update_request_has_smaller_rv_than_etcd(rabbitmq)))),
{
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(rabbitmq.object_ref());
    let upd_rv_leq = |msg: RMQMessage, s: RMQCluster| {
        sts_update_request_msg(rabbitmq.object_ref())(msg)
        ==> msg.content.get_update_request().obj.metadata.resource_version.is_Some()
            && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter
    };
    let inv = object_in_sts_update_request_has_smaller_rv_than_etcd(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq)(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::object_in_ok_get_response_has_smaller_rv_than_etcd(sts_key)(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    lemma_always_response_at_after_get_stateful_set_step_is_sts_get_response(spec, rabbitmq);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    RMQCluster::lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec, sts_key);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        lift_state(response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq)),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::object_in_ok_get_response_has_smaller_rv_than_etcd(sts_key))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let etcd_rv = s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0();
        assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && sts_update_request_msg(rabbitmq.object_ref())(msg) implies
        msg.content.get_update_request().obj.metadata.resource_version.is_Some()
        && msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s_prime.kubernetes_api_state.resource_version_counter by {
            let step = choose |step| RMQCluster::next_step(s, s_prime, step);
            if s.message_in_flight(msg) {
                assert(s.kubernetes_api_state.resource_version_counter <= s_prime.kubernetes_api_state.resource_version_counter);
            } else if sts_update_request_msg(rabbitmq.object_ref())(msg) {
                lemma_stateful_set_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                assert(at_rabbitmq_step(key, RabbitmqReconcileStep::AfterUpdateStatefulSet)(s_prime));
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

/// This function defined a replicas order for stateful set object. Here, obj can be the etcd statful set object, the object 
/// in create/update stateful set object. We define this order because, the replicas in the update request is derived from 
/// the triggering cr; so, in order to show the updated replicas is no smaller than the original one, we need to show that 
/// the original one (the one stored in etcd)'s replicas is no larger than that of triggering cr. obj.metadata.owner_references_only_contains
/// (s.triggering_cr_of(key).controller_owner_ref()) here is to ensure that the cr is still the one that creates the stateful 
/// set object. The left two comparison is to assist the last one because when the state moves to the next state, the triggering_cr 
/// may be assigned (inserted or updated).
spec fn replicas_satisfies_order(obj: DynamicObjectView, rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster>
    recommends
        obj.kind.is_StatefulSetKind(),
{
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let sts_replicas = replicas_of_stateful_set(obj);
        &&& s.resource_key_exists(key)
            && obj.metadata.owner_references_only_contains(RabbitmqClusterView::from_dynamic_object(s.resource_obj_of(key)).get_Ok_0().controller_owner_ref())
            ==> sts_replicas <= replicas_of_rabbitmq(s.resource_obj_of(key))
        &&& s.reconcile_scheduled_for(key)
            && obj.metadata.owner_references_only_contains(s.reconcile_scheduled_obj_of(key).controller_owner_ref())
            ==> sts_replicas <= s.reconcile_scheduled_obj_of(key).spec.replicas
        &&& s.reconcile_state_contains(key)
            && obj.metadata.owner_references_only_contains(s.triggering_cr_of(key).controller_owner_ref())
            ==> sts_replicas <= s.triggering_cr_of(key).spec.replicas
    }
}

spec fn replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        forall |msg: RMQMessage|
            #[trigger] s.message_in_flight(msg)
            && sts_update_request_msg(rabbitmq.object_ref())(msg)
            && s.resource_key_exists(sts_key)
            && s.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == msg.content.get_update_request().obj.metadata.resource_version.get_Some_0()
            ==> replicas_of_stateful_set(s.resource_obj_of(sts_key)) <= replicas_of_stateful_set(msg.content.get_update_request().obj)
    }
}

proof fn lemma_always_replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)))),
{
    let inv = replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq);
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(key);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)(s_prime)
        &&& object_in_sts_update_request_has_smaller_rv_than_etcd(rabbitmq)(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)(s)
        &&& response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq)(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    lemma_always_replicas_of_etcd_stateful_set_satisfies_order(spec, rabbitmq);
    always_to_always_later(spec, lift_state(replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)));
    lemma_always_object_in_sts_update_request_has_smaller_rv_than_etcd(spec, rabbitmq);
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    RMQCluster::lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, sts_key);
    lemma_always_response_at_after_get_stateful_set_step_is_sts_get_response(spec, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()), later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        later(lift_state(replicas_of_etcd_stateful_set_satisfies_order(rabbitmq))),
        lift_state(object_in_sts_update_request_has_smaller_rv_than_etcd(rabbitmq)),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)),
        lift_state(response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd_induction(rabbitmq, s, s_prime);
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}


proof fn replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd_induction(rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster)
    requires
        RMQCluster::next()(s, s_prime),
        RMQCluster::each_object_in_etcd_is_well_formed()(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s_prime),
        replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)(s_prime),
        replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)(s),
        object_in_sts_update_request_has_smaller_rv_than_etcd(rabbitmq)(s),
        RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        RMQCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(make_stateful_set_key(rabbitmq.object_ref()))(s),
        response_at_after_get_stateful_set_step_is_sts_get_response(rabbitmq)(s),
    ensures
        replicas_of_stateful_set_update_request_msg_is_no_smaller_than_etcd(rabbitmq)(s_prime),
{
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(key);
    assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && sts_update_request_msg(rabbitmq.object_ref())(msg)
    && s_prime.resource_key_exists(sts_key)
    && s_prime.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() implies StatefulSetView::from_dynamic_object(s_prime.resource_obj_of(sts_key)).get_Ok_0().spec.get_Some_0().replicas.get_Some_0()
    <= replicas_of_stateful_set(msg.content.get_update_request().obj) by {
        let step = choose |step| RMQCluster::next_step(s, s_prime, step);
        if s.message_in_flight(msg) {
            if !s.resource_key_exists(sts_key) || s.resource_obj_of(sts_key) != s_prime.resource_obj_of(sts_key) {
                assert(s_prime.resource_obj_of(sts_key).metadata.resource_version.get_Some_0() == s.kubernetes_api_state.resource_version_counter);
                assert(msg.content.get_update_request().obj.metadata.resource_version.get_Some_0() < s.kubernetes_api_state.resource_version_counter);
                assert(false);
            } else {
                assert(StatefulSetView::from_dynamic_object(s_prime.resource_obj_of(sts_key)).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() <= replicas_of_stateful_set(msg.content.get_update_request().obj));
            }
        } else {
            lemma_stateful_set_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
            StatefulSetView::spec_integrity_is_preserved_by_marshal();
            assert(s_prime.resource_obj_of(sts_key) == s.resource_obj_of(sts_key));
            assert(replicas_of_stateful_set(msg.content.get_update_request().obj) == s.triggering_cr_of(key).spec.replicas);
            assert(s.triggering_cr_of(key) == s_prime.triggering_cr_of(key));
            assert(s_prime.resource_obj_of(sts_key).metadata.owner_references_only_contains(s.triggering_cr_of(key).controller_owner_ref()));
            assert(StatefulSetView::from_dynamic_object(s_prime.resource_obj_of(sts_key)).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() <= replicas_of_stateful_set(msg.content.get_update_request().obj));
        }
    }
}

spec fn replicas_of_etcd_stateful_set_satisfies_order(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let key = rabbitmq.object_ref();
        let sts_key = make_stateful_set_key(key);
        s.resource_key_exists(sts_key) ==> replicas_satisfies_order(s.resource_obj_of(sts_key), rabbitmq)(s)
    }
}

proof fn lemma_always_replicas_of_etcd_stateful_set_satisfies_order(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)))),
{
    let inv = replicas_of_etcd_stateful_set_satisfies_order(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter()(s)
        &&& replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq)(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(spec);
    lemma_always_replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(spec, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter()),
        lift_state(replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        replicas_of_etcd_stateful_set_satisfies_order_induction(rabbitmq, s, s_prime);
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

/// To do this induction, we mainly proves how the invariant holds if everything is not changed from the previous state.
/// If the state changes, we rely on the property of create/update request message which is proved in another lemma.
proof fn replicas_of_etcd_stateful_set_satisfies_order_induction(rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster)
    requires
        RMQCluster::next()(s, s_prime),
        replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)(s),
        replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq)(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s_prime),
        every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter()(s),
    ensures
        replicas_of_etcd_stateful_set_satisfies_order(rabbitmq)(s_prime),
{
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(key);
    if s_prime.resource_key_exists(sts_key) {
        if s.resource_key_exists(sts_key) && s.resource_obj_of(sts_key) == s_prime.resource_obj_of(sts_key) {
            if s_prime.resource_key_exists(key) {
                if !s.resource_key_exists(key) {
                    assert(s_prime.resource_obj_of(key).metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                    let owner_refs = s.resource_obj_of(sts_key).metadata.owner_references;
                    if owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1 {
                        assert(owner_refs.get_Some_0()[0].uid != s.kubernetes_api_state.uid_counter);
                        assert(owner_refs.get_Some_0()[0] != RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).get_Ok_0().controller_owner_ref());
                    }
                } else if s.resource_obj_of(key) != s_prime.resource_obj_of(key) {
                    assert(s.resource_obj_of(key).metadata.uid == s_prime.resource_obj_of(key).metadata.uid);
                    assert(RabbitmqClusterView::from_dynamic_object(s.resource_obj_of(key)).is_Ok());
                    assert(RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).is_Ok());
                    assert(RabbitmqClusterView::from_dynamic_object(s.resource_obj_of(key)).get_Ok_0().controller_owner_ref() == RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).get_Ok_0().controller_owner_ref());
                    assert(replicas_of_rabbitmq(s.resource_obj_of(key)) <= replicas_of_rabbitmq(s_prime.resource_obj_of(key)));
                }
            }
            if s_prime.reconcile_scheduled_for(key) {
                if !s.reconcile_scheduled_for(key) || s.reconcile_scheduled_obj_of(key) != s_prime.reconcile_scheduled_obj_of(key) {
                    assert(s_prime.reconcile_scheduled_obj_of(key) == RabbitmqClusterView::from_dynamic_object(s.resource_obj_of(key)).get_Ok_0());
                }
            }
            if s_prime.reconcile_state_contains(key) {
                if !s.reconcile_state_contains(key) || s.triggering_cr_of(key) != s_prime.triggering_cr_of(key) {
                    assert(s_prime.triggering_cr_of(key) == s.reconcile_scheduled_obj_of(key));
                }
            }
        } else if s.resource_key_exists(sts_key) && s.resource_obj_of(sts_key) != s_prime.resource_obj_of(sts_key) {
            assert(replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq)(s));
            assert(replicas_satisfies_order(s_prime.resource_obj_of(sts_key), rabbitmq)(s_prime));
        } else {
            assert(replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq)(s));
            assert(replicas_satisfies_order(s_prime.resource_obj_of(sts_key), rabbitmq)(s_prime));
        }
    }
}

spec fn replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let sts_key = make_stateful_set_key(rabbitmq.object_ref());
        forall |msg: RMQMessage|
            #[trigger] s.message_in_flight(msg)
            ==> (
                sts_create_request_msg(rabbitmq.object_ref())(msg)
                ==> replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s)
            ) && (
                sts_update_request_msg(rabbitmq.object_ref())(msg)
                ==> replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s)
            )
    }
}

proof fn lemma_always_replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq)))),
{
    let inv = replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s)
        &&& RMQCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& RMQCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(rabbitmq)(s)
        &&& object_in_every_create_or_update_request_msg_only_has_valid_owner_references()(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(RMQCluster::each_object_in_etcd_is_well_formed()));
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    RMQCluster::lemma_always_transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(spec, rabbitmq);
    lemma_always_object_in_every_create_or_update_request_msg_only_has_valid_owner_references(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(RMQCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(rabbitmq)),
        lift_state(object_in_every_create_or_update_request_msg_only_has_valid_owner_references())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.message_in_flight(msg) implies (sts_create_request_msg(rabbitmq.object_ref())(msg)
        ==> replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s_prime)) && (sts_update_request_msg(rabbitmq.object_ref())(msg)
        ==> replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime)) by {
            if sts_create_request_msg(rabbitmq.object_ref())(msg) {
                replicas_of_stateful_set_create_request_msg_satisfies_order_induction(rabbitmq, s, s_prime, msg);
            }
            if sts_update_request_msg(rabbitmq.object_ref())(msg) {
                replicas_of_stateful_set_update_request_msg_satisfies_order_induction(rabbitmq, s, s_prime, msg);
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

proof fn replicas_of_stateful_set_create_request_msg_satisfies_order_induction(
    rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster, msg: RMQMessage
)
    requires
        RMQCluster::next()(s, s_prime),
        RMQCluster::each_object_in_etcd_is_well_formed()(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s_prime),
        RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        RMQCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(rabbitmq)(s),
        object_in_every_create_or_update_request_msg_only_has_valid_owner_references()(s),
        replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq)(s),
        s_prime.message_in_flight(msg),
        sts_create_request_msg(rabbitmq.object_ref())(msg),
    ensures
        replicas_satisfies_order(msg.content.get_create_request().obj, rabbitmq)(s_prime),
{
    let step = choose |step| RMQCluster::next_step(s, s_prime, step);
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(key);
    match step {
        Step::KubernetesAPIStep(input) => {
            assert(s.controller_state == s_prime.controller_state);
            assert(s.message_in_flight(msg));
            if s_prime.resource_key_exists(key) {
                if s.resource_key_exists(key) {
                    assert(replicas_of_rabbitmq(s.resource_obj_of(key)) <= replicas_of_rabbitmq(s_prime.resource_obj_of(key)));
                } else {
                    assert(s_prime.resource_obj_of(key).metadata.uid.is_Some());
                    assert(s_prime.resource_obj_of(key).metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                    let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
                    if owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1 {
                        assert(owner_refs.get_Some_0()[0].uid != s.kubernetes_api_state.uid_counter);
                        assert(owner_refs.get_Some_0()[0] != RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).get_Ok_0().controller_owner_ref());
                    }
                }
            }
        },
        Step::ControllerStep(input) => {
            if !s.message_in_flight(msg) {
                StatefulSetView::spec_integrity_is_preserved_by_marshal();
                lemma_stateful_set_create_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                assert(StatefulSetView::from_dynamic_object(msg.content.get_create_request().obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() <= s.triggering_cr_of(key).spec.replicas);
            }
        },
        Step::ScheduleControllerReconcileStep(input) => {
            assert(s.message_in_flight(msg));
            assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
        },
        Step::RestartController() => {
            assert(s.message_in_flight(msg));
            assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
        },
        _ => {
            assert(s.message_in_flight(msg));
            assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
            assert(s.controller_state == s_prime.controller_state);
        }
    }
}

proof fn replicas_of_stateful_set_update_request_msg_satisfies_order_induction(
    rabbitmq: RabbitmqClusterView, s: RMQCluster, s_prime: RMQCluster, msg: RMQMessage
)
    requires
        RMQCluster::next()(s, s_prime),
        RMQCluster::each_object_in_etcd_is_well_formed()(s),
        RMQCluster::each_object_in_etcd_is_well_formed()(s_prime),
        RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        RMQCluster::transition_rule_applies_to_etcd_and_scheduled_and_triggering_cr(rabbitmq)(s),
        object_in_every_create_or_update_request_msg_only_has_valid_owner_references()(s),
        replicas_of_stateful_set_create_or_update_request_msg_satisfies_order(rabbitmq)(s),
        s_prime.message_in_flight(msg),
        sts_update_request_msg(rabbitmq.object_ref())(msg),
    ensures
        replicas_satisfies_order(msg.content.get_update_request().obj, rabbitmq)(s_prime),
{
    let step = choose |step| RMQCluster::next_step(s, s_prime, step);
    let key = rabbitmq.object_ref();
    let sts_key = make_stateful_set_key(key);
    match step {
        Step::KubernetesAPIStep(input) => {
            assert(s.message_in_flight(msg));
            assert(s.controller_state == s_prime.controller_state);
            if s_prime.resource_key_exists(key) {
                if s.resource_key_exists(key) {
                    assert(replicas_of_rabbitmq(s.resource_obj_of(key)) <= replicas_of_rabbitmq(s_prime.resource_obj_of(key)));
                } else {
                    assert(s_prime.resource_obj_of(key).metadata.uid.is_Some());
                    assert(s_prime.resource_obj_of(key).metadata.uid.get_Some_0() == s.kubernetes_api_state.uid_counter);
                    let owner_refs = msg.content.get_update_request().obj.metadata.owner_references;
                    if owner_refs.is_Some() && owner_refs.get_Some_0().len() == 1 {
                        assert(owner_refs.get_Some_0()[0].uid < s.kubernetes_api_state.uid_counter);
                        assert(owner_refs.get_Some_0()[0] != RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).get_Ok_0().controller_owner_ref());
                    }
                }
            }
        },
        Step::ControllerStep(input) => {
            if !s.message_in_flight(msg) {
                StatefulSetView::spec_integrity_is_preserved_by_marshal();
                lemma_stateful_set_update_request_msg_implies_key_in_reconcile_equals(key, s, s_prime, msg, step);
                assert(StatefulSetView::from_dynamic_object(msg.content.get_update_request().obj).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() <= s.triggering_cr_of(key).spec.replicas);
            }
        },
        Step::ScheduleControllerReconcileStep(input) => {
            assert(s.message_in_flight(msg));
            assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
        },
        Step::RestartController() => {
            assert(s.message_in_flight(msg));
            assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
        },
        _ => {
            assert(s.message_in_flight(msg));
            assert(s.kubernetes_api_state == s_prime.kubernetes_api_state);
            assert(s.controller_state == s_prime.controller_state);
        }
    }
}

}
