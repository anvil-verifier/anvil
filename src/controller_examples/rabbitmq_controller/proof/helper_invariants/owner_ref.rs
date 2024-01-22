// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    model::reconciler::*,
    proof::{
        helper_invariants::{predicate::*, proof::*},
        predicate::*,
        resource::*,
    },
    trusted::{spec_types::*, step::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

/// Valid owner_references field satisfies that every owner reference in it valid uid, i.e., it points to some existing objects.
/// We don't test custom resource object here because we don't care about whether it's owner_references is valid.
pub open spec fn owner_references_is_valid(obj: DynamicObjectView, s: RMQCluster) -> bool {
    let owner_refs = obj.metadata.owner_references.get_Some_0();

    &&& obj.metadata.owner_references.is_Some()
    &&& owner_refs.len() == 1
    &&& owner_refs[0].uid < s.kubernetes_api_state.uid_counter
}

pub open spec fn object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let resource_key = get_request(sub_resource, rabbitmq).key;
        forall |msg|
            #[trigger] s.in_flight().contains(msg)
            ==> (
                resource_create_request_msg(resource_key)(msg)
                ==> owner_references_is_valid(msg.content.get_create_request().obj, s)
            ) && (
                resource_update_request_msg(resource_key)(msg)
                ==> owner_references_is_valid(msg.content.get_update_request().obj, s)
            )
    }
}

pub proof fn lemma_always_object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(
    spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures spec.entails(always(lift_state(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, rabbitmq)))),
{
    let inv = object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::triggering_cr_has_lower_uid_than_uid_counter()(s)
        &&& RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };
    RMQCluster::lemma_always_triggering_cr_has_lower_uid_than_uid_counter(spec);
    RMQCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()),
        lift_state(RMQCluster::triggering_cr_has_lower_uid_than_uid_counter()),
        lift_state(RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let create_valid = |msg: RMQMessage, s: RMQCluster| {
        resource_create_request_msg(resource_key)(msg) ==> owner_references_is_valid(msg.content.get_create_request().obj, s)
    };
    let update_valid = |msg: RMQMessage, s: RMQCluster| {
        resource_update_request_msg(resource_key)(msg) ==> owner_references_is_valid(msg.content.get_update_request().obj, s)
    };
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) implies create_valid(msg, s_prime) && update_valid(msg, s_prime) by {
            assert(s.kubernetes_api_state.uid_counter <= s_prime.kubernetes_api_state.uid_counter);
            if !s.in_flight().contains(msg) {
                object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references_helper(s, s_prime, sub_resource, rabbitmq, msg);
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

#[verifier(spinoff_prover)]
proof fn object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references_helper(
    s: RMQCluster, s_prime: RMQCluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, msg: RMQMessage
)
    requires
        !s.in_flight().contains(msg), s_prime.in_flight().contains(msg),
        RMQCluster::next()(s, s_prime),
        RMQCluster::triggering_cr_has_lower_uid_than_uid_counter()(s),
        RMQCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
    ensures
        resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg) ==> owner_references_is_valid(msg.content.get_create_request().obj, s_prime),
        resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg) ==> owner_references_is_valid(msg.content.get_update_request().obj, s_prime),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    assert(s.kubernetes_api_state.uid_counter <= s_prime.kubernetes_api_state.uid_counter);
    let step = choose |step| RMQCluster::next_step(s, s_prime, step);
    let input = step.get_ControllerStep_0();
    let cr = s.ongoing_reconciles()[input.1.get_Some_0()].triggering_cr;
    if resource_create_request_msg(resource_key)(msg) {
        lemma_resource_create_request_msg_implies_key_in_reconcile_equals(sub_resource, rabbitmq, s, s_prime, msg, step);
        let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
        assert(owner_refs == Some(seq![cr.controller_owner_ref()]));
        assert(owner_refs.is_Some());
        assert(owner_refs.get_Some_0().len() == 1);
        assert(owner_refs.get_Some_0()[0].uid < s.kubernetes_api_state.uid_counter);
    } else if resource_update_request_msg(resource_key)(msg) {
        lemma_resource_update_request_msg_implies_key_in_reconcile_equals(sub_resource, rabbitmq, s, s_prime, msg, step);
        let owner_refs = msg.content.get_update_request().obj.metadata.owner_references;
        assert(owner_refs == Some(seq![cr.controller_owner_ref()]));
        assert(owner_refs.is_Some());
        assert(owner_refs.get_Some_0().len() == 1);
        assert(owner_refs.get_Some_0()[0].uid < s.kubernetes_api_state.uid_counter);
    }
}

pub open spec fn every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let resource_key = get_request(sub_resource, rabbitmq).key;
        s.resources().contains_key(resource_key)
        ==> owner_references_is_valid(s.resources()[resource_key], s)
    }
}

pub proof fn lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(
    spec: TempPred<RMQCluster>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures spec.entails(always(lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sub_resource, rabbitmq)))),
{
    let inv = every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sub_resource, rabbitmq);
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, rabbitmq)(s)
    };
    lemma_always_object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(spec, sub_resource, rabbitmq);
    combine_spec_entails_always_n!(spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, rabbitmq)));
    let resource_key = get_request(sub_resource, rabbitmq).key;
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if s_prime.resources().contains_key(resource_key) {
            assert(s.kubernetes_api_state.uid_counter <= s_prime.kubernetes_api_state.uid_counter);
            if !s.resources().contains_key(resource_key) || s.resources()[resource_key].metadata.owner_references != s_prime.resources()[resource_key].metadata.owner_references {} else {}
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

}
