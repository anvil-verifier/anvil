// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::{
    model::reconciler::*,
    proof::{
        helper_invariants::{predicate::*, proof::*},
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
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

/// Valid owner_references field satisfies that every owner reference in it valid uid, i.e., it points to some existing objects.
/// We don't test custom resource object here because we don't care about whether it's owner_references is valid.
pub open spec fn owner_references_is_valid(obj: DynamicObjectView, s: FBCluster) -> bool {
    let owner_refs = obj.metadata.owner_references.get_Some_0();

    &&& obj.metadata.owner_references.is_Some()
    &&& owner_refs.len() == 1
    &&& owner_refs[0].uid < s.kubernetes_api_state.uid_counter
}

pub open spec fn object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(
    sub_resource: SubResource, fb: FluentBitView
) -> StatePred<FBCluster> {
    |s: FBCluster| {
        let resource_key = get_request(sub_resource, fb).key;
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
    spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView
)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, fb)))),
{
    let inv = object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, fb);
    let next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::triggering_cr_has_lower_uid_than_uid_counter()(s)
        &&& FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };
    FBCluster::lemma_always_triggering_cr_has_lower_uid_than_uid_counter(spec);
    FBCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(FBCluster::next()),
        lift_state(FBCluster::triggering_cr_has_lower_uid_than_uid_counter()),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    let resource_key = get_request(sub_resource, fb).key;
    let create_valid = |msg: FBMessage, s: FBCluster| {
        resource_create_request_msg(resource_key)(msg) ==> owner_references_is_valid(msg.content.get_create_request().obj, s)
    };
    let update_valid = |msg: FBMessage, s: FBCluster| {
        resource_update_request_msg(resource_key)(msg) ==> owner_references_is_valid(msg.content.get_update_request().obj, s)
    };
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) implies create_valid(msg, s_prime) && update_valid(msg, s_prime) by {
            assert(s.kubernetes_api_state.uid_counter <= s_prime.kubernetes_api_state.uid_counter);
            if !s.in_flight().contains(msg) {
                let step = choose |step| FBCluster::next_step(s, s_prime, step);
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fb, s, s_prime, msg, step);
                let input = step.get_ControllerStep_0();
                let cr = s.ongoing_reconciles()[input.1.get_Some_0()].triggering_cr;
                if resource_create_request_msg(resource_key)(msg) {
                    let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
                    assert(owner_refs == Some(seq![cr.controller_owner_ref()]));
                    assert(owner_refs.is_Some());
                    assert(owner_refs.get_Some_0().len() == 1);
                    assert(owner_refs.get_Some_0()[0].uid < s.kubernetes_api_state.uid_counter);
                } else if resource_update_request_msg(resource_key)(msg) {
                    let owner_refs = msg.content.get_update_request().obj.metadata.owner_references;
                    assert(owner_refs == Some(seq![cr.controller_owner_ref()]));
                    assert(owner_refs.is_Some());
                    assert(owner_refs.get_Some_0().len() == 1);
                    assert(owner_refs.get_Some_0()[0].uid < s.kubernetes_api_state.uid_counter);
                }
            }
        }
    }
    init_invariant(spec, FBCluster::init(), next, inv);
}

pub open spec fn every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(
    sub_resource: SubResource, fb: FluentBitView
) -> StatePred<FBCluster> {
    |s: FBCluster| {
        let resource_key = get_request(sub_resource, fb).key;
        s.resources().contains_key(resource_key)
        ==> owner_references_is_valid(s.resources()[resource_key], s)
    }
}

pub proof fn lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(
    spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView
)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sub_resource, fb)))),
{
    let inv = every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sub_resource, fb);
    let next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, fb)(s)
    };
    lemma_always_object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(spec, sub_resource, fb);
    combine_spec_entails_always_n!(spec, lift_action(next), lift_action(FBCluster::next()), lift_state(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, fb)));
    let resource_key = get_request(sub_resource, fb).key;
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if s_prime.resources().contains_key(resource_key) {
            assert(s.kubernetes_api_state.uid_counter <= s_prime.kubernetes_api_state.uid_counter);
            if !s.resources().contains_key(resource_key) || s.resources()[resource_key].metadata.owner_references != s_prime.resources()[resource_key].metadata.owner_references {} else {}
        }
    }
    init_invariant(spec, FBCluster::init(), next, inv);
}

}
