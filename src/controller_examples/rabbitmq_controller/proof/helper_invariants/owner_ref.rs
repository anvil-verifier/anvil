// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::invariants::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::common::*,
    spec::{rabbitmqcluster::*, reconciler::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub proof fn lemma_eventually_only_valid_server_config_map_exists(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq)))),
        spec.entails(always(lift_state(every_update_server_cm_req_does_the_same(rabbitmq)))),
        spec.entails(always(lift_state(every_create_server_cm_req_does_the_same(rabbitmq)))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(object_of_key_only_has_owner_reference_pointing_to_current_cr(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq))))),
{
    let key = make_server_config_map_key(rabbitmq.object_ref());
    let eventual_owner_ref = |owner_ref: Option<Seq<OwnerReferenceView>>| {owner_ref == Some(seq![rabbitmq.controller_owner_ref()])};
    always_weaken(spec, every_update_server_cm_req_does_the_same(rabbitmq), RMQCluster::every_update_msg_sets_owner_references_as(key, eventual_owner_ref));
    always_weaken(spec, every_create_server_cm_req_does_the_same(rabbitmq), RMQCluster::every_create_msg_sets_owner_references_as(key, eventual_owner_ref));
    always_weaken(spec, object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq), RMQCluster::object_has_no_finalizers(key));

    let state = |s: RMQCluster| {
        RMQCluster::desired_state_is(rabbitmq)(s)
        && object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq)(s)
    };
    invariant_n!(
        spec, lift_state(state), lift_state(RMQCluster::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(RMQCluster::garbage_collector_deletion_enabled(key))),
        lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq))
    );
    RMQCluster::lemma_eventually_objects_owner_references_satisfies(spec, key, eventual_owner_ref);
    temp_pred_equality(
        lift_state(object_of_key_only_has_owner_reference_pointing_to_current_cr(make_server_config_map_key(rabbitmq.object_ref()), rabbitmq)),
        lift_state(RMQCluster::objects_owner_references_satisfies(key, eventual_owner_ref))
    );
}

pub proof fn lemma_eventually_only_valid_stateful_set_exists(spec: TempPred<RMQCluster>, rabbitmq: RabbitmqClusterView)
    requires
        rabbitmq.well_formed(),
        spec.entails(always(lift_state(RMQCluster::busy_disabled()))),
        spec.entails(always(lift_action(RMQCluster::next()))),
        spec.entails(tla_forall(|i| RMQCluster::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| RMQCluster::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(RMQCluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq)))),
        spec.entails(always(lift_state(every_update_sts_req_does_the_same(rabbitmq)))),
        spec.entails(always(lift_state(every_create_sts_req_does_the_same(rabbitmq)))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(object_of_key_only_has_owner_reference_pointing_to_current_cr(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq))))),
{
    let key = make_stateful_set_key(rabbitmq.object_ref());
    let eventual_owner_ref = |owner_ref: Option<Seq<OwnerReferenceView>>| {owner_ref == Some(seq![rabbitmq.controller_owner_ref()])};
    always_weaken(spec, every_update_sts_req_does_the_same(rabbitmq), RMQCluster::every_update_msg_sets_owner_references_as(key, eventual_owner_ref));
    always_weaken(spec, every_create_sts_req_does_the_same(rabbitmq), RMQCluster::every_create_msg_sets_owner_references_as(key, eventual_owner_ref));
    always_weaken(spec, object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq), RMQCluster::object_has_no_finalizers(key));

    let state = |s: RMQCluster| {
        RMQCluster::desired_state_is(rabbitmq)(s)
        && object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq)(s)
    };
    invariant_n!(
        spec, lift_state(state), lift_state(RMQCluster::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(RMQCluster::garbage_collector_deletion_enabled(key))),
        lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(object_of_key_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq))
    );
    RMQCluster::lemma_eventually_objects_owner_references_satisfies(spec, key, eventual_owner_ref);
    temp_pred_equality(
        lift_state(object_of_key_only_has_owner_reference_pointing_to_current_cr(make_stateful_set_key(rabbitmq.object_ref()), rabbitmq)),
        lift_state(RMQCluster::objects_owner_references_satisfies(key, eventual_owner_ref))
    );
}

/// Valid owner_references field satisfies that every owner reference in it valid uid, i.e., it points to some existing objects.
/// We don't test custom resource object here because we don't care about whether it's owner_references is valid.
pub open spec fn owner_references_is_valid(obj: DynamicObjectView, s: RMQCluster) -> bool {
    if obj.kind.is_CustomResourceKind() {
        true
    } else {
        let owner_refs = obj.metadata.owner_references.get_Some_0();
        forall |i|
            #![auto] 0 <= i < owner_refs.len()
            ==> owner_refs[i].uid < s.kubernetes_api_state.uid_counter
    }
}

pub open spec fn object_in_every_create_or_update_request_msg_only_has_valid_owner_references() -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |msg|
            #[trigger] s.message_in_flight(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_APIRequest()
            ==> (
                msg.content.is_create_request() && msg.content.get_create_request().obj.metadata.owner_references.is_Some()
                ==> owner_references_is_valid(msg.content.get_create_request().obj, s)
            ) && (
                msg.content.is_update_request() && msg.content.get_update_request().obj.metadata.owner_references.is_Some()
                ==> owner_references_is_valid(msg.content.get_update_request().obj, s)
            )
    }
}

pub proof fn lemma_always_object_in_every_create_or_update_request_msg_only_has_valid_owner_references(spec: TempPred<RMQCluster>)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(object_in_every_create_or_update_request_msg_only_has_valid_owner_references()))),
{
    let inv = object_in_every_create_or_update_request_msg_only_has_valid_owner_references();
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& RMQCluster::triggering_cr_has_lower_uid_than_uid_counter()(s)
    };
    RMQCluster::lemma_always_triggering_cr_has_lower_uid_than_uid_counter(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(RMQCluster::triggering_cr_has_lower_uid_than_uid_counter())
    );
    let create_valid = |msg: RMQMessage, s: RMQCluster| {
        msg.content.is_create_request() && msg.content.get_create_request().obj.metadata.owner_references.is_Some()
        ==> owner_references_is_valid(msg.content.get_create_request().obj, s)
    };
    let update_valid = |msg: RMQMessage, s: RMQCluster| {
        msg.content.is_update_request() && msg.content.get_update_request().obj.metadata.owner_references.is_Some()
        ==> owner_references_is_valid(msg.content.get_update_request().obj, s)
    };
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.message_in_flight(msg) && msg.dst.is_KubernetesAPI() && msg.content.is_APIRequest()
        implies create_valid(msg, s_prime) && update_valid(msg, s_prime) by {
            assert(s.kubernetes_api_state.uid_counter <= s_prime.kubernetes_api_state.uid_counter);
            if !s.message_in_flight(msg) {
                let step = choose |step| RMQCluster::next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep(input) => {
                        let cr = s.triggering_cr_of(input.1.get_Some_0());
                        if msg.content.is_create_request() {
                            let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
                            if owner_refs.is_Some() {
                                assert(owner_refs == Some(seq![cr.controller_owner_ref()]));
                            }
                        } else if msg.content.is_update_request() {
                            let owner_refs = msg.content.get_update_request().obj.metadata.owner_references;
                            if owner_refs.is_Some() {
                                assert(owner_refs == Some(seq![cr.controller_owner_ref()]));
                            }
                        }
                    },
                    Step::ClientStep() => {
                        if msg.content.is_create_request() {
                            assert(msg.content.get_create_request().obj.kind.is_CustomResourceKind());
                        } else if msg.content.is_update_request() {
                            assert(msg.content.get_update_request().obj.kind.is_CustomResourceKind());
                        }
                    },
                    Step::BuiltinControllersStep(_) => {
                        assert(!msg.content.is_update_request() && !msg.content.is_create_request());
                    },
                    _ => {}
                }
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

pub open spec fn every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter() -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |key|
            #[trigger] s.resource_key_exists(key)
            && s.resource_obj_of(key).metadata.owner_references.is_Some()
            ==> owner_references_is_valid(s.resource_obj_of(key), s)
    }
}

pub proof fn lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(spec: TempPred<RMQCluster>)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(always(lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter()))),
{
    let inv = every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter();
    let next = |s, s_prime| {
        &&& RMQCluster::next()(s, s_prime)
        &&& object_in_every_create_or_update_request_msg_only_has_valid_owner_references()(s)
    };
    lemma_always_object_in_every_create_or_update_request_msg_only_has_valid_owner_references(spec);
    combine_spec_entails_always_n!(spec, lift_action(next), lift_action(RMQCluster::next()), lift_state(object_in_every_create_or_update_request_msg_only_has_valid_owner_references()));
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |key|
        #[trigger] s_prime.resource_key_exists(key) && s_prime.resource_obj_of(key).metadata.owner_references.is_Some()
        implies owner_references_is_valid(s_prime.resource_obj_of(key), s_prime) by {
            assert(s.kubernetes_api_state.uid_counter <= s_prime.kubernetes_api_state.uid_counter);
            if !s.resource_key_exists(key) || s.resource_obj_of(key).metadata.owner_references != s_prime.resource_obj_of(key).metadata.owner_references {} else {}
        }
    }
    init_invariant(spec, RMQCluster::init(), next, inv);
}

}
