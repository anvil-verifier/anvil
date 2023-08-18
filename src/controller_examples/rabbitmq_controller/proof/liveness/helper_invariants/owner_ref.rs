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
    builtin_controllers::types::{built_in_controller_req_msg, BuiltinControllerChoice},
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
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
        spec.entails(always(lift_state(server_config_map_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)))),
        spec.entails(always(lift_state(every_update_cm_req_does_the_same(rabbitmq)))),
        spec.entails(always(lift_state(every_create_cm_req_does_the_same(rabbitmq)))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(server_config_map_has_owner_reference_pointing_to_current_cr(rabbitmq))))),
{
    let key = make_server_config_map_key(rabbitmq.object_ref());
    let eventual_owner_ref = |owner_ref: Option<Seq<OwnerReferenceView>>| {owner_ref == Some(seq![rabbitmq.controller_owner_ref()])};
    always_weaken(spec, every_update_cm_req_does_the_same(rabbitmq), RMQCluster::every_update_msg_sets_owner_references_as(key, eventual_owner_ref));
    always_weaken(spec, every_create_cm_req_does_the_same(rabbitmq), RMQCluster::every_create_msg_sets_owner_references_as(key, eventual_owner_ref));
    always_weaken(spec, server_config_map_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq), RMQCluster::object_has_no_finalizers(key));

    let state = |s: RMQCluster| {
        RMQCluster::desired_state_is(rabbitmq)(s)
        && server_config_map_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)(s)
    };
    invariant_n!(
        spec, lift_state(state), lift_state(RMQCluster::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(RMQCluster::garbage_collector_deletion_enabled(key))),
        lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(server_config_map_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq))
    );
    RMQCluster::lemma_eventually_objects_owner_references_satisfies(spec, key, eventual_owner_ref);
    temp_pred_equality(
        lift_state(server_config_map_has_owner_reference_pointing_to_current_cr(rabbitmq)),
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
        spec.entails(always(lift_state(stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)))),
        spec.entails(always(lift_state(every_update_sts_req_does_the_same(rabbitmq)))),
        spec.entails(always(lift_state(every_create_sts_req_does_the_same(rabbitmq)))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq))))),
{
    let key = make_stateful_set_key(rabbitmq.object_ref());
    let eventual_owner_ref = |owner_ref: Option<Seq<OwnerReferenceView>>| {owner_ref == Some(seq![rabbitmq.controller_owner_ref()])};
    always_weaken(spec, every_update_sts_req_does_the_same(rabbitmq), RMQCluster::every_update_msg_sets_owner_references_as(key, eventual_owner_ref));
    always_weaken(spec, every_create_sts_req_does_the_same(rabbitmq), RMQCluster::every_create_msg_sets_owner_references_as(key, eventual_owner_ref));
    always_weaken(spec, stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq), RMQCluster::object_has_no_finalizers(key));

    let state = |s: RMQCluster| {
        RMQCluster::desired_state_is(rabbitmq)(s)
        && stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq)(s)
    };
    invariant_n!(
        spec, lift_state(state), lift_state(RMQCluster::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(RMQCluster::garbage_collector_deletion_enabled(key))),
        lift_state(RMQCluster::desired_state_is(rabbitmq)),
        lift_state(stateful_set_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(rabbitmq))
    );
    RMQCluster::lemma_eventually_objects_owner_references_satisfies(spec, key, eventual_owner_ref);
    temp_pred_equality(
        lift_state(stateful_set_has_owner_reference_pointing_to_current_cr(rabbitmq)),
        lift_state(RMQCluster::objects_owner_references_satisfies(key, eventual_owner_ref))
    );
}

}
