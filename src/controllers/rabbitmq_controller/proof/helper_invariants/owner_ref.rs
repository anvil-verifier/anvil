// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
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
    trusted::{spec_types::*, step::*, rely_guarantee::*},
};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::temporal_logic::{defs::*, rules::*};
use crate::rabbitmq_controller::model::install::*;
use vstd::prelude::*;

verus! {

// Valid owner_references field satisfies that every owner reference in it valid uid, i.e., it points to some existing objects.
// We don't test custom resource object here because we don't care about whether it's owner_references is valid.
pub open spec fn owner_references_is_valid(obj: DynamicObjectView, s: ClusterState) -> bool {
    let owner_refs = obj.metadata.owner_references->0;

    &&& obj.metadata.owner_references is Some
    &&& owner_refs.len() == 1
    &&& owner_refs[0].uid < s.api_server.uid_counter
}

pub open spec fn object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
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
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, rabbitmq)))),
{
    let inv = object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, rabbitmq);
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::triggering_cr_has_lower_uid_than_uid_counter(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
    };
    cluster.lemma_always_cr_states_are_unmarshallable::<RabbitmqReconciler, RabbitmqReconcileState, RabbitmqClusterView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_triggering_cr_has_lower_uid_than_uid_counter(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        lift_state(Cluster::triggering_cr_has_lower_uid_than_uid_counter(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        later(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let create_valid = |msg: Message, s: ClusterState| {
        resource_create_request_msg(resource_key)(msg) ==> owner_references_is_valid(msg.content.get_create_request().obj, s)
    };
    let update_valid = |msg: Message, s: ClusterState| {
        resource_update_request_msg(resource_key)(msg) ==> owner_references_is_valid(msg.content.get_update_request().obj, s)
    };
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) implies create_valid(msg, s_prime) && update_valid(msg, s_prime) by {
            assert(s.api_server.uid_counter <= s_prime.api_server.uid_counter);
            if !s.in_flight().contains(msg) {
                object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references_helper(controller_id, cluster, s, s_prime, sub_resource, rabbitmq, msg);
            }
        }
    }
    init_invariant(spec, cluster.init(), next, inv);
}

#[verifier(spinoff_prover)]
proof fn object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references_helper(
    controller_id: int,
    cluster: Cluster, s: ClusterState, s_prime: ClusterState, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, msg: Message
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        Cluster::triggering_cr_has_lower_uid_than_uid_counter(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id) ==> #[trigger] rmq_rely(other_id)(s_prime),
        !s.in_flight().contains(msg), s_prime.in_flight().contains(msg),
        cluster.next()(s, s_prime),
    ensures
        resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg) ==> owner_references_is_valid(msg.content.get_create_request().obj, s_prime),
        resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg) ==> owner_references_is_valid(msg.content.get_update_request().obj, s_prime),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    assert(s.api_server.uid_counter <= s_prime.api_server.uid_counter);
    let step = choose |step| cluster.next_step(s, s_prime, step);
    let input = step->ControllerStep_0;
    RabbitmqClusterView::marshal_preserves_integrity();
    RabbitmqReconcileState::marshal_preserves_integrity();
    let cr_dynamic = s.ongoing_reconciles(controller_id)[input.2->0].triggering_cr;
    let cr = RabbitmqClusterView::unmarshal(cr_dynamic).unwrap();
    if resource_create_request_msg(resource_key)(msg) {
        lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
        let owner_refs = msg.content.get_create_request().obj.metadata.owner_references;
        assert(owner_refs == Some(seq![cr.controller_owner_ref()]));
        assert(owner_refs is Some);
        assert(owner_refs->0.len() == 1);
        assert(owner_refs->0[0].uid < s.api_server.uid_counter);
    } else if resource_update_request_msg(resource_key)(msg) {
        lemma_resource_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
        let owner_refs = msg.content.get_update_request().obj.metadata.owner_references;
        assert(owner_refs == Some(seq![cr.controller_owner_ref()]));
        assert(owner_refs is Some);
        assert(owner_refs->0.len() == 1);
        assert(owner_refs->0[0].uid < s.api_server.uid_counter);
    }
}

pub open spec fn every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(
    sub_resource: SubResource, rabbitmq: RabbitmqClusterView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let resource_key = get_request(sub_resource, rabbitmq).key;
        s.resources().contains_key(resource_key)
        ==> owner_references_is_valid(s.resources()[resource_key], s)
    }
}

pub proof fn lemma_always_every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(
    controller_id: int,
    cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(always(lift_state(every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sub_resource, rabbitmq)))),
{
    let inv = every_owner_ref_of_every_object_in_etcd_has_different_uid_from_uid_counter(sub_resource, rabbitmq);
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, rabbitmq)(s)
        &&& no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)(s)
        &&& no_get_then_requests_and_update_resource_status_requests_in_flight(sub_resource, rabbitmq)(s)
    };
    lemma_always_object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(controller_id, cluster, spec, sub_resource, rabbitmq);
    lemma_always_no_create_resource_request_msg_without_name_in_flight(cluster, controller_id, spec, sub_resource, rabbitmq);
    lemma_always_no_get_then_requests_and_update_resource_status_requests_in_flight(controller_id, cluster, spec, sub_resource, rabbitmq);
    combine_spec_entails_always_n!(spec, lift_action(next), lift_action(cluster.next()),
        lift_state(object_in_every_resource_create_or_update_request_msg_only_has_valid_owner_references(sub_resource, rabbitmq)),
        lift_state(no_create_resource_request_msg_without_name_in_flight(sub_resource, rabbitmq)),
        lift_state(no_get_then_requests_and_update_resource_status_requests_in_flight(sub_resource, rabbitmq))
    );
    let resource_key = get_request(sub_resource, rabbitmq).key;
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        if s_prime.resources().contains_key(resource_key) {
            assert(s.api_server.uid_counter <= s_prime.api_server.uid_counter);
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    let msg = input->0;
                    assert(!resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(input->0));
                    if !s.resources().contains_key(resource_key) {
                    } else if s.resources()[resource_key].metadata.owner_references != s_prime.resources()[resource_key].metadata.owner_references {
                        if resource_update_request_msg(resource_key)(msg) {
                        } else if resource_get_then_update_request_msg(resource_key)(msg) {}
                    } else {}
                },
                _ => {}
            }
        }
    }
    init_invariant(spec, cluster.init(), next, inv);
}

}
