// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::generated_name,
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::kubernetes_cluster::proof::api_server::generated_name_reflects_prefix;
use crate::rabbitmq_controller::{
    model::reconciler::*,
    proof::{
        helper_invariants::{predicate::*, proof::*},
        helper_lemmas::lemma_resource_key_has_rmq_prefix,
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


// The owner_references requirement consumed by `Cluster::lemma_eventually_objects_owner_references_satisfies`:
// the only valid owner_references for our sub-resource is `[rabbitmq.controller_owner_ref()]`.
pub open spec fn owner_ref_is_current_cr_only(rabbitmq: RabbitmqClusterView) -> spec_fn(Option<Seq<OwnerReferenceView>>) -> bool {
    |o: Option<Seq<OwnerReferenceView>>| o == Some(seq![rabbitmq.controller_owner_ref()])
}

// Forall version that gives both `every_create_msg_sets_owner_references_as` and
// `every_create_msg_with_generate_name_matching_key_set_owner_references_as` for every sub_resource.
pub proof fn lemma_eventually_always_create_msg_owner_refs_satisfies_for_sub_resource_forall(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
        spec.entails(always(lift_state(rmq_guarantee(controller_id)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures
        spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource|
            lift_state(Cluster::every_create_msg_sets_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq))))))),
        spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource|
            lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq))))))),
{
    assert forall |sub_resource: SubResource|
        spec.entails(true_pred().leads_to(always(lift_state(#[trigger]
            Cluster::every_create_msg_sets_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq))))))
        && spec.entails(true_pred().leads_to(always(lift_state(#[trigger]
            Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq)))))) by {
        lemma_eventually_always_create_msg_owner_refs_satisfies_for_sub_resource(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(),
        |sub_resource: SubResource| lift_state(Cluster::every_create_msg_sets_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq))));
    leads_to_always_tla_forall_subresource(spec, true_pred(),
        |sub_resource: SubResource| lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq))));
}

// Per sub_resource: produces both posts in one shot.
#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_create_msg_owner_refs_satisfies_for_sub_resource(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
        spec.entails(always(lift_state(rmq_guarantee(controller_id)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(Cluster::every_create_msg_sets_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq)))))),
        spec.entails(true_pred().leads_to(always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq)))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let owner_ref_req = owner_ref_is_current_cr_only(rabbitmq);
    let requirements = |msg: Message, s: ClusterState| {
        (resource_create_request_msg(resource_key)(msg)
            ==> owner_ref_req(msg.content.get_create_request().obj.metadata.owner_references))
        && (resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg)
            ==> generated_name(s.api_server, msg.content.get_create_request().obj.metadata.generate_name->0) != resource_key.name)
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)(s)
        &&& Cluster::desired_state_is(rabbitmq)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::no_pending_request_to_api_server_from_non_controllers()(s_prime)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s_prime)
        &&& rmq_guarantee(controller_id)(s_prime)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
    };

    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
        implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message|
            (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
            && msg.dst is APIServer && msg.content is APIRequest
            implies requirements(msg, s_prime) by {
            // Branch (a): a fully-named create targeting our resource_key.
            if resource_create_request_msg(resource_key)(msg) {
                if !s.in_flight().contains(msg) {
                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    RabbitmqReconcileState::marshal_preserves_integrity();
                    RabbitmqClusterView::marshal_preserves_integrity();
                    lemma_resource_create_request_msg_implies_key_in_reconcile_equals(
                        controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                    let cr_dyn = s.ongoing_reconciles(controller_id)[key].triggering_cr;
                    let cr = RabbitmqClusterView::unmarshal(cr_dyn).unwrap();
                    // by `the_object_in_reconcile_has_spec_and_uid_as`: triggering_cr.metadata
                    // matches rabbitmq's name+namespace+uid. Hence controller_owner_ref matches.
                    assert(cr.controller_owner_ref() == rabbitmq.controller_owner_ref());
                    assert(msg.content.get_create_request().obj.metadata.owner_references
                        == Some(seq![rabbitmq.controller_owner_ref()]));
                } else {
                    // msg already in s -> use IH on s
                    assert(requirements(msg, s));
                }
            }
            // Branch (b): a generate-named create that could resolve to our resource_key.
            if resource_create_request_msg_without_name(resource_key.kind, resource_key.namespace)(msg) {
                // msg.dst is APIServer, msg.content is APIRequest (== CreateRequest), so
                // the source must be Controller or BuiltinController. BuiltinController only
                // issues delete requests. So the source is Controller.
                match msg.src {
                    HostId::Controller(id, _) => {
                        if id == controller_id {
                            // Our controller never issues create-without-name (rmq_guarantee says name is Some).
                            assert(rmq_guarantee_create_req(msg.content.get_create_request()));
                            assert(false);
                        } else {
                            // Other controller's create-without-name has no rmq prefix in generate_name
                            // (rmq_rely). resource_key.name has rmq prefix. So generated_name != resource_key.name.
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(rmq_rely(id)(s_prime));
                            assert(rmq_rely_create_req(msg.content.get_create_request()));
                            lemma_resource_key_has_rmq_prefix(sub_resource, rabbitmq);
                            generated_name_reflects_prefix(s_prime.api_server,
                                msg.content.get_create_request().obj.metadata.generate_name->0,
                                RabbitmqClusterView::kind()->CustomResourceKind_0);
                        }
                    },
                    _ => {
                        // Excluded by `no_pending_request_to_api_server_from_non_controllers`
                        // (non-controller, non-builtin sources can't target APIServer with APIRequest)
                        // and `all_requests_from_builtin_controllers_are_api_delete_requests`
                        // (builtin -> only delete).
                        assert(false);
                    },
                }
            }
        }
    };

    always_to_always_later(spec, lift_state(rmq_guarantee(controller_id)));
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    always_to_always_later(spec, lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()));
    always_to_always_later(spec, lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()));
    invariant_n!(spec,
        lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        later(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())),
        later(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        later(lift_state(rmq_guarantee(controller_id))),
        later(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );
    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    // Derive `every_create_msg_sets_owner_references_as` from `every_in_flight_req_msg_satisfies`.
    assert_by(
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)))
            .implies(always(lift_state(Cluster::every_create_msg_sets_owner_references_as(resource_key, owner_ref_req))))),
        {
            assert forall |ex: Execution<ClusterState>|
                #[trigger] always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))).satisfied_by(ex)
                implies always(lift_state(Cluster::every_create_msg_sets_owner_references_as(resource_key, owner_ref_req))).satisfied_by(ex) by {
                assert forall |i: nat| #[trigger] lift_state(Cluster::every_create_msg_sets_owner_references_as(resource_key, owner_ref_req)).satisfied_by(ex.suffix(i)) by {
                    assert(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)).satisfied_by(ex.suffix(i)));
                };
            };
        }
    );
    leads_to_weaken(spec, true_pred(), always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))),
        true_pred(), always(lift_state(Cluster::every_create_msg_sets_owner_references_as(resource_key, owner_ref_req))));

    // Derive `every_create_msg_with_generate_name_matching_key_set_owner_references_as` similarly.
    assert_by(
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)))
            .implies(always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(resource_key, owner_ref_req))))),
        {
            assert forall |ex: Execution<ClusterState>|
                #[trigger] always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))).satisfied_by(ex)
                implies always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(resource_key, owner_ref_req))).satisfied_by(ex) by {
                assert forall |i: nat| #[trigger] lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(resource_key, owner_ref_req)).satisfied_by(ex.suffix(i)) by {
                    assert(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)).satisfied_by(ex.suffix(i)));
                };
            };
        }
    );
    leads_to_weaken(spec, true_pred(), always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))),
        true_pred(), always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(resource_key, owner_ref_req))));
}

}
