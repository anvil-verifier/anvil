// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, 
    cluster::*,
    controller::types::*,
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
    proof::{predicate::*, helper_lemmas, helper_invariants::{predicate::*}, liveness::api_actions::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*};
use vstd::{map::*, map_lib::*, multiset::*, prelude::*, seq_lib::*};

verus!{

pub proof fn lemma_eventually_always_every_create_request_is_well_formed(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_create_request_is_well_formed(cluster, controller_id))))),
{
    let requirements = |msg: Message, s: ClusterState| {
        &&& msg.src.is_Controller()
        &&& msg.src.get_Controller_0() == controller_id
        &&& msg.dst.is_APIServer()
        &&& msg.content.is_APIRequest()
        &&& msg.content.is_create_request()
    } ==> {
        let content = msg.content;
        let req = content.get_create_request();
        let obj = req.obj;
        let created_obj = DynamicObjectView {
            kind: req.obj.kind,
            metadata: ObjectMetaView {
                // Set name for new object if name is not provided, here we generate
                // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
                name: if req.obj.metadata.name.is_Some() {
                    req.obj.metadata.name
                } else {
                    Some(generate_name(s.api_server))
                },
                namespace: Some(req.namespace), // Set namespace for new object
                resource_version: Some(s.api_server.resource_version_counter), // Set rv for new object
                uid: Some(s.api_server.uid_counter), // Set uid for new object
                deletion_timestamp: None, // Unset deletion timestamp for new object
                ..req.obj.metadata
            },
            spec: req.obj.spec,
            status: marshalled_default_status(req.obj.kind, cluster.installed_types), // Overwrite the status with the default one
        };
        &&& obj.metadata.name.is_None()
        &&& obj.metadata.deletion_timestamp.is_None()
        &&& created_obj.metadata.namespace.is_Some()
        &&& content.get_create_request().namespace == created_obj.metadata.namespace.unwrap()
        &&& unmarshallable_object(obj, cluster.installed_types)
        &&& created_object_validity_check(created_obj, cluster.installed_types).is_none()
        &&& PodView::unmarshal(created_obj).is_ok()
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        &&& msg.src.is_Controller()
        &&& msg.src.get_Controller_0() == controller_id
        &&& msg.dst.is_APIServer()
        &&& msg.content.is_APIRequest()
        &&& msg.content.is_create_request()
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s_prime)
    };
    
    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if requirements_antecedent(msg, s) {
                if s.in_flight().contains(msg) {
                    assert(requirements(msg, s));
                    assert(requirements(msg, s_prime));
                } else {
                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    match step {
                        Step::ControllerStep((id, _, cr_key)) => {
                            PodView::marshal_preserves_integrity();
                            VReplicaSetReconcileState::marshal_preserves_integrity();
                            if id != controller_id {
                                assert(vrs_not_interfered_by(controller_id, id)(s_prime));
                            }
                        },
                        _ => {
                            assert(requirements(msg, s_prime));
                        }
                    }
                }
            }
        }
    }

    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lifted_vrs_non_interference_property_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_no_pending_update_or_update_status_request_on_pods(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_pending_update_or_update_status_request_on_pods())))),
{
    let requirements = |msg: Message, s: ClusterState| {
        &&& msg.content.is_update_request() ==> msg.content.get_update_request().key().kind != PodView::kind()
        &&& msg.content.is_update_status_request() ==> msg.content.get_update_status_request().key().kind != PodView::kind()
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s_prime)
    };
    
    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.in_flight().contains(msg) {
                assert(requirements(msg, s));
                assert(requirements(msg, s_prime));
            } else {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep((id, _, _)) => {
                        VReplicaSetReconcileState::marshal_preserves_integrity();
                        if id != controller_id {
                            assert(vrs_not_interfered_by(controller_id, id)(s_prime));
                        }
                    },
                    _ => {
                        assert(requirements(msg, s_prime));
                    }
                }
            }
        }
    }

    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_non_interference_property_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_garbage_collector_does_not_delete_vrs_pods(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(no_pending_update_or_update_status_request_on_pods()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(garbage_collector_does_not_delete_vrs_pods(vrs))))),
{
    let requirements = |msg: Message, s: ClusterState| {
        ({
            &&& msg.src.is_BuiltinController()
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        })
        ==>
        ({
            let req = msg.content.get_delete_request(); 
            &&& msg.content.is_delete_request()
            &&& req.preconditions.is_Some()
            &&& req.preconditions.unwrap().uid.is_Some()
            &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
            &&& s.resources().contains_key(req.key)
                    ==> (!matching_pod_entries(vrs, s.resources()).contains_key(req.key)
                          || s.resources()[req.key].metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap())
        })
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        &&& msg.src.is_BuiltinController()
        &&& msg.dst.is_APIServer()
        &&& msg.content.is_APIRequest()
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s)
        &&& no_pending_update_or_update_status_request_on_pods()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s_prime)
    };

    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::BuiltinControllersStep(..) => {
                    if (!s.in_flight().contains(msg) && requirements_antecedent(msg, s_prime)) {
                        let key = msg.content.get_delete_request().key;
                        let obj = s.resources()[key];
                        let owner_references = obj.metadata.owner_references.get_Some_0();
                        assert(forall |i| #![trigger owner_references[i]] 0 <= i < owner_references.len() ==> {
                            // the referred owner object does not exist in the cluster state
                            ||| !s.resources().contains_key(owner_reference_to_object_reference(owner_references[i], key.namespace))
                            // or it exists but has a different uid
                            // (which means the actual owner was deleted and another object with the same name gets created again)
                            ||| s.resources()[owner_reference_to_object_reference(owner_references[i], key.namespace)].metadata.uid != Some(owner_references[i].uid)
                        });
                        if (matching_pod_entries(vrs, s.resources()).contains_key(key)) {
                            assert(obj.metadata.owner_references_contains(vrs.controller_owner_ref()));
                            let idx = choose |i| 0 <= i < owner_references.len() && owner_references[i] == vrs.controller_owner_ref();
                            assert(s.resources().contains_key(vrs.object_ref()));
                        }
                    }
                },
                _ => {}
            }
        }
    }
    
    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vrs)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lifted_vrs_non_interference_property_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_no_pending_create_or_delete_request_not_from_controller_on_pods(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_pending_create_or_delete_request_not_from_controller_on_pods())))),
{
    let requirements = |msg: Message, s: ClusterState| {
        ({
            &&& !(msg.src.is_Controller() || msg.src.is_BuiltinController())
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        })
        ==>
        ({
            &&& msg.content.is_create_request() ==> msg.content.get_create_request().key().kind != PodView::kind()
            &&& msg.content.is_delete_request() ==> msg.content.get_delete_request().key.kind != PodView::kind()
        })
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s_prime)
    };
    
    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vrs_non_interference_property_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_every_create_matching_pod_request_implies_at_after_create_pod_step(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id))))),
{
    let key = vrs.object_ref();
    let requirements = |msg: Message, s: ClusterState| {
        ({
            let content = msg.content;
            let req = content.get_create_request();
            let created_obj = DynamicObjectView {
                kind: req.obj.kind,
                metadata: ObjectMetaView {
                    // Set name for new object if name is not provided, here we generate
                    // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
                    name: if req.obj.metadata.name.is_Some() {
                        req.obj.metadata.name
                    } else {
                        Some(generate_name(s.api_server))
                    },
                    namespace: Some(req.namespace), // Set namespace for new object
                    resource_version: Some(s.api_server.resource_version_counter), // Set rv for new object
                    uid: Some(s.api_server.uid_counter), // Set uid for new object
                    deletion_timestamp: None, // Unset deletion timestamp for new object
                    ..req.obj.metadata
                },
                spec: req.obj.spec,
                status: marshalled_default_status(req.obj.kind, cluster.installed_types), // Overwrite the status with the default one
            };
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
            &&& content.is_create_request()
            &&& owned_selector_match_is(vrs, created_obj)
        } ==> {
            &&& exists |diff: nat| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(diff))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        })
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        let content = msg.content;
        let req = content.get_create_request();
        let created_obj = DynamicObjectView {
            kind: req.obj.kind,
            metadata: ObjectMetaView {
                // Set name for new object if name is not provided, here we generate
                // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
                name: if req.obj.metadata.name.is_Some() {
                    req.obj.metadata.name
                } else {
                    Some(generate_name(s.api_server))
                },
                namespace: Some(req.namespace), // Set namespace for new object
                resource_version: Some(s.api_server.resource_version_counter), // Set rv for new object
                uid: Some(s.api_server.uid_counter), // Set uid for new object
                deletion_timestamp: None, // Unset deletion timestamp for new object
                ..req.obj.metadata
            },
            spec: req.obj.spec,
            status: marshalled_default_status(req.obj.kind, cluster.installed_types), // Overwrite the status with the default one
        };
        &&& msg.src.is_Controller()
        &&& msg.src.get_Controller_0() == controller_id
        &&& msg.dst.is_APIServer()
        &&& msg.content.is_APIRequest()
        &&& content.is_create_request()
        &&& owned_selector_match_is(vrs, created_obj)
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s_prime)
    };
    
    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            VReplicaSetReconcileState::marshal_preserves_integrity();
            if requirements_antecedent(msg, s) {
                if s.in_flight().contains(msg) {
                    assert(requirements(msg, s));

                    let diff = choose |diff: nat| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(diff))(s);
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(diff))(s_prime)
                        || at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod((diff - 1) as nat))(s_prime));

                    assert(requirements(msg, s_prime));
                } else {
                    let content = msg.content;
                    let req = content.get_create_request();
                    let request_key = content.get_create_request().key();
                    let obj = content.get_create_request().obj;
                    let created_obj = DynamicObjectView {
                        kind: req.obj.kind,
                        metadata: ObjectMetaView {
                            // Set name for new object if name is not provided, here we generate
                            // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
                            name: if req.obj.metadata.name.is_Some() {
                                req.obj.metadata.name
                            } else {
                                Some(generate_name(s.api_server))
                            },
                            namespace: Some(req.namespace), // Set namespace for new object
                            resource_version: Some(s.api_server.resource_version_counter), // Set rv for new object
                            uid: Some(s.api_server.uid_counter), // Set uid for new object
                            deletion_timestamp: None, // Unset deletion timestamp for new object
                            ..req.obj.metadata
                        },
                        spec: req.obj.spec,
                        status: marshalled_default_status(req.obj.kind, cluster.installed_types), // Overwrite the status with the default one
                    };

                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    let cr_key = step.get_ControllerStep_0().2.get_Some_0();
                    let local_step = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let local_step_prime = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let new_diff = local_step_prime.get_AfterCreatePod_0();
                    let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();

                    assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));

                    let controller_owners = created_obj.metadata.owner_references.unwrap();
                    assert(controller_owners.len() == 1);
                    assert(controller_owners.contains(
                        triggering_cr.controller_owner_ref()
                    ));
                    assert(controller_owners.contains(vrs.controller_owner_ref()));
                    assert(triggering_cr.object_ref() == cr_key);

                    assert(cr_key.name == key.name);
                    assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(new_diff))(s_prime));
                    assert(requirements(msg, s_prime));
                }
            }
        }
    }

    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vrs)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lifted_vrs_non_interference_property_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_every_delete_matching_pod_request_implies_at_after_delete_pod_step(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<VReplicaSetView>(controller_id, vrs)))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))),
        spec.entails(always(lift_state(no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)))),
        spec.entails(always(lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),

    ensures spec.entails(true_pred().leads_to(always(lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))))),
{
    let key = vrs.object_ref();
    let requirements = |msg: Message, s: ClusterState| {
        ({
            let content = msg.content;
            let req = content.get_delete_request();
            let key = content.get_delete_request().key;
            let req_rv = req.preconditions.unwrap().resource_version.unwrap();
            let obj = s.resources()[key];
            &&& content.is_delete_request()
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
            &&& msg.dst.is_APIServer()
            &&& s.resources().contains_key(key)
            &&& owned_selector_match_is(vrs, obj)

            // Delete precondition clauses.
            &&& req.preconditions.is_Some()
            &&& req.preconditions.unwrap().resource_version.is_Some()
            &&& req.preconditions.unwrap().uid.is_None()
            &&& obj.metadata.resource_version.is_Some()
            &&& obj.metadata.resource_version.unwrap() == req_rv
        } ==> {
            let content = msg.content;
            let req = content.get_delete_request();
            let req_rv = req.preconditions.unwrap().resource_version.unwrap();
            let key = req.key;
            let obj = s.resources()[key];
            &&& exists |diff: nat| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        })
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        let content = msg.content;
        let req = content.get_delete_request();
        let key = content.get_delete_request().key;
        let req_rv = req.preconditions.unwrap().resource_version.unwrap();
        let obj = s.resources()[key];
        &&& content.is_delete_request()
        &&& msg.src.is_Controller()
        &&& msg.src.get_Controller_0() == controller_id
        &&& msg.dst.is_APIServer()
        &&& s.resources().contains_key(key)
        &&& owned_selector_match_is(vrs, obj)

        // Delete precondition clauses.
        &&& req.preconditions.is_Some()
        &&& req.preconditions.unwrap().resource_version.is_Some()
        &&& req.preconditions.unwrap().uid.is_None()
        &&& obj.metadata.resource_version.is_Some()
        &&& obj.metadata.resource_version.unwrap() == req_rv
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as::<VReplicaSetView>(controller_id, vrs)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s_prime)
        &&& no_pending_update_or_update_status_request_on_pods()(s)
        &&& every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
        &&& each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)(s)
        &&& vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
    };
    
    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            VReplicaSetReconcileState::marshal_preserves_integrity();
            VReplicaSetView::marshal_preserves_integrity();
            if requirements_antecedent(msg, s) {
                if s.in_flight().contains(msg) {
                    assert(requirements(msg, s));

                    let diff = choose |diff: nat| #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s);
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                        || at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod((diff + 1) as nat))(s_prime));

                    assert(requirements(msg, s_prime));
                } else {
                    let content = msg.content;
                    let request_key = content.get_delete_request().key;
                    let obj = s.resources()[content.get_delete_request().key];

                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    let cr_key = step.get_ControllerStep_0().2.get_Some_0();
                    let local_step = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let local_step_prime = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let new_diff = local_step_prime.get_AfterDeletePod_0();

                    let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();

                    if local_step.is_AfterListPods() {
                        let cr_msg = step.get_ControllerStep_0().1.get_Some_0();
                        let req_msg = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg.get_Some_0();
                        let objs = cr_msg.content.get_list_response().res.unwrap();
                        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                        let desired_replicas: nat = triggering_cr.spec.replicas.unwrap_or(0) as nat;
                        let pods_or_none = objects_to_pods(objs);
                        let pods = pods_or_none.unwrap();
                        let filtered_pods = filter_pods(pods, triggering_cr);
                        let diff = filtered_pods.len() - desired_replicas;

                        // show filtered_pods[diff - 1] has the desired property.
                        seq_filter_contains_implies_seq_contains(
                            pods,
                            |pod: PodView|
                            pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                            && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                            && pod.metadata.deletion_timestamp.is_None(),
                            filtered_pods[diff - 1]
                        );
                        if diff - 1 >= 0 {
                            assert(filtered_pods[diff - 1].metadata.owner_references_contains(triggering_cr.controller_owner_ref()));
                        }

                        // Show that pods[idx1] and filtered_pods[diff - 1] have the same metadata.
                        let idx1 = choose |i| 0 <= i < pods.len() && pods[i] == filtered_pods[diff - 1];
                        assert(pods[idx1].metadata == filtered_pods[diff - 1].metadata);

                        // Show that pods[idx1] and objs[idx1] have the same metadata.
                        let unwrap_obj = |o: DynamicObjectView| PodView::unmarshal(o).unwrap();
                        assert(pods == objs.map_values(unwrap_obj));
                        assert(objs.contains(objs[idx1]));
                        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                            objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err()
                        );
                        assert(PodView::unmarshal(objs[idx1]).is_ok());
                        assert(objs[idx1].metadata == pods[idx1].metadata);

                        // Show that objs[idx1] and obj (in etcd) have the same metadata.
                        if s.resources().contains_key(objs[idx1].object_ref()) 
                            && s.resources()[objs[idx1].object_ref()].metadata.resource_version == objs[idx1].metadata.resource_version {
                            assert(objs[idx1].metadata == obj.metadata);
                        }
                    }

                    let controller_owners = obj.metadata.owner_references.unwrap().filter(
                        |o: OwnerReferenceView| o.controller.is_Some() && o.controller.get_Some_0()
                    );
                    assert(controller_owners.contains(
                        VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr)
                            .unwrap().controller_owner_ref()
                    ));
                    assert(controller_owners.contains(vrs.controller_owner_ref()));
                    assert(cr_key.name == key.name);
                    assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(new_diff))(s_prime));
                    assert(requirements(msg, s_prime));
                }
            } else {
                if s.in_flight().contains(msg) {
                    assert(!requirements_antecedent(msg, s));
                    let content = msg.content;
                    let req = content.get_delete_request();
                    let key = req.key;
                    let obj = s.resources()[key];

                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    match step {
                        Step::APIServerStep(input) => {
                            // Invariant every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter
                            // is essential here.
                        },
                        _ => {}
                    }
                }
            }
        }
    }

    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vrs)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<VReplicaSetView>(controller_id, vrs)),
        lifted_vrs_non_interference_property_action(cluster, controller_id),
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lift_state(every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)),
        lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id))
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)))),
        spec.entails(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        spec.entails(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)))),
        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(tla_forall(|vrs: VReplicaSetView| true_pred().leads_to(lift_state(|s: ClusterState| !(s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))),
        spec.entails(always(lift_state(no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(every_create_request_is_well_formed(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id))))),
{
    let requirements = |key: ObjectRef, s: ClusterState| {
        let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
        let filtered_pods = state.filtered_pods.unwrap();
        &&& triggering_cr.object_ref() == key
        &&& triggering_cr.metadata().well_formed()
        &&& state.filtered_pods.is_Some() ==>
        // Maintained across deletes, 
        // maintained across creates since all new keys with generate_name
        // are unique, maintained across updates since there are
        // no updates.
            forall |i| #![auto] 0 <= i < filtered_pods.len() ==>
            (
                filtered_pods[i].object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                && ((s.resources().contains_key(filtered_pods[i].object_ref())
                    && s.resources()[filtered_pods[i].object_ref()].metadata.resource_version
                        == filtered_pods[i].metadata.resource_version) ==>
                    (s.resources()[filtered_pods[i].object_ref()].metadata.owner_references_contains(
                        triggering_cr.controller_owner_ref()
                        )
                        ))
                && filtered_pods[i].metadata.resource_version.is_some()
                && filtered_pods[i].metadata.resource_version.unwrap()
                    < s.api_server.resource_version_counter
            )
        &&& state.reconcile_step.is_AfterListPods() ==> {
            let req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
            &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
            &&& req_msg.dst.is_APIServer()
            &&& req_msg.content.is_list_request()
            &&& req_msg.content.get_list_request() == ListRequest {
                kind: PodView::kind(),
                namespace: triggering_cr.metadata.namespace.unwrap(),
            }
            &&& forall |msg| {
                let req_msg = s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                &&& #[trigger] s.in_flight().contains(msg)
                &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                &&& msg.src.is_APIServer()
                &&& resp_msg_matches_req_msg(msg, req_msg)
            } ==> {
                let resp_objs = msg.content.get_list_response().res.unwrap();
                &&& msg.content.is_list_response()
                &&& msg.content.get_list_response().res.is_Ok()
                &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                &&& forall |i| #![auto] 0 <= i < resp_objs.len() ==>
                (
                    resp_objs[i].metadata.namespace.is_some()
                    && resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                    && ((s.resources().contains_key(resp_objs[i].object_ref())
                            && s.resources()[resp_objs[i].object_ref()].metadata.resource_version
                            == resp_objs[i].metadata.resource_version) ==> 
                            s.resources()[resp_objs[i].object_ref()].metadata
                                == resp_objs[i].metadata)
                    && resp_objs[i].metadata.resource_version.is_some()
                    && resp_objs[i].metadata.resource_version.unwrap()
                            < s.api_server.resource_version_counter
                )
            }
        }
    };

    // Technical side-condition: prove two forms of termination property are equivalent
    helper_lemmas::termination_property_for_all_vrs_is_equivalent_to_termination_property_for_all_keys(controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)(s)
        &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as::<VReplicaSetView>(controller_id, vrs)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s_prime)
        &&& no_pending_update_or_update_status_request_on_pods()(s)
        &&& every_create_request_is_well_formed(cluster, controller_id)(s)
    };
    
    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) ==> Cluster::every_new_ongoing_reconcile_satisfies(controller_id, requirements)(s, s_prime) by {
        assert forall |key: ObjectRef| (!s.ongoing_reconciles(controller_id).contains_key(key) || requirements(key, s)) 
        && #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key) && stronger_next(s, s_prime) implies requirements(key, s_prime) by {
            VReplicaSetReconcileState::marshal_preserves_integrity();
            VReplicaSetView::marshal_preserves_integrity();
            if s.ongoing_reconciles(controller_id).contains_key(key) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep((id, _, cr_key_opt)) => {
                        let cr_key = cr_key_opt.get_Some_0();
                        if id == controller_id && cr_key == key {
                            let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();

                            let reconcile_step = state.reconcile_step;
                            if reconcile_step.is_AfterListPods() {
                                let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                                let cr_msg = step.get_ControllerStep_0().1.get_Some_0();
                                let req_msg = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg.get_Some_0();
                                let objs = cr_msg.content.get_list_response().res.unwrap();
                                let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                                let pods_or_none = objects_to_pods(objs);
                                let pods = pods_or_none.unwrap();
                                let filtered_pods = filter_pods(pods, triggering_cr);

                                assert forall |i| #![auto] 
                                    0 <= i < filtered_pods.len()
                                    && requirements(key, s)
                                    && stronger_next(s, s_prime)
                                    implies
                                    (filtered_pods[i].object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                                    && ((s_prime.resources().contains_key(filtered_pods[i].object_ref())
                                        && s_prime.resources()[filtered_pods[i].object_ref()].metadata.resource_version
                                            == filtered_pods[i].metadata.resource_version) ==>
                                        (s_prime.resources()[filtered_pods[i].object_ref()].metadata.owner_references_contains(
                                            triggering_cr.controller_owner_ref()
                                            )
                                            ))
                                    && filtered_pods[i].metadata.resource_version.is_some()
                                    && filtered_pods[i].metadata.resource_version.unwrap()
                                        < s_prime.api_server.resource_version_counter) by {

                                    assert({
                                        let req_msg = s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                                        &&& s.in_flight().contains(cr_msg)
                                        &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                                        &&& cr_msg.src.is_APIServer()
                                        &&& resp_msg_matches_req_msg(cr_msg, req_msg)});
                                    
                                    seq_filter_contains_implies_seq_contains(
                                        pods,
                                        |pod: PodView|
                                        pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                                        && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                        && pod.metadata.deletion_timestamp.is_None(),
                                        filtered_pods[i]
                                    );

                                    // Show that pods[idx1] and filtered_pods[i] have the same metadata.
                                    let idx1 = choose |j| 0 <= j < pods.len() && pods[j] == filtered_pods[i];
                                    assert(pods[idx1].metadata == filtered_pods[i].metadata);

                                    assert(objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 );
                                    assert(objs.len() == pods.len());

                                    // Show that pods[idx1] and objs[idx1] have the same metadata.
                                    seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                        objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err()
                                    );
                                    assert(objs.contains(objs[idx1]));
                                    assert(PodView::unmarshal(objs[idx1]).is_ok());

                                    let unwrap_obj = |o: DynamicObjectView| PodView::unmarshal(o).unwrap();
                                    assert(pods == objs.map_values(unwrap_obj));
                                    assert(objs.contains(objs[idx1]));
                                    assert(objs[idx1].metadata == pods[idx1].metadata);
                                }
                            }

                            // prove that the newly sent message has no response.
                            if s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some() {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                                assert(forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id);
                                assert(s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg));
                                assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) 
                                    && (forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id)
                                    && s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg)
                                    && msg != req_msg 
                                    implies msg.rpc_id != req_msg.rpc_id by {
                                    if !s.in_flight().contains(msg) {} // need this to invoke trigger.
                                }
                            }

                        } else {
                            let new_msgs = s_prime.in_flight().sub(s.in_flight());

                            let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                            let triggering_cr = VReplicaSetView::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                            let filtered_pods = state.filtered_pods.unwrap();
                            if state.reconcile_step.is_AfterListPods() {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                                assert forall |msg| {
                                    let req_msg = s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                                    &&& #[trigger] s_prime.in_flight().contains(msg)
                                    &&& s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                                    &&& msg.src.is_APIServer()
                                    &&& resp_msg_matches_req_msg(msg, req_msg)
                                    &&& requirements(key, s)
                                    &&& stronger_next(s, s_prime)
                                } implies {
                                    let resp_objs = msg.content.get_list_response().res.unwrap();
                                    &&& msg.content.is_list_response()
                                    &&& msg.content.get_list_response().res.is_Ok()
                                    &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                                    &&& forall |i| #![auto] 0 <= i < resp_objs.len() ==>
                                    (
                                        resp_objs[i].metadata.namespace.is_some()
                                        && resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                                        && ((s_prime.resources().contains_key(resp_objs[i].object_ref())
                                                && s_prime.resources()[resp_objs[i].object_ref()].metadata.resource_version
                                                == resp_objs[i].metadata.resource_version) ==> 
                                                s_prime.resources()[resp_objs[i].object_ref()].metadata
                                                    == resp_objs[i].metadata)
                                        && resp_objs[i].metadata.resource_version.is_some()
                                        && resp_objs[i].metadata.resource_version.unwrap()
                                                < s_prime.api_server.resource_version_counter
                                    )
                                } by {
                                    assert(forall |msg| #[trigger] new_msgs.contains(msg) ==> !(#[trigger] msg.src.is_APIServer()));
                                    if !new_msgs.contains(msg) {
                                        assert(s.in_flight().contains(msg));
                                    }
                                }
                            }
                        }

                    },
                    Step::APIServerStep(req_msg_opt) => {
                        let current_req_msg = req_msg_opt.unwrap();
                        let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());
                        if state.reconcile_step.is_AfterListPods() {
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                            let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                            assert forall |msg| {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                                &&& #[trigger] s_prime.in_flight().contains(msg)
                                &&& s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                                &&& msg.src.is_APIServer()
                                &&& resp_msg_matches_req_msg(msg, req_msg)
                                &&& requirements(key, s)
                                &&& stronger_next(s, s_prime)
                            } implies {
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                &&& msg.content.is_list_response()
                                &&& msg.content.get_list_response().res.is_Ok()
                                &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                                &&& forall |i| #![auto] 0 <= i < resp_objs.len() ==>
                                (
                                    resp_objs[i].metadata.namespace.is_some()
                                    && resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                                    && ((s_prime.resources().contains_key(resp_objs[i].object_ref())
                                            && s_prime.resources()[resp_objs[i].object_ref()].metadata.resource_version
                                            == resp_objs[i].metadata.resource_version) ==> 
                                            s_prime.resources()[resp_objs[i].object_ref()].metadata
                                                == resp_objs[i].metadata)
                                    && resp_objs[i].metadata.resource_version.is_some()
                                    && resp_objs[i].metadata.resource_version.unwrap()
                                            < s_prime.api_server.resource_version_counter
                                )
                            } by {
                                if (new_msgs.contains(msg)) {
                                    if current_req_msg == req_msg {
                                        let resp_objs = msg.content.get_list_response().res.unwrap();
                                        
                                        assert forall |o: DynamicObjectView| #![auto]
                                        requirements(key, s)
                                        && stronger_next(s, s_prime)
                                        && resp_objs.contains(o)
                                        implies !PodView::unmarshal(o).is_err() by {
                                            // Tricky reasoning about .to_seq
                                            let selector = |o: DynamicObjectView| {
                                                &&& o.object_ref().namespace == req_msg.content.get_list_request().namespace
                                                &&& o.object_ref().kind == req_msg.content.get_list_request().kind
                                            };
                                            let selected_elements = s.resources().values().filter(selector);
                                            lemma_values_finite(s.resources());
                                            finite_set_to_seq_contains_all_set_elements(selected_elements);
                                            assert(resp_objs =~= selected_elements.to_seq());
                                            assert(selected_elements.contains(o));
                                        }
                                        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                            resp_objs, 
                                            |o: DynamicObjectView| PodView::unmarshal(o).is_err()
                                        );

                                        assert forall |i| #![auto] { 
                                            0 <= i < resp_objs.len()
                                            && requirements(key, s)
                                            && stronger_next(s, s_prime)
                                        } implies {
                                            resp_objs[i].metadata.namespace.is_some()
                                            && resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                                            && ((s_prime.resources().contains_key(resp_objs[i].object_ref())
                                                    && s_prime.resources()[resp_objs[i].object_ref()].metadata.resource_version
                                                    == resp_objs[i].metadata.resource_version) ==> 
                                                    s_prime.resources()[resp_objs[i].object_ref()].metadata
                                                        == resp_objs[i].metadata)
                                            && resp_objs[i].metadata.resource_version.is_some()
                                            && resp_objs[i].metadata.resource_version.unwrap()
                                                    < s_prime.api_server.resource_version_counter
                                        } by {
                                            // Tricky reasoning about .to_seq
                                            let selector = |o: DynamicObjectView| {
                                                &&& o.object_ref().namespace == req_msg.content.get_list_request().namespace
                                                &&& o.object_ref().kind == req_msg.content.get_list_request().kind
                                            };
                                            let selected_elements = s.resources().values().filter(selector);
                                            lemma_values_finite(s.resources());
                                            finite_set_to_seq_contains_all_set_elements(selected_elements);
                                            assert(resp_objs =~= selected_elements.to_seq());
                                            assert(selected_elements.to_seq().contains(resp_objs[i]));
                                            assert(selected_elements.contains(resp_objs[i]));
                                        }
                                    } else {
                                        assert(s.in_flight().contains(current_req_msg));
                                        assert(current_req_msg.rpc_id != req_msg.rpc_id);
                                    }
                                } else {
                                    let msg_antecedent = {
                                        &&& s.in_flight().contains(msg)
                                        &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                                        &&& msg.src.is_APIServer()
                                        &&& resp_msg_matches_req_msg(msg, req_msg)
                                    };
                                    if msg_antecedent {
                                        let resp_objs = msg.content.get_list_response().res.unwrap();
                                        assert({
                                            &&& msg.content.is_list_response()
                                            &&& msg.content.get_list_response().res.is_Ok()
                                            &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                                        });
                                        assert(forall |i| #![auto] 0 <= i < resp_objs.len() ==>
                                            (
                                                resp_objs[i].metadata.namespace.is_some()
                                                && resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                                                && ((s_prime.resources().contains_key(resp_objs[i].object_ref())
                                                        && s_prime.resources()[resp_objs[i].object_ref()].metadata.resource_version
                                                        == resp_objs[i].metadata.resource_version) ==> 
                                                        s_prime.resources()[resp_objs[i].object_ref()].metadata
                                                            == resp_objs[i].metadata)
                                                && resp_objs[i].metadata.resource_version.is_some()
                                                && resp_objs[i].metadata.resource_version.unwrap()
                                                        < s_prime.api_server.resource_version_counter
                                            ));
                                    }
                                }
                            }
                        }
                    },
                    Step::BuiltinControllersStep(..) => {
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());

                        let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                        let triggering_cr = VReplicaSetView::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                        let filtered_pods = state.filtered_pods.unwrap();
                        if state.reconcile_step.is_AfterListPods() {
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                            assert forall |msg| {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                                &&& #[trigger] s_prime.in_flight().contains(msg)
                                &&& s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                                &&& msg.src.is_APIServer()
                                &&& resp_msg_matches_req_msg(msg, req_msg)
                                &&& requirements(key, s)
                                &&& stronger_next(s, s_prime)
                            } implies {
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                &&& msg.content.is_list_response()
                                &&& msg.content.get_list_response().res.is_Ok()
                                &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                                &&& forall |i| #![auto] 0 <= i < resp_objs.len() ==>
                                (
                                    resp_objs[i].metadata.namespace.is_some()
                                    && resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                                    && ((s_prime.resources().contains_key(resp_objs[i].object_ref())
                                            && s_prime.resources()[resp_objs[i].object_ref()].metadata.resource_version
                                            == resp_objs[i].metadata.resource_version) ==> 
                                            s_prime.resources()[resp_objs[i].object_ref()].metadata
                                                == resp_objs[i].metadata)
                                    && resp_objs[i].metadata.resource_version.is_some()
                                    && resp_objs[i].metadata.resource_version.unwrap()
                                            < s_prime.api_server.resource_version_counter
                                )
                            } by {
                                assert(forall |msg| #[trigger] new_msgs.contains(msg) ==> !(#[trigger] msg.src.is_APIServer()));
                                if !new_msgs.contains(msg) {
                                    assert(s.in_flight().contains(msg));
                                }
                            }
                        }
                    },
                    _ => {}
                }
            }
        }
    }
       

    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_ongoing_reconcile_satisfies(controller_id, requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vrs)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<VReplicaSetView>(controller_id, vrs)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(Cluster::etcd_is_finite()),
        lifted_vrs_non_interference_property_action(cluster, controller_id),
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lift_state(every_create_request_is_well_formed(cluster, controller_id))
    );

    cluster.lemma_true_leads_to_always_every_ongoing_reconcile_satisfies(spec, controller_id, requirements);
    temp_pred_equality(
        lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_satisfies(controller_id, requirements))
    );
}

#[verifier(rlimit(4000))]
pub proof fn lemma_eventually_always_at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vrs)))),
        spec.entails(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        spec.entails(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)))),
        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(tla_forall(|vrs: VReplicaSetView| true_pred().leads_to(lift_state(|s: ClusterState| !(s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))),
        spec.entails(always(lift_state(no_pending_update_or_update_status_request_on_pods()))),
        spec.entails(always(lift_state(no_pending_create_or_delete_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(every_create_request_is_well_formed(cluster, controller_id)))),
        spec.entails(always(lift_state(every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)))),
        spec.entails(always(lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)))),
        spec.entails(always(lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id))))),
{
    let requirements = |key: ObjectRef, s: ClusterState| {
        let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
        let filtered_pods = state.filtered_pods.unwrap();
        key == vrs.object_ref() ==> {
            &&& triggering_cr.object_ref() == key
            &&& triggering_cr.metadata().well_formed()
            &&& forall |diff: nat| {
                    #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s)
                } ==> {
                    let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                    let filtered_pods = state.filtered_pods.unwrap();
                    let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                    let req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                    &&& s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
                    &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
                    &&& state.filtered_pods.is_Some()
                    &&& diff <= filtered_pod_keys.len()
                    &&& filtered_pod_keys.no_duplicates()
                    &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                    &&& req_msg.dst.is_APIServer()
                    &&& req_msg.content.is_delete_request()
                    &&& forall |i| #![auto] 0 <= i < diff ==> {
                        &&& matching_pod_entries(vrs, s.resources()).contains_key(filtered_pod_keys[i])
                        &&& PodView::unmarshal(matching_pod_entries(vrs, s.resources())[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                        &&& req_msg.content.get_delete_request().key != filtered_pod_keys[i]
                    }
                }
            &&& state.reconcile_step.is_AfterListPods() ==> {
                let req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                &&& req_msg.dst.is_APIServer()
                &&& req_msg.content.is_list_request()
                &&& req_msg.content.get_list_request() == ListRequest {
                    kind: PodView::kind(),
                    namespace: triggering_cr.metadata.namespace.unwrap(),
                }
                &&& forall |msg| {
                    let req_msg = s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                    &&& #[trigger] s.in_flight().contains(msg)
                    &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                    &&& msg.src.is_APIServer()
                    &&& resp_msg_matches_req_msg(msg, req_msg)
                } ==> {
                    let resp_objs = msg.content.get_list_response().res.unwrap();
                    let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                    &&& msg.content.is_list_response()
                    &&& msg.content.get_list_response().res.is_Ok()
                    &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                    &&& resp_obj_keys.no_duplicates()
                    &&& matching_pod_entries(vrs, s.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                }
            }
        }
    };

    // Technical side-condition: prove two forms of termination property are equivalent
    helper_lemmas::termination_property_for_all_vrs_is_equivalent_to_termination_property_for_all_keys(controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)(s)
        &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as::<VReplicaSetView>(controller_id, vrs)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)(s)
        &&& Cluster::etcd_is_finite()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s_prime)
        &&& no_pending_update_or_update_status_request_on_pods()(s)
        &&& no_pending_create_or_delete_request_not_from_controller_on_pods()(s)
        &&& garbage_collector_does_not_delete_vrs_pods(vrs)(s)
        &&& every_create_request_is_well_formed(cluster, controller_id)(s)
        &&& every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)(s)
        &&& every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)(s)
        &&& every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id)(s)
    };
    
    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) ==> Cluster::every_new_ongoing_reconcile_satisfies(controller_id, requirements)(s, s_prime) by {
        assert forall |key: ObjectRef| (!s.ongoing_reconciles(controller_id).contains_key(key) || requirements(key, s)) 
        && #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key) && stronger_next(s, s_prime) implies requirements(key, s_prime) by {
            VReplicaSetReconcileState::marshal_preserves_integrity();
            VReplicaSetView::marshal_preserves_integrity();
            if s.ongoing_reconciles(controller_id).contains_key(key) && key == vrs.object_ref() {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep((id, _, cr_key_opt)) => {
                        let cr_key = cr_key_opt.get_Some_0();
                        if id == controller_id && cr_key == key {
                            assert forall |diff: nat| {
                                #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                                && requirements(key, s)
                                && stronger_next(s, s_prime)
                            } implies {
                                let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                                let filtered_pods = state.filtered_pods.unwrap();
                                let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                                &&& s_prime.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
                                &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
                                &&& state.filtered_pods.is_Some()
                                &&& diff <= filtered_pod_keys.len()
                                &&& filtered_pod_keys.no_duplicates()
                                &&& s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.is_Some()
                                &&& req_msg.dst.is_APIServer()
                                &&& req_msg.content.is_delete_request()
                                &&& forall |i| #![auto] 0 <= i < diff ==> {
                                    &&& matching_pod_entries(vrs, s_prime.resources()).contains_key(filtered_pod_keys[i])
                                    &&& PodView::unmarshal(matching_pod_entries(vrs, s_prime.resources())[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                                    &&& req_msg.content.get_delete_request().key != filtered_pod_keys[i]
                                }
                            } by {
                                let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                                let new_state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                                let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();

                                let reconcile_step = state.reconcile_step;
                                let new_reconcile_step = new_state.reconcile_step;
                                if reconcile_step.is_AfterListPods() {
                                    let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                                    let cr_msg = step.get_ControllerStep_0().1.get_Some_0();
                                    let req_msg = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg.get_Some_0();
                                    let new_req_msg = s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg.get_Some_0();
                                    let objs = cr_msg.content.get_list_response().res.unwrap();
                                    let obj_keys = objs.map_values(|o: DynamicObjectView| o.object_ref());
                                    let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                                    let pods_or_none = objects_to_pods(objs);
                                    let pods = pods_or_none.unwrap();
                                    let filtered_pods = filter_pods(pods, triggering_cr);
                                    let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());

                                    assert_by(pods.no_duplicates(), {
                                        assert forall |i: int, j: int| #![auto]
                                            0 <= i < pods.len() 
                                            && 0 <= j < pods.len()
                                            && i != j
                                            && requirements(key, s)
                                            && stronger_next(s, s_prime)
                                            && obj_keys.no_duplicates()
                                            implies pods[i] != pods[j] by {
                                            assert(pods == objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()));
                                            assert(pods.len() == objs.len());
                                            seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                                objs, 
                                                |obj: DynamicObjectView| PodView::unmarshal(obj).is_err()
                                            );
                                            assert(objs.contains(objs[i]));
                                            assert(objs.contains(objs[j]));
                                            assert(PodView::unmarshal(objs[i]).is_Ok());
                                            assert(PodView::unmarshal(objs[j]).is_Ok());
                                            
                                            assert(pods[i] == PodView::unmarshal(objs[i]).get_Ok_0());
                                            assert(pods[j] == PodView::unmarshal(objs[j]).get_Ok_0());
                                            
                                            assert(pods[i].object_ref() == objs[i].object_ref());
                                            assert(pods[j].object_ref() == objs[j].object_ref());
                                            
                                            assert(objs[i].object_ref() == obj_keys[i]);
                                            assert(objs[j].object_ref() == obj_keys[j]);
                                        }
                                    });

                                    assert forall |i: int, j: int| #![auto]
                                        0 <= i < filtered_pod_keys.len() 
                                        && 0 <= j < filtered_pod_keys.len()
                                        && i != j
                                        && requirements(key, s)
                                        && stronger_next(s, s_prime)
                                        && pods.no_duplicates()
                                        implies filtered_pod_keys[i] != filtered_pod_keys[j] by {

                                        seq_filter_contains_implies_seq_contains(
                                            pods,
                                            |pod: PodView| 
                                                pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                                                && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                                && pod.metadata.deletion_timestamp.is_None(),
                                            filtered_pods[i]
                                        );
                                        seq_filter_contains_implies_seq_contains(
                                            pods,
                                            |pod: PodView| 
                                                pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                                                && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                                && pod.metadata.deletion_timestamp.is_None(),
                                            filtered_pods[j]
                                        );

                                        let idxi = choose |idx| 0 <= idx < pods.len() && pods[idx] == filtered_pods[i];
                                        let idxj = choose |idx| 0 <= idx < pods.len() && pods[idx] == filtered_pods[j];

                                        assert(pods == objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()));
                                        assert(pods.len() == objs.len());
                                        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                            objs, 
                                            |obj: DynamicObjectView| PodView::unmarshal(obj).is_err()
                                        );
                                        assert(objs.contains(objs[idxi]));
                                        assert(objs.contains(objs[idxj]));
                                        assert(PodView::unmarshal(objs[idxi]).is_Ok());
                                        assert(PodView::unmarshal(objs[idxj]).is_Ok());
                                        
                                        assert(pods[idxi] == PodView::unmarshal(objs[idxi]).get_Ok_0());
                                        assert(pods[idxj] == PodView::unmarshal(objs[idxj]).get_Ok_0());
                                        
                                        assert(pods[idxi].object_ref() == objs[idxi].object_ref());
                                        assert(pods[idxj].object_ref() == objs[idxj].object_ref());

                                        if idxi == idxj {
                                            seq_filter_preserves_no_duplicates(
                                                pods,
                                                |pod: PodView| 
                                                    pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                                                    && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                                    && pod.metadata.deletion_timestamp.is_None(),
                                            );
                                        } else {
                                            assert(obj_keys[idxi] == objs[idxi].object_ref());
                                            assert(obj_keys[idxj] == objs[idxj].object_ref());
                                            assert(objs[idxi].object_ref() != objs[idxj].object_ref());
                                        }
                                    }

                                    let new_diff = new_state.reconcile_step.get_AfterDeletePod_0();
                                    assert forall |i| #![auto] 
                                        0 <= i < new_diff
                                        && requirements(key, s)
                                        && stronger_next(s, s_prime)
                                        && pods.no_duplicates()
                                        && filtered_pod_keys.no_duplicates()
                                        implies {
                                            &&& matching_pod_entries(vrs, s_prime.resources()).contains_key(filtered_pod_keys[i])
                                            &&& PodView::unmarshal(matching_pod_entries(vrs, s_prime.resources())[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                                            &&& new_req_msg.content.get_delete_request().key != filtered_pod_keys[i]
                                        } by {
                                        let obj_keys = objs.map_values(|o: DynamicObjectView| o.object_ref());
                                        let pod_keys = pods.map_values(|p: PodView| p.object_ref());

                                        // first conjunct
                                        seq_filter_contains_implies_seq_contains(
                                            pods,
                                            |pod: PodView| 
                                                pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                                                && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                                && pod.metadata.deletion_timestamp.is_None(),
                                            filtered_pods[i]
                                        );
                                        assert(pods.contains(filtered_pods[i]));
                                        let i1 = choose |j| 0 <= j < pods.len() && pods[j] == filtered_pods[i];
                                        assert(pods[i1] == filtered_pods[i]);
                                        assert(pods == objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()));
                                        assert(pods.len() == objs.len());
                                        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                            objs, 
                                            |obj: DynamicObjectView| PodView::unmarshal(obj).is_err()
                                        );
                                        assert(objs.contains(objs[i1]));
                                        assert(PodView::unmarshal(objs[i1]).is_Ok());
                                        assert(pods[i1] == PodView::unmarshal(objs[i1]).get_Ok_0());
                                        assert(pods[i1].object_ref() == objs[i1].object_ref());
                                        assert(owned_selector_match_is(vrs, objs[i1]));
                                        objs.filter_lemma(|obj| owned_selector_match_is(vrs, obj));
                                        assert(objs.filter(|obj| owned_selector_match_is(vrs, obj)).contains(objs[i1]));
                                        assert(matching_pod_entries(vrs, s.resources()).values().contains(objs[i1]));
                                        assert(matching_pod_entries(vrs, s_prime.resources()).contains_key(filtered_pod_keys[i]));

                                        // second conjunct
                                        assert(matching_pod_entries(vrs, s.resources())[filtered_pod_keys[i]] == objs[i1]);
                                        assert(filtered_pods[i] == PodView::unmarshal(objs[i1]).get_Ok_0());
                                        assert(PodView::unmarshal(matching_pod_entries(vrs, s.resources())[filtered_pod_keys[i]]).is_Ok()
                                                == PodView::unmarshal(objs[i1]).is_Ok());

                                        // third conjunct
                                        assert(new_state.reconcile_step.is_AfterDeletePod());
                                        assert_by(
                                            filtered_pods[new_diff as int].metadata.namespace.is_Some()
                                            && filtered_pods[new_diff as int].metadata.namespace == vrs.metadata.namespace,
                                            {
                                                let nd = new_diff as int;
                                                assert(filtered_pods.contains(filtered_pods[nd]));
                                                seq_filter_contains_implies_seq_contains(
                                                    pods,
                                                    |pod: PodView| 
                                                        pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                                                        && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                                        && pod.metadata.deletion_timestamp.is_None(),
                                                    filtered_pods[nd]
                                                );
                                                let i1 = choose |j| 0 <= j < pods.len() && pods[j] == filtered_pods[i];
                                                assert(pods[i1] == filtered_pods[i]);
                                                assert(pods == objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()));
                                                assert(pods.len() == objs.len());
                                                seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                                    objs, 
                                                    |obj: DynamicObjectView| PodView::unmarshal(obj).is_err()
                                                );
                                                assert(objs.contains(objs[i1]));
                                                assert(PodView::unmarshal(objs[i1]).is_Ok());
                                                assert(pods[i1] == PodView::unmarshal(objs[i1]).get_Ok_0());
                                                assert(pods[i1].object_ref() == objs[i1].object_ref());
                                            }
                                        );
                                        assert(new_req_msg.content.get_delete_request().key == filtered_pods[new_diff as int].object_ref());
                                        assert(filtered_pods[new_diff as int].object_ref() == filtered_pod_keys[new_diff as int]);
                                    }
                                } else {
                                    assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime));
                                    assert(new_reconcile_step.is_AfterDeletePod());
                                    assert(new_reconcile_step.get_AfterDeletePod_0() == diff);
                                    assert(reconcile_step.is_AfterDeletePod());
                                    assert(reconcile_step.get_AfterDeletePod_0() == diff + 1);
                                    assert({
                                        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).unwrap();
                                        let local_state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                                        &&& s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
                                        &&& VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).is_ok()
                                        &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
                                        &&& triggering_cr.object_ref() == vrs.object_ref()
                                        &&& triggering_cr.spec() == vrs.spec()
                                        &&& triggering_cr.metadata().uid == vrs.metadata().uid
                                        &&& local_state.reconcile_step == VReplicaSetRecStepView::AfterDeletePod(diff + 1)
                                    });
                                    assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff + 1))(s));
                                }
                            }

                            // prove that the newly sent message has no response.
                            if s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some() {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                                assert(forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id);
                                assert(s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg));
                                assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) 
                                    && (forall |msg| #[trigger] s.in_flight().contains(msg) ==> msg.rpc_id != req_msg.rpc_id)
                                    && s_prime.in_flight().sub(s.in_flight()) == Multiset::singleton(req_msg)
                                    && msg != req_msg 
                                    implies msg.rpc_id != req_msg.rpc_id by {
                                    if !s.in_flight().contains(msg) {} // need this to invoke trigger.
                                }
                            }
                        } else {
                            let new_msgs = s_prime.in_flight().sub(s.in_flight());

                            let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                            let triggering_cr = VReplicaSetView::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                            let filtered_pods = state.filtered_pods.unwrap();
                            if state.reconcile_step.is_AfterListPods() {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                                assert forall |msg| {
                                    let req_msg = s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                                    &&& #[trigger] s_prime.in_flight().contains(msg)
                                    &&& s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                                    &&& msg.src.is_APIServer()
                                    &&& resp_msg_matches_req_msg(msg, req_msg)
                                    &&& requirements(key, s)
                                    &&& stronger_next(s, s_prime)
                                } implies {
                                    let resp_objs = msg.content.get_list_response().res.unwrap();
                                    let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                                    &&& msg.content.is_list_response()
                                    &&& msg.content.get_list_response().res.is_Ok()
                                    &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                                    &&& resp_obj_keys.no_duplicates()
                                    &&& matching_pod_entries(vrs, s.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                                    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                                } by {
                                    assert(forall |msg| #[trigger] new_msgs.contains(msg) ==> !(#[trigger] msg.src.is_APIServer()));
                                    if !new_msgs.contains(msg) {
                                        assert(s.in_flight().contains(msg));
                                    }
                                }
                            }

                            // annoying maintenance of quantified invariant.
                            assert forall |diff: nat| {
                                #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                                && requirements(key, s)
                                && stronger_next(s, s_prime)
                            } implies {
                                let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                                let filtered_pods = state.filtered_pods.unwrap();
                                let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                                &&& s_prime.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
                                &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
                                &&& state.filtered_pods.is_Some()
                                &&& diff <= filtered_pod_keys.len()
                                &&& filtered_pod_keys.no_duplicates()
                                &&& s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.is_Some()
                                &&& req_msg.dst.is_APIServer()
                                &&& req_msg.content.is_delete_request()
                                &&& forall |i| #![auto] 0 <= i < diff ==> {
                                    &&& matching_pod_entries(vrs, s_prime.resources()).contains_key(filtered_pod_keys[i])
                                    &&& PodView::unmarshal(matching_pod_entries(vrs, s_prime.resources())[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                                    &&& req_msg.content.get_delete_request().key != filtered_pod_keys[i]
                                }
                            } by {
                                assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                                    ==> at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s));
                            }
                        }

                    },
                    Step::APIServerStep(req_msg_opt) => {
                        let current_req_msg = req_msg_opt.unwrap();
                        let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());
                        if state.reconcile_step.is_AfterListPods() {
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                            let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                            assert forall |msg| {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                                &&& #[trigger] s_prime.in_flight().contains(msg)
                                &&& s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                                &&& msg.src.is_APIServer()
                                &&& resp_msg_matches_req_msg(msg, req_msg)
                                &&& requirements(key, s)
                                &&& stronger_next(s, s_prime)
                            } implies {
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                                &&& msg.content.is_list_response()
                                &&& msg.content.get_list_response().res.is_Ok()
                                &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                                &&& resp_obj_keys.no_duplicates()
                                &&& matching_pod_entries(vrs, s_prime.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                                &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                                &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                            } by {
                                if (new_msgs.contains(msg)) {
                                    if current_req_msg == req_msg {
                                        let resp_objs = msg.content.get_list_response().res.unwrap();
                                        let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                                        
                                        assert forall |o: DynamicObjectView| #![auto]
                                        requirements(key, s)
                                        && stronger_next(s, s_prime)
                                        && resp_objs.contains(o)
                                        implies !PodView::unmarshal(o).is_err()
                                                && o.metadata.namespace == vrs.metadata.namespace by {
                                            // Tricky reasoning about .to_seq
                                            let selector = |o: DynamicObjectView| {
                                                &&& o.object_ref().namespace == req_msg.content.get_list_request().namespace
                                                &&& o.object_ref().kind == req_msg.content.get_list_request().kind
                                            };
                                            let selected_elements = s.resources().values().filter(selector);
                                            lemma_values_finite(s.resources());
                                            finite_set_to_seq_contains_all_set_elements(selected_elements);
                                            assert(resp_objs =~= selected_elements.to_seq());
                                            assert(selected_elements.contains(o));
                                        }
                                        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                            resp_objs, 
                                            |o: DynamicObjectView| PodView::unmarshal(o).is_err()
                                        );

                                        assert_by(resp_obj_keys.no_duplicates(), {
                                            let selector = |o: DynamicObjectView| {
                                                &&& o.object_ref().namespace == req_msg.content.get_list_request().namespace
                                                &&& o.object_ref().kind == req_msg.content.get_list_request().kind
                                            };
                                            let selected_elements = s.resources().values().filter(selector);
                                            lemma_values_finite(s.resources());
                                            finite_set_to_seq_has_no_duplicates(selected_elements);
                                            let selected_elements_seq = selected_elements.to_seq();
                                            assert(selected_elements_seq.no_duplicates());
                                            assert forall |o1: DynamicObjectView, o2: DynamicObjectView| #![auto]
                                                o1 != o2 
                                                && selected_elements_seq.contains(o1) 
                                                && selected_elements_seq.contains(o2) 
                                                && requirements(key, s)
                                                && stronger_next(s, s_prime)
                                                implies o1.object_ref() != o2.object_ref() by {
                                                finite_set_to_seq_contains_all_set_elements(selected_elements);
                                                assert(selected_elements.contains(o1));
                                                assert(selected_elements.contains(o2));
                                                assert(s.resources().values().contains(o1));
                                                assert(s.resources().values().contains(o2));
                                                assert(o1.object_ref() != o2.object_ref());
                                            }
                                            let selected_element_keys = selected_elements_seq.map_values(|o: DynamicObjectView| o.object_ref());
                                            assert(selected_element_keys.no_duplicates());
                                            assert(resp_obj_keys =~= selected_element_keys);
                                        });

                                        assert(matching_pod_entries(vrs, s.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set() && resp_objs.no_duplicates()) by {
                                            // reveal API server spec
                                            let selector = |o: DynamicObjectView| {
                                                &&& o.object_ref().namespace == vrs.metadata.namespace.unwrap()
                                                &&& o.object_ref().kind == PodView::kind()
                                            };
                                            assert(resp_objs == s.resources().values().filter(selector).to_seq());
                                            // consistency of no_duplicates
                                            lemma_values_finite(s.resources());
                                            finite_set_to_finite_filtered_set(s.resources().values(), selector);
                                            finite_set_to_seq_has_no_duplicates(s.resources().values().filter(selector));
                                            assert(resp_objs.no_duplicates());
                                            // reveal matching_pod_entries logic
                                            let matched_entries = matching_pod_entries(vrs, s.resources());
                                            assert(matched_entries.values() =~= s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj))) by {
                                                assert forall |obj| s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj) implies matched_entries.values().contains(obj) by {
                                                    assert(owned_selector_match_is(vrs, obj));
                                                    assert(s.resources().contains_key(obj.object_ref()) && s.resources()[obj.object_ref()] == obj);
                                                    assert(matched_entries.contains_key(obj.object_ref()) && matched_entries[obj.object_ref()] == obj);
                                                }
                                                assert forall |obj| matched_entries.values().contains(obj) implies s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj) by {
                                                    assert(s.resources().contains_key(obj.object_ref()));
                                                    assert(owned_selector_match_is(vrs, obj));
                                                }
                                                // optional if antisymmetry_of_set_equality is imported
                                                assert(forall |obj| matched_entries.values().contains(obj) == s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj));
                                            }
                                            assert(s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj) && selector(obj)) == matching_pod_entries(vrs, s.resources()).values());
                                            // merge 2 selectors
                                            assert((|obj| owned_selector_match_is(vrs, obj) && selector(obj)) =~= (|obj| owned_selector_match_is(vrs, obj)));
                                            // get rid of DS conversion, basically babysitting Verus
                                            assert(resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set() =~= s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj))) by {
                                                assert(resp_objs == s.resources().values().filter(selector).to_seq());
                                                assert((|obj : DynamicObjectView| owned_selector_match_is(vrs, obj) && selector(obj)) =~= (|obj : DynamicObjectView| owned_selector_match_is(vrs, obj)));
                                                seq_filter_preserves_no_duplicates(resp_objs, |obj| owned_selector_match_is(vrs, obj));
                                                seq_filter_is_a_subset_of_original_seq(resp_objs, |obj| owned_selector_match_is(vrs, obj));
                                                finite_set_to_seq_contains_all_set_elements(s.resources().values().filter(selector));
                                                finite_set_to_seq_contains_all_set_elements(s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)));
                                                assert(forall |obj| resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set().contains(obj) ==> {
                                                    &&& resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj)
                                                    &&& #[trigger] resp_objs.contains(obj)
                                                    &&& s.resources().values().filter(selector).to_seq().contains(obj)
                                                    &&& s.resources().values().filter(selector).contains(obj)
                                                    &&& s.resources().values().contains(obj)
                                                    &&& #[trigger] owned_selector_match_is(vrs, obj)
                                                    &&& s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj)
                                                });
                                                assert(forall |obj| s.resources().values().filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj) ==> {
                                                    &&& s.resources().values().contains(obj)
                                                    &&& owned_selector_match_is(vrs, obj)
                                                    &&& #[trigger] selector(obj)
                                                    &&& s.resources().values().filter(selector).contains(obj)
                                                    &&& s.resources().values().filter(selector).to_seq().contains(obj)
                                                    &&& resp_objs.contains(obj)
                                                    &&& resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).contains(obj)
                                                    &&& resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set().contains(obj)
                                                });
                                            }
                                        }
                                        
                                        assert({
                                            let resp_objs = msg.content.get_list_response().res.unwrap();
                                            let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                                            &&& msg.content.is_list_response()
                                            &&& msg.content.get_list_response().res.is_Ok()
                                            &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                                            &&& resp_obj_keys.no_duplicates()
                                            &&& matching_pod_entries(vrs, s_prime.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                                            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                                            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                                        });
                                    } else {
                                        assert(s.in_flight().contains(current_req_msg));
                                        assert(current_req_msg.rpc_id != req_msg.rpc_id);
                                        let resp_objs = msg.content.get_list_response().res.unwrap();
                                        assert_by(
                                            matching_pod_entries(vrs, s_prime.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set(),
                                            {
                                                assert({
                                                    &&& forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(diff))(s))
                                                    &&& forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s))
                                                });
                                                assert(forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                                                        ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s));
                                                lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
                                                    s, s_prime, vrs, cluster, controller_id, 42, current_req_msg
                                                );
                                            }
                                        );
                                    }
                                } else {
                                    let msg_antecedent = {
                                        &&& s.in_flight().contains(msg)
                                        &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                                        &&& msg.src.is_APIServer()
                                        &&& resp_msg_matches_req_msg(msg, req_msg)
                                    };
                                    let inv_pre = |msg: Message| {
                                        let content = msg.content;
                                        let req = content.get_delete_request();
                                        let key = content.get_delete_request().key;
                                        let obj = s.resources()[key];
                                        &&& s.in_flight().contains(msg)
                                        &&& msg.src.is_Controller()
                                        &&& msg.src.get_Controller_0() == controller_id
                                        &&& msg.dst.is_APIServer()
                                        &&& msg.content.is_APIRequest()
                                        &&& content.is_delete_request()
                                        &&& s.resources().contains_key(key)
                                        &&& owned_selector_match_is(vrs, obj)
                                        // NOTE: We require that the resource version in etcd is
                                        // equal to the one carried by the delete request to
                                        // exclude the case where another reconcile working on another
                                        // vrs object tries to delete the same object.
                                        &&& req.preconditions.is_Some()
                                        &&& req.preconditions.unwrap().resource_version.is_Some()
                                        &&& req.preconditions.unwrap().uid.is_None()
                                        &&& obj.metadata.resource_version.is_Some()
                                        &&& obj.metadata.resource_version.unwrap() == 
                                                req.preconditions.unwrap().resource_version.unwrap()
                                    };

                                    if inv_pre(current_req_msg) {
                                        assert(forall |diff: nat| ! #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s));
                                        assert(false);
                                    } else if (current_req_msg.content.is_delete_request()) {
                                        let current_req = current_req_msg.content.get_delete_request();
                                        if !(current_req_msg.src.is_Controller() || current_req_msg.src.is_BuiltinController()) {
                                            assert({
                                                &&& s.in_flight().contains(current_req_msg)
                                                &&& !(current_req_msg.src.is_Controller() || current_req_msg.src.is_BuiltinController())
                                                &&& current_req_msg.dst.is_APIServer()
                                                &&& current_req_msg.content.is_APIRequest()
                                            } ==>{
                                                &&& current_req_msg.content.is_create_request() ==> current_req_msg.content.get_create_request().key().kind != PodView::kind()
                                                &&& current_req_msg.content.is_delete_request() ==> current_req_msg.content.get_delete_request().key.kind != PodView::kind()
                                            });
                                        } else if current_req_msg.src.is_Controller() && current_req_msg.src.get_Controller_0() != controller_id {
                                            assert(vrs_not_interfered_by(controller_id, current_req_msg.src.get_Controller_0())(s));
                                        } 
                                    }

                                    if msg_antecedent {
                                        let resp_objs = msg.content.get_list_response().res.unwrap();
                                        let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());

                                        assert_by(
                                            matching_pod_entries(vrs, s_prime.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set(),
                                            {
                                                assert({
                                                    &&& forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(diff))(s))
                                                    &&& forall |diff: nat| !(#[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s))
                                                });
                                                assert(forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                                                        ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s));
                                                lemma_api_request_outside_create_or_delete_loop_maintains_matching_pods(
                                                    s, s_prime, vrs, cluster, controller_id, 42, current_req_msg
                                                );
                                            }
                                        );
                                        assert({
                                            let resp_objs = msg.content.get_list_response().res.unwrap();
                                            let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                                            &&& msg.content.is_list_response()
                                            &&& msg.content.get_list_response().res.is_Ok()
                                            &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                                            &&& resp_obj_keys.no_duplicates()
                                            //&&& matching_pod_entries(vrs, s_prime.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                                            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                                            &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                                        });
                                    }
                                }
                            }

                            // annoying maintenance of quantified invariant.
                            assert forall |diff: nat| {
                                #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                                && requirements(key, s)
                                && stronger_next(s, s_prime)
                            } implies {
                                let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                                let filtered_pods = state.filtered_pods.unwrap();
                                let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                                &&& s_prime.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
                                &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
                                &&& state.filtered_pods.is_Some()
                                &&& diff <= filtered_pod_keys.len()
                                &&& filtered_pod_keys.no_duplicates()
                                &&& s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.is_Some()
                                &&& req_msg.dst.is_APIServer()
                                &&& req_msg.content.is_delete_request()
                                &&& forall |i| #![auto] 0 <= i < diff ==> {
                                    &&& matching_pod_entries(vrs, s_prime.resources()).contains_key(filtered_pod_keys[i])
                                    &&& PodView::unmarshal(matching_pod_entries(vrs, s_prime.resources())[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                                    &&& req_msg.content.get_delete_request().key != filtered_pod_keys[i]
                                }
                            } by {
                                assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                                    ==> at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s));
                            }
                        } else {
                            // annoying maintenance of quantified invariant.
                            assert forall |diff: nat| {
                                #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                                && requirements(key, s)
                                && stronger_next(s, s_prime)
                            } implies {
                                let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                                let filtered_pods = state.filtered_pods.unwrap();
                                let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                                &&& s_prime.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
                                &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
                                &&& state.filtered_pods.is_Some()
                                &&& diff <= filtered_pod_keys.len()
                                &&& filtered_pod_keys.no_duplicates()
                                &&& s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.is_Some()
                                &&& req_msg.dst.is_APIServer()
                                &&& req_msg.content.is_delete_request()
                                &&& forall |i| #![auto] 0 <= i < diff ==> {
                                    &&& matching_pod_entries(vrs, s_prime.resources()).contains_key(filtered_pod_keys[i])
                                    &&& PodView::unmarshal(matching_pod_entries(vrs, s_prime.resources())[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                                    &&& req_msg.content.get_delete_request().key != filtered_pod_keys[i]
                                }
                            } by {
                                assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s));
                                
                                assert forall |i: int|
                                    #![trigger VReplicaSetReconcileState::unmarshal(
                                        s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state
                                    ).unwrap().filtered_pods.unwrap()[i]] {
                                    &&& 0 <= i < diff
                                    &&& requirements(key, s)
                                    &&& stronger_next(s, s_prime)
                                    &&& at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                                } implies {
                                    let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                                    let filtered_pods = state.filtered_pods.unwrap();
                                    let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                                    let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                                    &&& matching_pod_entries(vrs, s_prime.resources()).contains_key(filtered_pod_keys[i])
                                    &&& PodView::unmarshal(matching_pod_entries(vrs, s_prime.resources())[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                                    &&& req_msg.content.get_delete_request().key != filtered_pod_keys[i]
                                } by {
                                    let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                                    let filtered_pods = state.filtered_pods.unwrap();
                                    let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                                    let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                                    assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s));
                                    if current_req_msg.content.is_create_request() {
                                        assert(forall |diff: nat| ! #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterCreatePod(diff))(s));
                                    } else if current_req_msg.content.is_delete_request() {
                                        if current_req_msg != req_msg {
                                            lemma_api_request_not_made_by_vrs_maintains_matching_pods(
                                                s, s_prime, vrs, cluster, controller_id, 42, current_req_msg, Some(req_msg)
                                            );
                                        }
                                    }                                    
                                }
                            }
                        }
                    },
                    Step::BuiltinControllersStep(..) => {
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());

                        let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                        let triggering_cr = VReplicaSetView::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                        let filtered_pods = state.filtered_pods.unwrap();
                        if state.reconcile_step.is_AfterListPods() {
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                            assert forall |msg| {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                                &&& #[trigger] s_prime.in_flight().contains(msg)
                                &&& s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                                &&& msg.src.is_APIServer()
                                &&& resp_msg_matches_req_msg(msg, req_msg)
                                &&& requirements(key, s)
                                &&& stronger_next(s, s_prime)
                            } implies {
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                let resp_obj_keys = resp_objs.map_values(|o: DynamicObjectView| o.object_ref());
                                &&& msg.content.is_list_response()
                                &&& msg.content.get_list_response().res.is_Ok()
                                &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                                &&& resp_obj_keys.no_duplicates()
                                &&& matching_pod_entries(vrs, s.resources()).values() == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
                                &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace.is_Some()
                                &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
                            } by {
                                assert(forall |msg| #[trigger] new_msgs.contains(msg) ==> !(#[trigger] msg.src.is_APIServer()));
                                if !new_msgs.contains(msg) {
                                    assert(s.in_flight().contains(msg));
                                }
                            }
                        }

                        // annoying maintenance of quantified invariant.
                        assert forall |diff: nat| {
                            #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                            && requirements(key, s)
                            && stronger_next(s, s_prime)
                        } implies {
                            let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                            let filtered_pods = state.filtered_pods.unwrap();
                            let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                            &&& s_prime.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
                            &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
                            &&& state.filtered_pods.is_Some()
                            &&& diff <= filtered_pod_keys.len()
                            &&& filtered_pod_keys.no_duplicates()
                            &&& s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.is_Some()
                            &&& req_msg.dst.is_APIServer()
                            &&& req_msg.content.is_delete_request()
                            &&& forall |i| #![auto] 0 <= i < diff ==> {
                                &&& matching_pod_entries(vrs, s_prime.resources()).contains_key(filtered_pod_keys[i])
                                &&& PodView::unmarshal(matching_pod_entries(vrs, s_prime.resources())[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                                &&& req_msg.content.get_delete_request().key != filtered_pod_keys[i]
                            }
                        } by {
                            assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                                ==> at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s));
                        }
                    },
                    _ => {
                        // annoying maintenance of quantified invariant.
                        assert forall |diff: nat| {
                            #[trigger] at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                            && requirements(key, s)
                            && stronger_next(s, s_prime)
                        } implies {
                            let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
                            let filtered_pods = state.filtered_pods.unwrap();
                            let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
                            &&& s_prime.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
                            &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
                            &&& state.filtered_pods.is_Some()
                            &&& diff <= filtered_pod_keys.len()
                            &&& filtered_pod_keys.no_duplicates()
                            &&& s_prime.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg.is_Some()
                            &&& req_msg.dst.is_APIServer()
                            &&& req_msg.content.is_delete_request()
                            &&& forall |i| #![auto] 0 <= i < diff ==> {
                                &&& matching_pod_entries(vrs, s_prime.resources()).contains_key(filtered_pod_keys[i])
                                &&& PodView::unmarshal(matching_pod_entries(vrs, s_prime.resources())[filtered_pod_keys[i]]).get_Ok_0() == filtered_pods[i]
                                &&& req_msg.content.get_delete_request().key != filtered_pod_keys[i]
                            }
                        } by {
                            assert(at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s_prime)
                                ==> at_vrs_step_with_vrs(vrs, controller_id, VReplicaSetRecStepView::AfterDeletePod(diff))(s));
                        }
                    }
                }
            } 
        }
    }
       

    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_ongoing_reconcile_satisfies(controller_id, requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vrs)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<VReplicaSetView>(controller_id, vrs)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)),
        lift_state(Cluster::etcd_is_finite()),
        lifted_vrs_non_interference_property_action(cluster, controller_id),
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lift_state(no_pending_create_or_delete_request_not_from_controller_on_pods()),
        lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(every_create_request_is_well_formed(cluster, controller_id)),
        lift_state(every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(every_create_matching_pod_request_implies_at_after_create_pod_step(vrs, cluster.installed_types, controller_id)),
        lift_state(every_delete_matching_pod_request_implies_at_after_delete_pod_step(vrs, controller_id))
    );

    cluster.lemma_true_leads_to_always_every_ongoing_reconcile_satisfies(spec, controller_id, requirements);

    temp_pred_equality(
        lift_state(at_after_delete_pod_step_implies_filtered_pods_in_matching_pod_entries(vrs, controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_satisfies(controller_id, requirements))
    );
    
}

pub proof fn lemma_eventually_always_every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(no_pending_update_or_update_status_request_on_pods()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_not_interfered_by(controller_id, other_id)))),
        spec.entails(always(lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id))))),
{
    let requirements = |msg: Message, s: ClusterState| {
        ({
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
            &&& msg.content.is_APIRequest()
            &&& msg.content.is_delete_request()
        })
        ==>
        ({
            let content = msg.content;
            let req = content.get_delete_request();
            &&& req.preconditions.is_Some()
            &&& req.preconditions.unwrap().resource_version.is_Some()
            &&& req.preconditions.unwrap().uid.is_None()
            &&& req.preconditions.unwrap().resource_version.unwrap() < s.api_server.resource_version_counter
        })
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        &&& msg.src.is_Controller()
        &&& msg.src.get_Controller_0() == controller_id
        &&& msg.content.is_APIRequest()
        &&& msg.content.is_delete_request()
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& no_pending_update_or_update_status_request_on_pods()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_not_interfered_by(controller_id, other_id)(s_prime)
        &&& each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)(s)
    };

    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            VReplicaSetReconcileState::marshal_preserves_integrity();
            VReplicaSetView::marshal_preserves_integrity();
            if requirements_antecedent(msg, s) {
                if !s.in_flight().contains(msg) {
                    let content = msg.content;
                    let request_key = content.get_delete_request().key;
                    let obj = s.resources()[content.get_delete_request().key];

                    let step = choose |step| cluster.next_step(s, s_prime, step);
                    let cr_key = step.get_ControllerStep_0().2.get_Some_0();
                    let local_step = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let local_step_prime = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap().reconcile_step;
                    let new_diff = local_step_prime.get_AfterDeletePod_0();

                    let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();

                    if local_step.is_AfterListPods() {
                        let cr_msg = step.get_ControllerStep_0().1.get_Some_0();
                        let req_msg = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg.get_Some_0();
                        let objs = cr_msg.content.get_list_response().res.unwrap();
                        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                        let desired_replicas: nat = triggering_cr.spec.replicas.unwrap_or(0) as nat;
                        let pods_or_none = objects_to_pods(objs);
                        let pods = pods_or_none.unwrap();
                        let filtered_pods = filter_pods(pods, triggering_cr);
                        let diff = filtered_pods.len() - desired_replicas;

                        // show filtered_pods[diff - 1] has the desired property.
                        seq_filter_contains_implies_seq_contains(
                            pods,
                            |pod: PodView|
                            pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                            && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                            && pod.metadata.deletion_timestamp.is_None(),
                            filtered_pods[diff - 1]
                        );

                        // Show that pods[idx1] and filtered_pods[diff - 1] have the same key and metadata.
                        let idx1 = choose |i| 0 <= i < pods.len() && pods[i] == filtered_pods[diff - 1];
                        assert(pods[idx1].object_ref() == filtered_pods[diff - 1].object_ref());
                        assert(pods[idx1].metadata == filtered_pods[diff - 1].metadata);

                        // Show that pods[idx1] and objs[idx1] have the same key and metadata.
                        let unwrap_obj = |o: DynamicObjectView| PodView::unmarshal(o).unwrap();
                        assert(pods == objs.map_values(unwrap_obj));
                        assert(objs.contains(objs[idx1]));
                        seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                            objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err()
                        );
                        assert(PodView::unmarshal(objs[idx1]).is_ok());
                        assert(objs[idx1].object_ref() == pods[idx1].object_ref());
                        assert(objs[idx1].metadata == pods[idx1].metadata);

                        // Show that objs[idx1] and obj (in etcd) have the same key and metadata.
                        if s.resources().contains_key(objs[idx1].object_ref()) 
                            && s.resources()[objs[idx1].object_ref()].metadata.resource_version == objs[idx1].metadata.resource_version {
                            assert(objs[idx1].object_ref() == obj.object_ref());
                            assert(objs[idx1].metadata == obj.metadata);

                            assert(request_key == obj.object_ref());
                        } 
                    }
                    assert(requirements(msg, s_prime));
                }
            }
        }
    }
    
    helper_lemmas::vrs_non_interference_property_equivalent_to_lifted_vrs_non_interference_property_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next), 
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vrs)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(no_pending_update_or_update_status_request_on_pods()),
        lifted_vrs_non_interference_property_action(cluster, controller_id),
        lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id))
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(every_delete_request_from_vrs_has_rv_precondition_that_is_less_than_rv_counter(vrs, controller_id)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_always_vrs_in_etcd_does_not_have_deletion_timestamp(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.controller_models.contains_key(controller_id),
ensures
    spec.entails(always(lift_state(vrs_in_etcd_does_not_have_deletion_timestamp(vrs, controller_id)))),
{
    let inv = vrs_in_etcd_does_not_have_deletion_timestamp(vrs, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& vrs_in_etcd_does_not_have_deletion_timestamp(vrs, controller_id)(s)
    };
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

pub proof fn lemma_always_vrs_in_schedule_does_not_have_deletion_timestamp(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.controller_models.contains_key(controller_id),
ensures
    spec.entails(always(lift_state(vrs_in_schedule_does_not_have_deletion_timestamp(vrs, controller_id)))),
{
    let inv = vrs_in_schedule_does_not_have_deletion_timestamp(vrs, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& vrs_in_etcd_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    lemma_always_vrs_in_etcd_does_not_have_deletion_timestamp(spec, vrs, cluster, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(vrs_in_etcd_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

pub proof fn lemma_always_vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int
)
requires    
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.controller_models.contains_key(controller_id),
ensures
    spec.entails(always(lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
{
    let inv = vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& vrs_in_etcd_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& vrs_in_schedule_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    lemma_always_vrs_in_etcd_does_not_have_deletion_timestamp(spec, vrs, cluster, controller_id);
    lemma_always_vrs_in_schedule_does_not_have_deletion_timestamp(spec, vrs, cluster, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(vrs_in_etcd_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(vrs_in_schedule_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

}