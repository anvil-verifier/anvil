// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use verifiable_controllers::kubernetes_api_objects::spec::prelude::*;
use verifiable_controllers::kubernetes_cluster::spec::{
    api_server::state_machine::*, cluster::*, controller::types::*, message::*,
};
use verifiable_controllers::reconciler::spec::io::*;
use verifiable_controllers::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    proof::{
        helper_invariants::predicate::*, helper_lemmas, liveness::api_actions::*, predicate::*,
    },
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verifiable_controllers::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*};
use vstd::{map::*, map_lib::*, multiset::*, prelude::*, seq_lib::*};

verus! {

pub proof fn lemma_eventually_always_no_other_pending_request_interferes_with_vrs_reconcile(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
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
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(tla_forall(|vrs: VReplicaSetView| lift_state(vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs))))),
        spec.entails(always(lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)))),
        spec.entails(always(lift_state(no_pending_mutation_request_not_from_controller_on_pods()))),
        spec.entails(always(lift_state(every_msg_from_vrs_controller_carries_vrs_key(controller_id)))),
        spec.entails(always(lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))))),
{
    let requirements = |msg: Message, s: ClusterState| {
        &&& s.in_flight().contains(msg)
        &&& msg.src != HostId::Controller(controller_id, vrs.object_ref())
        &&& msg.dst.is_APIServer()
        &&& msg.content.is_APIRequest()
    } ==> {
        let content = msg.content;
        match content.get_APIRequest_0() {
            APIRequest::CreateRequest(req) => no_other_pending_create_request_interferes_with_vrs_reconcile(req, vrs)(s),
            APIRequest::UpdateRequest(req) => no_other_pending_update_request_interferes_with_vrs_reconcile(req, vrs)(s),
            APIRequest::UpdateStatusRequest(req) => no_other_pending_update_status_request_interferes_with_vrs_reconcile(req, vrs)(s),
            APIRequest::GetThenUpdateRequest(req) => no_other_pending_get_then_update_request_interferes_with_vrs_reconcile(req, vrs)(s),
            APIRequest::DeleteRequest(req) => no_other_pending_delete_request_interferes_with_vrs_reconcile(req, vrs)(s),
            APIRequest::GetThenDeleteRequest(req) => no_other_pending_get_then_delete_request_interferes_with_vrs_reconcile(req, vrs)(s),
            _ => true,
        }
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        &&& s.in_flight().contains(msg)
        &&& msg.src != HostId::Controller(controller_id, vrs.object_ref())
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
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s_prime)
        &&& Cluster::etcd_is_finite()(s)
        &&& vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)(s)
        &&& garbage_collector_does_not_delete_vrs_pods(vrs)(s)
        &&& garbage_collector_does_not_delete_vrs_pods(vrs)(s_prime)
        &&& no_pending_mutation_request_not_from_controller_on_pods()(s)
        &&& no_pending_mutation_request_not_from_controller_on_pods()(s_prime)
        &&& every_msg_from_vrs_controller_carries_vrs_key(controller_id)(s)
        &&& every_msg_from_vrs_controller_carries_vrs_key(controller_id)(s_prime)
        &&& forall |vrs: VReplicaSetView| #[trigger] vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs)(s)
        &&& forall |vrs: VReplicaSetView| #[trigger] vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs)(s_prime)
    };

    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            PodView::marshal_preserves_integrity();
            VReplicaSetReconcileState::marshal_preserves_integrity();
            VReplicaSetView::marshal_preserves_integrity();

            if requirements_antecedent(msg, s_prime) {
                // approach: dissect msg by its sender and content, and invoke the appropriate invariant
                // (instantiated on both s and s_prime).

                match msg.src {
                    HostId::Controller(id, cr_key) => {
                        if id != controller_id {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(vrs_rely(id)(s_prime));
                        } else {
                            let havoc_vrs = make_vrs(); // havoc for VReplicaSetView
                            let vrs_with_key = VReplicaSetView {
                                metadata: ObjectMetaView {
                                    name: Some(cr_key.name),
                                    namespace: Some(cr_key.namespace),
                                    ..havoc_vrs.metadata
                                },
                                ..havoc_vrs
                            };
                            assert(cr_key == vrs_with_key.object_ref());
                            assert(vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs_with_key)(s_prime));
                        }
                    },
                    _ => {},
                }
           }
        }
    }

    always_to_always_later(spec, lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)));
    always_to_always_later(spec, lift_state(no_pending_mutation_request_not_from_controller_on_pods()));
    always_to_always_later(spec, lift_state(every_msg_from_vrs_controller_carries_vrs_key(controller_id)));
    helper_lemmas::only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself_action(
        spec, cluster, controller_id
    );
    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition_action(
        spec, cluster, controller_id
    );
    let only_interferes_with_itself_closure = |vrs: VReplicaSetView| lift_state(vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs));

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
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(Cluster::desired_state_is(vrs)),
        lifted_vrs_rely_condition_action(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id)),
        lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)),
        later(lift_state(garbage_collector_does_not_delete_vrs_pods(vrs))),
        lift_state(no_pending_mutation_request_not_from_controller_on_pods()),
        later(lift_state(no_pending_mutation_request_not_from_controller_on_pods())),
        lift_state(every_msg_from_vrs_controller_carries_vrs_key(controller_id)),
        later(lift_state(every_msg_from_vrs_controller_carries_vrs_key(controller_id))),
        lifted_vrs_reconcile_request_only_interferes_with_itself_action(controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

// Havoc function for VReplicaSetView.
uninterp spec fn make_vrs() -> VReplicaSetView;

#[verifier(rlimit(100))]
pub proof fn lemma_always_vrs_reconcile_request_only_interferes_with_itself(
    spec: TempPred<ClusterState>, 
    cluster: Cluster, 
    controller_id: int,
    vrs: VReplicaSetView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
    ensures
        spec.entails(always(lift_state(vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs))))
{
    let invariant = vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs);

    cluster.lemma_always_cr_states_are_unmarshallable::<VReplicaSetReconciler, VReplicaSetReconcileState, VReplicaSetView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    lemma_always_each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(spec, cluster, controller_id);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>(spec);

    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>())
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        VReplicaSetView::marshal_preserves_integrity();
        VReplicaSetReconcileState::marshal_preserves_integrity();
        PodView::marshal_preserves_integrity();

        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(req_msg_opt) => {
                let req_msg = req_msg_opt.unwrap();

                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content.is_APIRequest()
                    &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
                } implies match msg.content.get_APIRequest_0() {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_reconcile_create_request_only_interferes_with_itself(req, vrs)(s_prime),
                    APIRequest::GetThenDeleteRequest(req) => vrs_reconcile_get_then_delete_request_only_interferes_with_itself(req, vrs)(s_prime),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
            Step::ControllerStep((id, _, cr_key_opt)) => {
                let cr_key = cr_key_opt->0;
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content.is_APIRequest()
                    &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
                } implies match msg.content.get_APIRequest_0() {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_reconcile_create_request_only_interferes_with_itself(req, vrs)(s_prime),
                    APIRequest::GetThenDeleteRequest(req) => vrs_reconcile_get_then_delete_request_only_interferes_with_itself(req, vrs)(s_prime),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.

                    if id == controller_id {
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());

                        if new_msgs.contains(msg) && msg.content.is_get_then_delete_request() {
                            let req = msg.content.get_get_then_delete_request();
                            let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();    
                            
                            assert(req.owner_ref == triggering_cr.controller_owner_ref());
                        }
                    }
                }
            }
            _ => {
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content.is_APIRequest()
                    &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
                } implies match msg.content.get_APIRequest_0() {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_reconcile_create_request_only_interferes_with_itself(req, vrs)(s_prime),
                    APIRequest::GetThenDeleteRequest(req) => vrs_reconcile_get_then_delete_request_only_interferes_with_itself(req, vrs)(s_prime),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}

// TODO: Investigate flaky proof.
#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_no_pending_interfering_update_request(
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
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_pending_interfering_update_request())))),
{
    let requirements = |msg: Message, s: ClusterState| {
        msg.content.is_APIRequest() ==>
            match msg.content.get_APIRequest_0() {
                APIRequest::UpdateRequest(req) => vrs_rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) => vrs_rely_get_then_update_req(req)(s),
                _ => true,
            }
    };

    // To make our job easier, we carry a few stronger conditions on what
    // in the cluster can send updates.
    let stronger_requirements = |msg: Message, s: ClusterState| {
        msg.content.is_APIRequest() ==>
            match msg.content.get_APIRequest_0() {
                APIRequest::UpdateRequest(req) =>
                    msg.src.is_Controller()
                    && !msg.src.is_controller_id(controller_id)
                    && vrs_rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) =>
                    msg.src.is_Controller()
                    && !msg.src.is_controller_id(controller_id)
                    && vrs_rely_get_then_update_req(req)(s),
                _ => true,
            }
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
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s_prime)
    };

    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(stronger_requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || stronger_requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies stronger_requirements(msg, s_prime) by {
            if msg.content.is_APIRequest()
                && msg.content.get_APIRequest_0().is_UpdateRequest() {
                if msg.src.is_Controller() {
                    let id = msg.src.get_Controller_0();
                    PodView::marshal_preserves_integrity();
                    VReplicaSetReconcileState::marshal_preserves_integrity();
                    if id != controller_id {
                        assert(vrs_rely(id)(s_prime));
                    } else {
                        assert(!s.in_flight().contains(msg));
                    }
                }
            } else if msg.content.is_APIRequest()
                && msg.content.get_APIRequest_0().is_GetThenUpdateRequest() {
                if msg.src.is_Controller() {
                    let id = msg.src.get_Controller_0();
                    PodView::marshal_preserves_integrity();
                    VReplicaSetReconcileState::marshal_preserves_integrity();
                    if id != controller_id {
                        assert(vrs_rely(id)(s_prime));
                    } else {
                        assert(!s.in_flight().contains(msg));
                    }
                }
            }
        }
    }

    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(stronger_requirements)),
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
        lifted_vrs_rely_condition_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, stronger_requirements);

    // Convert true ~> []stronger_requirements to true ~> []requirements.
    entails_preserved_by_always(
        lift_state(Cluster::every_in_flight_req_msg_satisfies(stronger_requirements)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
    leads_to_weaken(
        spec,
        true_pred(), always(lift_state(Cluster::every_in_flight_req_msg_satisfies(stronger_requirements))),
        true_pred(), always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)))
    );

    temp_pred_equality(
        lift_state(no_pending_interfering_update_request()),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

#[verifier(rlimit(100))]
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
        spec.entails(always(lift_state(no_pending_interfering_update_request()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),
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
            &&& req.preconditions is Some
            &&& req.preconditions.unwrap().uid is Some
            &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
            &&& s.resources().contains_key(req.key) ==> {
                let obj = s.resources()[req.key];
                ||| !(obj.metadata.owner_references_contains(vrs.controller_owner_ref())
                        && obj.kind == Kind::PodKind
                        && obj.metadata.namespace == vrs.metadata.namespace)
                ||| obj.metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap()
            }
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
        &&& no_pending_interfering_update_request()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s_prime)
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
                        let owner_references = obj.metadata.owner_references->0;
                        assert(forall |i| #![trigger owner_references[i]] 0 <= i < owner_references.len() ==> {
                            // the referred owner object does not exist in the cluster state
                            ||| !s.resources().contains_key(owner_reference_to_object_reference(owner_references[i], key.namespace))
                            // or it exists but has a different uid
                            // (which means the actual owner was deleted and another object with the same name gets created again)
                            ||| s.resources()[owner_reference_to_object_reference(owner_references[i], key.namespace)].metadata.uid != Some(owner_references[i].uid)
                        });
                        if obj.metadata.owner_references_contains(vrs.controller_owner_ref())
                            && obj.kind == Kind::PodKind
                            && obj.metadata.namespace == vrs.metadata.namespace {
                            let idx = choose |i| 0 <= i < owner_references.len() && owner_references[i] == vrs.controller_owner_ref();
                            assert(s.resources().contains_key(vrs.object_ref()));
                        }
                    }
                },
                _ => {}
            }
        }
    }

    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition_action(
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
        lift_state(no_pending_interfering_update_request()),
        lifted_vrs_rely_condition_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(garbage_collector_does_not_delete_vrs_pods(vrs)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_no_pending_mutation_request_not_from_controller_on_pods(
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
            ==> spec.entails(always(lift_state(#[trigger] vrs_rely(other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_pending_mutation_request_not_from_controller_on_pods())))),
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
            &&& msg.content.is_update_request() ==> msg.content.get_update_request().key().kind != PodView::kind()
            // too radical, loosen it later to allow updates on pod status.
            &&& msg.content.is_update_status_request() ==> msg.content.get_update_status_request().key().kind != PodView::kind()
            &&& msg.content.is_delete_request() ==> msg.content.get_delete_request().key.kind != PodView::kind()
            &&& msg.content.is_get_then_delete_request() ==> msg.content.get_get_then_delete_request().key.kind != PodView::kind()
            &&& msg.content.is_get_then_update_request() ==> msg.content.get_get_then_update_request().key().kind != PodView::kind()
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
                ==> #[trigger] vrs_rely(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vrs_rely(other_id)(s_prime)
    };

    helper_lemmas::vrs_rely_condition_equivalent_to_lifted_vrs_rely_condition_action(
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
        lifted_vrs_rely_condition_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_pending_mutation_request_not_from_controller_on_pods()),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

// TODO: investigate flaky proof.
#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
pub proof fn lemma_always_each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
    ensures spec.entails(always(lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)))),
{
    let invariant = each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id);
    let invariant_matrix = |key: ObjectRef, s: ClusterState| {
        let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
        let filtered_pods = state.filtered_pods.unwrap();
        &&& triggering_cr.object_ref() == key
        &&& triggering_cr.metadata().well_formed_for_namespaced()
        &&& state.filtered_pods is Some ==>
            forall |i| #![trigger filtered_pods[i]] 0 <= i < filtered_pods.len() ==>
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
            let req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
            &&& req_msg.dst.is_APIServer()
            &&& req_msg.content.is_list_request()
            &&& req_msg.content.get_list_request() == ListRequest {
                kind: PodView::kind(),
                namespace: triggering_cr.metadata.namespace.unwrap(),
            }
            &&& forall |msg| {
                let req_msg = s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg->0;
                &&& #[trigger] s.in_flight().contains(msg)
                &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                &&& msg.src.is_APIServer()
                &&& resp_msg_matches_req_msg(msg, req_msg)
                &&& is_ok_resp(msg.content.get_APIResponse_0())
            } ==> {
                let resp_objs = msg.content.get_list_response().res.unwrap();
                &&& msg.content.is_list_response()
                &&& msg.content.get_list_response().res is Ok
                &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0
                &&& forall |i| #![trigger resp_objs[i]] 0 <= i < resp_objs.len() ==>
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

    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_builtin_object_in_etcd_is_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>(spec);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(spec, controller_id);
    cluster.lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(spec, controller_id);
    cluster.lemma_always_etcd_is_finite(spec);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
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
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)(s)
        &&& Cluster::etcd_is_finite()(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
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
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(Cluster::etcd_is_finite())
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| {
            &&& invariant(s)
            &&& stronger_next(s, s_prime)
            &&& #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
        } implies invariant_matrix(key, s_prime) by {
            VReplicaSetReconcileState::marshal_preserves_integrity();
            VReplicaSetView::marshal_preserves_integrity();
            if s.ongoing_reconciles(controller_id).contains_key(key) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep((id, _, cr_key_opt)) => {
                        let cr_key = cr_key_opt->0;
                        if id == controller_id && cr_key == key {
                            let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();

                            let reconcile_step = state.reconcile_step;
                            let cr_msg = step.get_ControllerStep_0().1->0;
                            if reconcile_step.is_AfterListPods()
                               && is_ok_resp(cr_msg.content.get_APIResponse_0()) {
                                let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                                let req_msg = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                                let objs = cr_msg.content.get_list_response().res.unwrap();
                                let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                                let pods_or_none = objects_to_pods(objs);
                                let pods = pods_or_none.unwrap();
                                let filtered_pods = filter_pods(pods, triggering_cr);

                                assert forall |i| #![auto]
                                    0 <= i < filtered_pods.len()
                                    && invariant_matrix(key, s)
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
                                        let req_msg = s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg->0;
                                        &&& s.in_flight().contains(cr_msg)
                                        &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                                        &&& cr_msg.src.is_APIServer()
                                        &&& resp_msg_matches_req_msg(cr_msg, req_msg)});

                                    seq_filter_contains_implies_seq_contains(
                                        pods,
                                        |pod: PodView|
                                        pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                                        && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                        && pod.metadata.deletion_timestamp is None,
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
                            if s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
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
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                                assert forall |msg| {
                                    let req_msg = s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg->0;
                                    &&& #[trigger] s_prime.in_flight().contains(msg)
                                    &&& s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                                    &&& msg.src.is_APIServer()
                                    &&& resp_msg_matches_req_msg(msg, req_msg)
                                    &&& is_ok_resp(msg.content.get_APIResponse_0())
                                    &&& invariant_matrix(key, s)
                                    &&& stronger_next(s, s_prime)
                                } implies {
                                    let resp_objs = msg.content.get_list_response().res.unwrap();
                                    &&& msg.content.is_list_response()
                                    &&& msg.content.get_list_response().res is Ok
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
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                            let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                            assert forall |msg| {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg->0;
                                &&& #[trigger] s_prime.in_flight().contains(msg)
                                &&& s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                                &&& msg.src.is_APIServer()
                                &&& resp_msg_matches_req_msg(msg, req_msg)
                                &&& is_ok_resp(msg.content.get_APIResponse_0())
                                &&& invariant_matrix(key, s)
                                &&& stronger_next(s, s_prime)
                            } implies {
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                &&& msg.content.is_list_response()
                                &&& msg.content.get_list_response().res is Ok
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
                                        invariant_matrix(key, s)
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
                                            && invariant_matrix(key, s)
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
                                        &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                                        &&& msg.src.is_APIServer()
                                        &&& resp_msg_matches_req_msg(msg, req_msg)
                                    };
                                    if msg_antecedent {
                                        let resp_objs = msg.content.get_list_response().res.unwrap();
                                        assert({
                                            &&& msg.content.is_list_response()
                                            &&& msg.content.get_list_response().res is Ok
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
                            let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                            assert forall |msg| {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg->0;
                                &&& #[trigger] s_prime.in_flight().contains(msg)
                                &&& s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                                &&& msg.src.is_APIServer()
                                &&& resp_msg_matches_req_msg(msg, req_msg)
                                &&& is_ok_resp(msg.content.get_APIResponse_0())
                                &&& invariant_matrix(key, s)
                                &&& stronger_next(s, s_prime)
                            } implies {
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                &&& msg.content.is_list_response()
                                &&& msg.content.get_list_response().res is Ok
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
                    _ => {
                        let state = VReplicaSetReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                        let triggering_cr = VReplicaSetView::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                        if state.reconcile_step.is_AfterListPods() {
                            assert forall |msg| {
                                let req_msg = s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg->0;
                                &&& invariant_matrix(key, s)
                                &&& stronger_next(s, s_prime)
                                &&& #[trigger] s_prime.in_flight().contains(msg)
                                &&& s_prime.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                                &&& msg.src.is_APIServer()
                                &&& resp_msg_matches_req_msg(msg, req_msg)
                                &&& is_ok_resp(msg.content.get_APIResponse_0())
                            } implies {
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                &&& msg.content.is_list_response()
                                &&& msg.content.get_list_response().res is Ok
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
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                if s.in_flight().contains(msg) {} // needed for trigger.
                            }
                        }
                    }
                }
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}

pub proof fn lemma_always_every_msg_from_vrs_controller_carries_vrs_key(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
    ensures
        spec.entails(always(lift_state(every_msg_from_vrs_controller_carries_vrs_key(controller_id)))),
{
    let inv = every_msg_from_vrs_controller_carries_vrs_key(controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(
        spec, controller_id
    );

    VReplicaSetReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();

    assert forall|s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime)
        implies inv(s_prime) by {
        let new_msgs = s_prime.in_flight().sub(s.in_flight());

        assert forall |msg: Message|
            inv(s)
            && #[trigger] s_prime.in_flight().contains(msg)
            && msg.src.is_Controller()
            && msg.src.get_Controller_0() == controller_id
            implies msg.src.get_Controller_1().kind == VReplicaSetView::kind() by {
            if new_msgs.contains(msg) {
            } else {
                if s.in_flight().contains(msg) {
                    // Empty if statement required to trigger quantifiers.
                }
            }
        }
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

pub proof fn lemma_eventually_always_vrs_in_schedule_does_not_have_deletion_timestamp(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vrs)))),
    spec.entails(cluster.schedule_controller_reconcile().weak_fairness((controller_id, vrs.object_ref()))),
    cluster.controller_models.contains_key(controller_id),
    cluster.controller_models[controller_id].reconcile_model.kind == VReplicaSetView::kind(),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vrs_in_schedule_does_not_have_deletion_timestamp(vrs, controller_id))))),
{
    let p_prime = |s: ClusterState| Cluster::desired_state_is(vrs)(s);
    let q = vrs_in_schedule_does_not_have_deletion_timestamp(vrs, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::desired_state_is(vrs)(s)
        &&& Cluster::desired_state_is(vrs)(s_prime)
    };
    always_to_always_later(spec, lift_state(Cluster::desired_state_is(vrs)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::desired_state_is(vrs)),
        later(lift_state(Cluster::desired_state_is(vrs)))
    );

    cluster.schedule_controller_reconcile().wf1(
        (controller_id, vrs.object_ref()),
        spec,
        stronger_next,
        p_prime,
        q
    );
    leads_to_stable(spec, lift_action(stronger_next), lift_state(p_prime), lift_state(q));

    temp_pred_equality(
        true_pred().and(lift_state(p_prime)),
        lift_state(p_prime)
    );
    pack_conditions_to_spec(spec, lift_state(p_prime), true_pred(), always(lift_state(q)));
    temp_pred_equality(
        lift_state(p_prime),
        lift_state(Cluster::desired_state_is(vrs))
    );
    simplify_predicate(spec, always(lift_state(p_prime)));
}

// TODO: investigate flaky proof.
#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(vrs_in_schedule_does_not_have_deletion_timestamp(vrs, controller_id)))),
    spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))),
    cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id))))),
{
    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref());
    let q = vrs_in_ongoing_reconciles_does_not_have_deletion_timestamp(vrs, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& vrs_in_schedule_does_not_have_deletion_timestamp(vrs, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(vrs_in_schedule_does_not_have_deletion_timestamp(vrs, controller_id))
    );

    leads_to_weaken(
        spec,
        true_pred(), lift_state(reconcile_idle),
        true_pred(), lift_state(q)
    );
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(q));
}

// TODO: investigate flaky proof.
#[verifier(spinoff_prover)]
pub proof fn lemma_always_there_is_no_request_msg_to_external_from_controller(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
ensures
    spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
{
    let inv = Cluster::there_is_no_request_msg_to_external_from_controller(controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(
        spec, controller_id
    );

    VReplicaSetReconcileState::marshal_preserves_integrity();
    VReplicaSetView::marshal_preserves_integrity();

    assert forall|s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime)
        implies inv(s_prime) by {
        let new_msgs = s_prime.in_flight().sub(s.in_flight());

        assert forall |msg: Message|
            inv(s)
            && #[trigger] s_prime.in_flight().contains(msg)
            && msg.src.is_controller_id(controller_id)
            implies msg.dst != HostId::External(controller_id) by {
            if s.in_flight().contains(msg) {
                // Empty if statement required to trigger quantifiers.
            }
            if new_msgs.contains(msg) {
                // Empty if statement required to trigger quantifiers.
            }
        }
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

}
