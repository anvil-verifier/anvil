// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, cluster::*, controller::types::*, message::*,
    builtin_controllers::types::*,
};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    proof::{
        guarantee,
        helper_invariants::predicate::*, helper_lemmas, liveness::api_actions::*, predicate::*,
    },
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*};
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
        spec.entails(always(lift_state(desired_state_is(vrs)))),
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
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))))),
{
    let requirements = |msg: Message, s: ClusterState| {
        &&& s.in_flight().contains(msg)
        &&& msg.src != HostId::Controller(controller_id, vrs.object_ref())
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
    } ==> {
        let content = msg.content;
        match content->APIRequest_0 {
            APIRequest::CreateRequest(req) => no_other_pending_create_request_interferes_with_vrs_reconcile(req, vrs)(s),
            APIRequest::UpdateRequest(req) => no_other_pending_update_request_interferes_with_vrs_reconcile(req, vrs)(s),
            APIRequest::UpdateStatusRequest(req) => no_other_pending_update_status_request_interferes_with_vrs_reconcile(req, vrs)(s),
            APIRequest::GetThenUpdateRequest(req) => no_other_pending_get_then_update_request_interferes_with_vrs_reconcile(req, vrs)(s),
            APIRequest::DeleteRequest(req) => no_other_pending_delete_request_interferes_with_vrs_reconcile(req, vrs)(s),
            APIRequest::GetThenDeleteRequest(req) => no_other_pending_get_then_delete_request_interferes_with_vrs_reconcile(req, vrs)(s),
            APIRequest::GetThenUpdateStatusRequest(req) => no_other_pending_get_then_update_status_request_interferes_with_vrs_reconcile(req, vrs)(s),
            _ => true,
        }
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        &&& s.in_flight().contains(msg)
        &&& msg.src != HostId::Controller(controller_id, vrs.object_ref())
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& desired_state_is(vrs)(s)
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
        lift_state(desired_state_is(vrs)),
        lifted_vrs_rely_condition_action(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
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

#[verifier(rlimit(50))]
#[verifier(spinoff_prover)]
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
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>(spec);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(spec, controller_id);
    guarantee::lemma_always_local_pods_have_vrs_prefix(spec, cluster, controller_id);

    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)(s)
        &&& guarantee::local_pods_have_vrs_prefix(controller_id)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id)),
        lift_state(guarantee::local_pods_have_vrs_prefix(controller_id))
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
                    &&& msg.content is APIRequest
                    &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_reconcile_create_request_only_interferes_with_itself(req, vrs),
                    APIRequest::GetThenDeleteRequest(req) => vrs_reconcile_get_then_delete_request_only_interferes_with_itself(req, vrs),
                    APIRequest::GetThenUpdateStatusRequest(req) => vrs_reconcile_get_then_update_status_request_only_interferes_with_itself(req, vrs),
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
                    &&& msg.content is APIRequest
                    &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_reconcile_create_request_only_interferes_with_itself(req, vrs),
                    APIRequest::GetThenDeleteRequest(req) => vrs_reconcile_get_then_delete_request_only_interferes_with_itself(req, vrs),
                    APIRequest::GetThenUpdateStatusRequest(req) => vrs_reconcile_get_then_update_status_request_only_interferes_with_itself(req, vrs),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.

                    if cr_key == vrs.object_ref() && id == controller_id {
                        // init
                        if !s.ongoing_reconciles(controller_id).contains_key(cr_key) {
                            assert(s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg is None);
                        } else {
                            assert(VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr) is Ok);
                            let new_msgs = s_prime.in_flight().sub(s.in_flight());
                            let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                            if new_msgs.contains(msg) {
                                assert(msg.content is APIRequest);
                                let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                                match msg.content->APIRequest_0 {
                                    APIRequest::CreateRequest(req) => {
                                        assert(req.obj == make_pod(triggering_cr).marshal());
                                        assert(req.key().namespace == triggering_cr.metadata.namespace.unwrap());
                                        assert(req.key().namespace == vrs.metadata.namespace.unwrap());
                                        assert(req.obj.kind == Kind::PodKind);
                                        // owner_references from make_pod
                                        let pod = make_pod(triggering_cr);
                                        assert(pod.metadata.owner_references == Some(make_owner_references(triggering_cr)));
                                        assert(make_owner_references(triggering_cr) == seq![triggering_cr.controller_owner_ref()]);
                                        let owner_ref = triggering_cr.controller_owner_ref();
                                        assert(owner_ref.controller == Some(true));
                                        assert(owner_ref.kind == VReplicaSetView::kind());
                                        assert(owner_ref.name == triggering_cr.metadata.name->0);
                                        assert(owner_ref.name == vrs.object_ref().name);
                                    },
                                    APIRequest::GetThenDeleteRequest(req) => {
                                        assert(req.owner_ref == triggering_cr.controller_owner_ref());
                                        assert(req.key.kind == Kind::PodKind);
                                        assert(req.key.namespace == triggering_cr.metadata.namespace.unwrap());
                                        assert(req.key.namespace == vrs.metadata.namespace.unwrap());
                                        assert(req.owner_ref.controller == Some(true));
                                        assert(req.owner_ref.kind == VReplicaSetView::kind());
                                        assert(req.owner_ref.name == vrs.object_ref().name);
                                    },
                                    APIRequest::GetThenUpdateStatusRequest(req) => {
                                        assert(req.key() == triggering_cr.object_ref());
                                        assert(req.key() == vrs.object_ref());
                                    },
                                    APIRequest::ListRequest(_) => {},
                                    _ => {
                                        assert(false);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            _ => {
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_reconcile_create_request_only_interferes_with_itself(req, vrs),
                    APIRequest::GetThenDeleteRequest(req) => vrs_reconcile_get_then_delete_request_only_interferes_with_itself(req, vrs),
                    APIRequest::GetThenUpdateStatusRequest(req) => vrs_reconcile_get_then_update_status_request_only_interferes_with_itself(req, vrs),
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
        msg.content is APIRequest ==>
            match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => vrs_rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) => vrs_rely_get_then_update_req(req)(s),
                _ => true,
            }
    };

    // To make our job easier, we carry a few stronger conditions on what
    // in the cluster can send updates.
    let stronger_requirements = |msg: Message, s: ClusterState| {
        msg.content is APIRequest ==>
            match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) =>
                    msg.src is Controller
                    && !msg.src.is_controller_id(controller_id)
                    && vrs_rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) =>
                    msg.src is Controller
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
            if msg.content is APIRequest
                && msg.content->APIRequest_0 is UpdateRequest {
                if msg.src is Controller {
                    let id = msg.src->Controller_0;
                    PodView::marshal_preserves_integrity();
                    VReplicaSetReconcileState::marshal_preserves_integrity();
                    if id != controller_id {
                        assert(vrs_rely(id)(s_prime));
                    } else {
                        assert(!s.in_flight().contains(msg));
                    }
                }
            } else if msg.content is APIRequest
                && msg.content->APIRequest_0 is GetThenUpdateRequest {
                if msg.src is Controller {
                    let id = msg.src->Controller_0;
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

#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
#[verifier(external_body)]
pub proof fn lemma_eventually_always_garbage_collector_does_not_delete_vrs_pods(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(vrs)))),
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
            &&& msg.src is BuiltinController
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
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
        &&& msg.src is BuiltinController
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& desired_state_is(vrs)(s)
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
        lift_state(desired_state_is(vrs)),
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
            &&& !(msg.src is Controller || msg.src is BuiltinController)
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
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
            && msg.src is Controller
            && msg.src->Controller_0 == controller_id
            implies msg.src->Controller_1.kind == VReplicaSetView::kind() by {
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

pub proof fn lemma_eventually_always_vrs_in_schedule_has_only_one_owner_ref_and_no_deletion_timestamp(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(desired_state_is(vrs)))),
    spec.entails(cluster.schedule_controller_reconcile().weak_fairness((controller_id, vrs.object_ref()))),
    cluster.controller_models.contains_key(controller_id),
    cluster.controller_models[controller_id].reconcile_model.kind == VReplicaSetView::kind(),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vrs_in_schedule_has_only_one_owner_ref_and_no_deletion_timestamp(vrs, controller_id))))),
{
    let p_prime = |s: ClusterState| desired_state_is(vrs)(s);
    let q = vrs_in_schedule_has_only_one_owner_ref_and_no_deletion_timestamp(vrs, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& desired_state_is(vrs)(s)
        &&& desired_state_is(vrs)(s_prime)
    };
    always_to_always_later(spec, lift_state(desired_state_is(vrs)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(desired_state_is(vrs)),
        later(lift_state(desired_state_is(vrs)))
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
        lift_state(desired_state_is(vrs))
    );
    simplify_predicate(spec, always(lift_state(p_prime)));
}

pub proof fn lemma_eventually_always_vrs_in_ongoing_reconciles_has_only_one_owner_ref_and_no_deletion_timestamp(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(desired_state_is(vrs)))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(vrs_in_schedule_has_only_one_owner_ref_and_no_deletion_timestamp(vrs, controller_id)))),
    spec.entails(always(lift_state(no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))),
    spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())))),
    cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vrs_in_ongoing_reconciles_has_only_one_owner_ref_and_no_deletion_timestamp(vrs, controller_id))))),
{
    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref());
    let q = vrs_in_ongoing_reconciles_has_only_one_owner_ref_and_no_deletion_timestamp(vrs, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& desired_state_is(vrs)(s)
        &&& desired_state_is(vrs)(s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& vrs_in_schedule_has_only_one_owner_ref_and_no_deletion_timestamp(vrs, controller_id)(s)
        &&& no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s)
    };
    always_to_always_later(spec, lift_state(desired_state_is(vrs)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(desired_state_is(vrs)),
        later(lift_state(desired_state_is(vrs))),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(vrs_in_schedule_has_only_one_owner_ref_and_no_deletion_timestamp(vrs, controller_id)),
        lift_state(no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id))
    );
    leads_to_weaken(
        spec,
        true_pred(), lift_state(reconcile_idle),
        true_pred(), lift_state(q)
    );
    assert forall |s, s_prime| q(s) && #[trigger] stronger_next(s, s_prime) implies q(s_prime) by {
        if s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref()) {}
    }
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
