#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::InstalledTypes}, 
    cluster::*, 
    message::*,
    controller::types::*,
};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    trusted::{
        liveness_theorem::*, 
        rely_guarantee::*, 
        spec_types::*, 
        step::*,
        util::*,
    },
    proof::{
        predicate::*, 
        helper_invariants::predicate::*,
        helper_lemmas
    },
};
use crate::vreplicaset_controller::{
    trusted::{
        spec_types::*,
    }
};
use crate::vstd_ext::{seq_lib::*, set_lib::*, string_view::int_to_string_view};
use vstd::{map_lib::*, multiset::*, prelude::*};

verus! {

pub proof fn lemma_eventually_always_no_other_pending_request_interferes_with_vd_reconcile(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(desired_state_is(vd)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(tla_forall(|vd: VDeploymentView| lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd))))),
        spec.entails(always(lift_state(garbage_collector_does_not_delete_vd_vrs_objects(vd)))),
        spec.entails(always(lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()))),
        spec.entails(always(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)))),
        spec.entails(always(lift_state(vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id))))),
{
    let requirements = |msg: Message, s: ClusterState| {
        &&& s.in_flight().contains(msg)
        &&& msg.src != HostId::Controller(controller_id, vd.object_ref())
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
    } ==> {
        let content = msg.content;
        match content->APIRequest_0 {
            APIRequest::CreateRequest(req) => no_other_pending_create_request_interferes_with_vd_reconcile(req, vd)(s),
            APIRequest::UpdateRequest(req) => no_other_pending_update_request_interferes_with_vd_reconcile(req, vd)(s),
            APIRequest::UpdateStatusRequest(req) => no_other_pending_update_status_request_interferes_with_vd_reconcile(req, vd)(s),
            APIRequest::GetThenUpdateRequest(req) => no_other_pending_get_then_update_request_interferes_with_vd_reconcile(req, vd)(s),
            APIRequest::DeleteRequest(req) => no_other_pending_delete_request_interferes_with_vd_reconcile(req, vd)(s),
            APIRequest::GetThenDeleteRequest(req) => no_other_pending_get_then_delete_request_interferes_with_vd_reconcile(req, vd)(s),
            _ => true,
        }
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        &&& s.in_flight().contains(msg)
        &&& msg.src != HostId::Controller(controller_id, vd.object_ref())
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& desired_state_is(vd)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s_prime)
        &&& Cluster::etcd_is_finite()(s)
        &&& vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)(s)
        &&& garbage_collector_does_not_delete_vd_vrs_objects(vd)(s)
        &&& garbage_collector_does_not_delete_vd_vrs_objects(vd)(s_prime)
        &&& no_pending_mutation_request_not_from_controller_on_vrs_objects()(s)
        &&& no_pending_mutation_request_not_from_controller_on_vrs_objects()(s_prime)
        &&& every_msg_from_vd_controller_carries_vd_key(controller_id)(s)
        &&& every_msg_from_vd_controller_carries_vd_key(controller_id)(s_prime)
        &&& forall |vd: VDeploymentView| #[trigger] vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& forall |vd: VDeploymentView| #[trigger] vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s_prime)
    };

    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            VReplicaSetView::marshal_preserves_integrity();
            VDeploymentReconcileState::marshal_preserves_integrity();
            VDeploymentView::marshal_preserves_integrity();

            if requirements_antecedent(msg, s_prime) {
                // approach: dissect msg by its sender and content, and invoke the appropriate invariant
                // (instantiated on both s and s_prime).

                match msg.src {
                    HostId::Controller(id, cr_key) => {
                        if id != controller_id {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(vd_rely(id)(s_prime));
                        } else {
                            let havoc_vd = make_vd(); // havoc for VDeploymentView
                            let vd_with_key = VDeploymentView {
                                metadata: ObjectMetaView {
                                    name: Some(cr_key.name),
                                    namespace: Some(cr_key.namespace),
                                    ..havoc_vd.metadata
                                },
                                ..havoc_vd
                            };
                            assert(cr_key == vd_with_key.object_ref());
                            assert(vd_reconcile_request_only_interferes_with_itself(controller_id, vd_with_key)(s_prime));

                            if msg.content.is_get_then_update_request() && vd.object_ref() != cr_key {
                                let req = msg.content.get_get_then_update_request();
                                let owners = req.obj.metadata.owner_references->0;
                                let controller_owners = owners.filter(
                                    |o: OwnerReferenceView| o.controller is Some && o.controller->0
                                );
                                assert(controller_owners.len() == 1);
                                assert(controller_owners[0].name == vd_with_key.object_ref().name);
                                assert(controller_owners[0].kind == VDeploymentView::kind());
                                if req.key().namespace == vd.object_ref().namespace {
                                    assert(vd_with_key.controller_owner_ref().name != vd.controller_owner_ref().name);
                                    assert(controller_owners[0].name == vd_with_key.controller_owner_ref().name);
                                    assert(!controller_owners.contains(vd.controller_owner_ref()));
                                }
                            }
                        }
                    },
                    _ => {},
                }
           }
        }
    }

    always_to_always_later(spec, lift_state(garbage_collector_does_not_delete_vd_vrs_objects(vd)));
    always_to_always_later(spec, lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()));
    always_to_always_later(spec, lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)));
    helper_lemmas::only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself_action(
        spec, cluster, controller_id
    );
    helper_lemmas::vd_rely_condition_equivalent_to_lifted_vd_rely_condition_action(
        spec, cluster, controller_id
    );
    let only_interferes_with_itself_closure = |vd: VDeploymentView| lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd));

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
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)),
        lift_state(desired_state_is(vd)),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)),
        lift_state(garbage_collector_does_not_delete_vd_vrs_objects(vd)),
        later(lift_state(garbage_collector_does_not_delete_vd_vrs_objects(vd))),
        lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()),
        later(lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects())),
        lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)),
        later(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id))),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

// Havoc function for VDeploymentView.
uninterp spec fn make_vd() -> VDeploymentView;

pub proof fn lemma_always_vd_reconcile_request_only_interferes_with_itself(
    spec: TempPred<ClusterState>, 
    cluster: Cluster, 
    controller_id: int,
    vd: VDeploymentView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    ensures
        spec.entails(always(lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd))))
{
    let invariant = vd_reconcile_request_only_interferes_with_itself(controller_id, vd);

    cluster.lemma_always_cr_states_are_unmarshallable::<VDeploymentReconciler, VDeploymentReconcileState, VDeploymentView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    lemma_always_vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(spec, cluster, controller_id);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VDeploymentView>(spec);

    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)(s)
        &&& vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)(s_prime)
        &&& Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()(s)
    };

    always_to_always_later(spec, lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)));

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)),
        later(lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id))),
        lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>())
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        VDeploymentView::marshal_preserves_integrity();
        VDeploymentReconcileState::marshal_preserves_integrity();
        VReplicaSetView::marshal_preserves_integrity();

        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(req_msg_opt) => {
                let req_msg = req_msg_opt.unwrap();

                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src == HostId::Controller(controller_id, vd.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vd_reconcile_create_request_only_interferes_with_itself(req, vd)(s),
                    APIRequest::GetThenUpdateRequest(req) => vd_reconcile_get_then_update_request_only_interferes_with_itself(req, vd)(s),
                    _ => false, // vd doesn't send other requests (yet).
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
            Step::ControllerStep((id, resp_msg_opt, cr_key_opt)) => {
                let cr_key = cr_key_opt->0;
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src == HostId::Controller(controller_id, vd.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vd_reconcile_create_request_only_interferes_with_itself(req, vd)(s),
                    APIRequest::GetThenUpdateRequest(req) => vd_reconcile_get_then_update_request_only_interferes_with_itself(req, vd)(s),
                    _ => false, // vd doesn't send other requests (yet).
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.

                    if id == controller_id && cr_key == vd.object_ref() {
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());

                        if new_msgs.contains(msg) && msg.content.is_get_then_update_request() {
                            let req = msg.content.get_get_then_update_request();
                            let state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();    

                            if state.reconcile_step == VDeploymentReconcileStepView::AfterListVRS {
                                let list_resp = resp_msg_opt.unwrap().content.get_list_response();
                                let objs = list_resp.res.unwrap();
                                let vrs_list_or_none = objects_to_vrs_list(objs);
                                let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(triggering_cr, vrs_list_or_none->0.filter(|vrs| valid_owned_vrs(vrs, triggering_cr)));

                                // idea: sidestep an explicit proof that the message we send is owned by triggering_cr
                                // by applying the invariant `vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd`
                                // to s_prime.
                                if new_vrs is Some && !match_replicas(triggering_cr, new_vrs->0) {
                                    let state_prime = VDeploymentReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                                    // we need this to trigger the invariant on the post-state.
                                    assert(s_prime.ongoing_reconciles(controller_id).contains_key(cr_key));
                                }
                            }
                            assert(req.owner_ref == triggering_cr.controller_owner_ref());
                            let owners = req.obj.metadata.owner_references->0;
                            let controller_owners = owners.filter(
                                |o: OwnerReferenceView| o.controller is Some && o.controller->0
                            );
                            assert(controller_owners.len() == 1);
                            assert(controller_owners[0] == triggering_cr.controller_owner_ref());
                            assert(controller_owners == seq![triggering_cr.controller_owner_ref()]);
                            assert(controller_owners.contains(triggering_cr.controller_owner_ref()));
                            seq_filter_contains_implies_seq_contains(
                                owners,
                                |o: OwnerReferenceView| o.controller is Some && o.controller->0,
                                triggering_cr.controller_owner_ref(),
                            );
                            assert(req.obj.metadata.owner_references_contains(triggering_cr.controller_owner_ref()));
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
                    &&& msg.src == HostId::Controller(controller_id, vd.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vd_reconcile_create_request_only_interferes_with_itself(req, vd)(s),
                    APIRequest::GetThenUpdateRequest(req) => vd_reconcile_get_then_update_request_only_interferes_with_itself(req, vd)(s),
                    _ => false, // vd doesn't send other requests (yet).
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_no_pending_interfering_update_request(
    spec: TempPred<ClusterState>,
    vd: VDeploymentView,
    cluster: Cluster, 
    controller_id: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(vd)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),

        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(lift_state(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)))),
        spec.entails(always(tla_forall(|vd: VDeploymentView| lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd))))),
        spec.entails(always(lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)))),
        spec.entails(always(lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()))),
        spec.entails(always(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)))),
        spec.entails(always(lift_state(vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_pending_interfering_update_request(vd, controller_id))))),
{
    let requirements = |msg: Message, s: ClusterState| {
        &&& msg.src != HostId::Controller(controller_id, vd.object_ref()) ==>
            match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => vd_rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) => no_other_pending_get_then_update_request_interferes_with_vd_reconcile(req, vd)(s),
                _ => true,
            }
        // If a get-then-update request is issued by vd, the request carried must contain vd's owner reference.
        &&& {
            let req = msg.content.get_get_then_update_request();
            ({
                &&& msg.src == HostId::Controller(controller_id, vd.object_ref())
                &&& msg.content.is_get_then_update_request()
            }) ==> req.owner_ref == vd.controller_owner_ref()
        }
    };

    // To make our job easier, we carry a few stronger conditions on what
    // in the cluster can send updates.
    let stronger_requirements = |msg: Message, s: ClusterState| {
        msg.content is APIRequest ==> {
            &&& msg.src != HostId::Controller(controller_id, vd.object_ref()) ==>
                match msg.content->APIRequest_0 {
                    APIRequest::UpdateRequest(req) =>
                        msg.src is Controller
                        && vd_rely_update_req(req)(s),
                    APIRequest::GetThenUpdateRequest(req) => 
                        msg.src is Controller
                        && no_other_pending_get_then_update_request_interferes_with_vd_reconcile(req, vd)(s),
                    _ => true,
                }
            // If a get-then-update request is issued by vd, the request carried must contain vd's owner reference.
            &&& {
                let req = msg.content.get_get_then_update_request();
                ({
                    &&& msg.src == HostId::Controller(controller_id, vd.object_ref())
                    &&& msg.content.is_get_then_update_request()
                }) ==> req.owner_ref == vd.controller_owner_ref()
            }
        }
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& desired_state_is(vd)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s_prime)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s_prime)
        &&& Cluster::etcd_is_finite()(s)
        &&& vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)(s)
        &&& vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)(s)
        &&& vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)(s)
        &&& vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)(s_prime)
        &&& no_pending_mutation_request_not_from_controller_on_vrs_objects()(s)
        &&& no_pending_mutation_request_not_from_controller_on_vrs_objects()(s_prime)
        &&& every_msg_from_vd_controller_carries_vd_key(controller_id)(s)
        &&& every_msg_from_vd_controller_carries_vd_key(controller_id)(s_prime)
        &&& forall |vd: VDeploymentView| #[trigger] vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& forall |vd: VDeploymentView| #[trigger] vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s_prime)
    };

    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(stronger_requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || stronger_requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies stronger_requirements(msg, s_prime) by {
            VDeploymentReconcileState::marshal_preserves_integrity();
            VDeploymentView::marshal_preserves_integrity();

            if !s.in_flight().contains(msg) {
                if msg.content.is_update_request() {
                    if msg.src is Controller {
                        let id = msg.src->Controller_0;
                        let key = msg.src->Controller_1;
                        if id != controller_id {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(vd_rely(id)(s_prime));
                        }
                    } else {
                        assert(no_pending_mutation_request_not_from_controller_on_vrs_objects()(s_prime));
                    }
                } else if msg.content.is_get_then_update_request() {
                    if msg.src is Controller {
                        let id = msg.src->Controller_0;
                        let key = msg.src->Controller_1;
                        if id != controller_id {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(vd_rely(id)(s_prime));
                        } else if key == vd.object_ref() {
                            assert(msg.src == HostId::Controller(controller_id, vd.object_ref()));
                            assert(vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s_prime));
                        } else {
                            let havoc_vd = make_vd(); // havoc for VDeploymentView
                            let vd_with_key = VDeploymentView {
                                metadata: ObjectMetaView {
                                    name: Some(key.name),
                                    namespace: Some(key.namespace),
                                    ..havoc_vd.metadata
                                },
                                ..havoc_vd
                            };
                            assert(vd_reconcile_request_only_interferes_with_itself(controller_id, vd_with_key)(s_prime));

                            let req = msg.content.get_get_then_update_request();
                            if req.obj.metadata.owner_references is Some && req.key().namespace == vd.object_ref().namespace {
                                assert(vd_with_key.object_ref().name != vd.object_ref().name);

                                // going for a proof of 'Prevents 2)' by contradiction
                                if req.obj.metadata.owner_references->0.contains(vd.controller_owner_ref()) {
                                    let owners = req.obj.metadata.owner_references->0;
                                    let controller_owners = owners.filter(
                                        |o: OwnerReferenceView| o.controller is Some && o.controller->0
                                    );
                                    assert(owners.contains(vd.controller_owner_ref()));
                                    assert(controller_owners.contains(vd.controller_owner_ref()));
                                    assert(controller_owners[0] == vd.controller_owner_ref());

                                    // we have
                                    assert(controller_owners[0].name == vd.object_ref().name);
                                    // but this contradicts
                                    assert(controller_owners[0].name == vd_with_key.object_ref().name);
                                }
                            }
                        }
                    } else {
                        assert(no_pending_mutation_request_not_from_controller_on_vrs_objects()(s_prime));
                    }
                }
            } else {
                if s.in_flight().contains(msg)
                    && msg.content is APIRequest
                    && msg.src is Controller {
                    let id = msg.src->Controller_0;
                    let cr_key = msg.src->Controller_1;
                    if id != controller_id {
                        assert(cluster.controller_models.remove(controller_id).contains_key(id));
                        assert(vd_rely(id)(s_prime));
                    } else {
                        let havoc_vd = make_vd(); // havoc for VDeploymentView
                        let vd_with_key = VDeploymentView {
                            metadata: ObjectMetaView {
                                name: Some(cr_key.name),
                                namespace: Some(cr_key.namespace),
                                ..havoc_vd.metadata
                            },
                            ..havoc_vd
                        };
                        assert(cr_key == vd_with_key.object_ref());
                        assert(vd_reconcile_request_only_interferes_with_itself(controller_id, vd_with_key)(s_prime));
                    }
                }
            }
        }
    }

    always_to_always_later(spec, lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)));
    always_to_always_later(spec, lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()));
    always_to_always_later(spec, lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()));
    always_to_always_later(spec, lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)));
    helper_lemmas::only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself_action(
        spec, cluster, controller_id
    );
    helper_lemmas::vd_rely_condition_equivalent_to_lifted_vd_rely_condition_action(
        spec, cluster, controller_id
    );
    let only_interferes_with_itself_closure = |vd: VDeploymentView| lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd));

    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(stronger_requirements)),
        lift_action(cluster.next()),
        lift_state(desired_state_is(vd)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        later(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)),
        lift_state(vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)),
        lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)),
        later(lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id))),
        lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()),
        later(lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects())),
        lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)),
        later(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id))),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id)
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
        lift_state(no_pending_interfering_update_request(vd, controller_id)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_garbage_collector_does_not_delete_vd_vrs_objects(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(desired_state_is(vd)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
        
        spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
        spec.entails(always(tla_forall(|vd: VDeploymentView| lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd))))),
        spec.entails(always(lift_state(no_pending_interfering_update_request(vd, controller_id)))),
        spec.entails(always(lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()))),
        spec.entails(always(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)))),
        spec.entails(always(lift_state(vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(garbage_collector_does_not_delete_vd_vrs_objects(vd))))),
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
                ||| !(obj.metadata.owner_references_contains(vd.controller_owner_ref())
                        && obj.kind == VReplicaSetView::kind()
                        && obj.metadata.namespace == vd.metadata.namespace)
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
        &&& desired_state_is(vd)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s_prime)
        &&& Cluster::etcd_is_finite()(s)
        &&& vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)(s)
        &&& no_pending_interfering_update_request(vd, controller_id)(s)
        &&& no_pending_mutation_request_not_from_controller_on_vrs_objects()(s)
        &&& no_pending_mutation_request_not_from_controller_on_vrs_objects()(s_prime)
        &&& every_msg_from_vd_controller_carries_vd_key(controller_id)(s)
        &&& every_msg_from_vd_controller_carries_vd_key(controller_id)(s_prime)
        &&& forall |vd: VDeploymentView| #[trigger] vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s)
        &&& forall |vd: VDeploymentView| #[trigger] vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s_prime)
    };

    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger]  #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            VDeploymentView::marshal_preserves_integrity();
            VDeploymentReconcileState::marshal_preserves_integrity();
            VReplicaSetView::marshal_preserves_integrity();

            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::BuiltinControllersStep(..) => {
                    if (!s.in_flight().contains(msg) && requirements_antecedent(msg, s_prime)) {
                        let req = msg.content.get_delete_request();
                        let key = req.key;
                        let obj = s.resources()[key];
                        let owner_references = obj.metadata.owner_references->0;
                        assert(forall |i| #![trigger owner_references[i]] 0 <= i < owner_references.len() ==> {
                            // the referred owner object does not exist in the cluster state
                            ||| !s.resources().contains_key(owner_reference_to_object_reference(owner_references[i], key.namespace))
                            // or it exists but has a different uid
                            // (which means the actual owner was deleted and another object with the same name gets created again)
                            ||| s.resources()[owner_reference_to_object_reference(owner_references[i], key.namespace)].metadata.uid != Some(owner_references[i].uid)
                        });
                        if obj.metadata.owner_references_contains(vd.controller_owner_ref())
                            && obj.kind == Kind::PodKind
                            && obj.metadata.namespace == vd.metadata.namespace {
                            let idx = choose |i| 0 <= i < owner_references.len() && owner_references[i] == vd.controller_owner_ref();
                            assert(s.resources().contains_key(vd.object_ref()));
                        }
                    }
                },
                Step::APIServerStep(req_msg_opt) => {
                    let req_msg = req_msg_opt.unwrap();

                    if requirements_antecedent(msg, s_prime) {
                        if req_msg.content is APIRequest
                            && req_msg.content->APIRequest_0 is UpdateRequest {
                            let req = msg.content.get_delete_request();
                            if req_msg.src is Controller {
                                let id = req_msg.src->Controller_0;
                                let key = req_msg.src->Controller_1;
                                if id != controller_id {
                                    assert(vd_rely(id)(s_prime));
                                } else if key == vd.object_ref() {
                                    assert(req_msg.src == HostId::Controller(controller_id, vd.object_ref()));
                                    assert(vd_reconcile_request_only_interferes_with_itself(controller_id, vd)(s));
                                } else {
                                    let havoc_vd = make_vd(); // havoc for VDeploymentView
                                    let vd_with_key = VDeploymentView {
                                        metadata: ObjectMetaView {
                                            name: Some(key.name),
                                            namespace: Some(key.namespace),
                                            ..havoc_vd.metadata
                                        },
                                        ..havoc_vd
                                    };
                                    assert(vd_reconcile_request_only_interferes_with_itself(controller_id, vd_with_key)(s));
                                }
                            }
                        } else if req_msg.content is APIRequest
                            && req_msg.content->APIRequest_0 is GetThenUpdateRequest {
                            if req_msg.src is Controller {
                                let id = req_msg.src->Controller_0;
                                let key = req_msg.src->Controller_1;
                                if id != controller_id {
                                    assert(vd_rely(id)(s_prime));
                                } else if key == vd.object_ref() {
                                    // the proof requires no body now, but I had to 'debug'
                                    // along different lines from other cases, so I leave this case
                                    // marked.
                                } else {
                                    let havoc_vd = make_vd(); // havoc for VDeploymentView
                                    let vd_with_key = VDeploymentView {
                                        metadata: ObjectMetaView {
                                            name: Some(key.name),
                                            namespace: Some(key.namespace),
                                            ..havoc_vd.metadata
                                        },
                                        ..havoc_vd
                                    };
                                    assert(vd_reconcile_request_only_interferes_with_itself(controller_id, vd_with_key)(s));
                                }
                            }
                        }
                    }
                },
                _ => {}
            }
        }
    }

    always_to_always_later(spec, lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()));
    always_to_always_later(spec, lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)));
    helper_lemmas::only_interferes_with_itself_equivalent_to_lifted_only_interferes_with_itself_action(
        spec, cluster, controller_id
    );
    helper_lemmas::vd_rely_condition_equivalent_to_lifted_vd_rely_condition_action(
        spec, cluster, controller_id
    );
    let only_interferes_with_itself_closure = |vd: VDeploymentView| lift_state(vd_reconcile_request_only_interferes_with_itself(controller_id, vd));

    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(desired_state_is(vd)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())),
        lifted_vd_rely_condition_action(cluster, controller_id),
        lift_state(Cluster::etcd_is_finite()),
        lift_state(vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id)),
        lift_state(no_pending_interfering_update_request(vd, controller_id)),
        lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()),
        later(lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects())),
        lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)),
        later(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id))),
        lifted_vd_reconcile_request_only_interferes_with_itself_action(controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(garbage_collector_does_not_delete_vd_vrs_objects(vd)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_eventually_always_no_pending_mutation_request_not_from_controller_on_vrs_objects(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
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
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects())))),
{
    let requirements = |msg: Message, s: ClusterState| {
        ({
            &&& !(msg.src is Controller || msg.src is BuiltinController)
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
        })
        ==>
        ({
            &&& msg.content.is_create_request() ==> msg.content.get_create_request().key().kind != VReplicaSetView::kind()
            &&& msg.content.is_update_request() ==> msg.content.get_update_request().key().kind != VReplicaSetView::kind()
            // too radical, loosen it later to allow updates on pod status.
            &&& msg.content.is_update_status_request() ==> msg.content.get_update_status_request().key().kind != VReplicaSetView::kind()
            &&& msg.content.is_delete_request() ==> msg.content.get_delete_request().key.kind != VReplicaSetView::kind()
            &&& msg.content.is_get_then_delete_request() ==> msg.content.get_get_then_delete_request().key.kind != VReplicaSetView::kind()
            &&& msg.content.is_get_then_update_request() ==> msg.content.get_get_then_update_request().key().kind != VReplicaSetView::kind()
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
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s_prime)
    };

    helper_lemmas::vd_rely_condition_equivalent_to_lifted_vd_rely_condition_action(
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
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vd_rely_condition_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_always_vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    ensures spec.entails(always(lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)))),
{
    let invariant = vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id);

    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_builtin_object_in_etcd_is_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VDeploymentView>(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>(spec);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(spec, controller_id);
    cluster.lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(spec, controller_id);
    cluster.lemma_always_etcd_is_finite(spec);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id)(s)
        &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)(s)
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
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)),
        lift_state(Cluster::etcd_is_finite())
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| {
            &&& invariant(s)
            &&& stronger_next(s, s_prime)
            &&& #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
        } implies vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd_with_key(controller_id, key, s_prime) by {
            if s.ongoing_reconciles(controller_id).contains_key(key) {
                lemma_vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd_with_key_preserves_from_s_to_s_prime(
                    cluster, controller_id, s, s_prime, key
                );
            } else { // RunScheduledReconcile
                VDeploymentView::marshal_preserves_integrity();
                VDeploymentReconcileState::marshal_preserves_integrity();
                let triggering_cr = VDeploymentView::unmarshal(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                assert(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(triggering_cr, controller_id)(s_prime));
                helper_lemmas::lemma_cr_fields_eq_to_cr_predicates_eq(triggering_cr, controller_id, s_prime);
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}

#[verifier(external_body)]
// see https://github.com/verus-lang/verus/issues/2038
// currently every branch in match is proved, but the combination of them fails
// we need to fix this after that feature to isolate reasoning about different branches is added,
// or separate this proof into multiple sub proofs as the last resort
proof fn lemma_vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd_with_key_preserves_from_s_to_s_prime(
    cluster: Cluster, controller_id: int, s: ClusterState, s_prime: ClusterState, key: ObjectRef
)
    requires
        cluster.next()(s, s_prime),
        Cluster::there_is_the_controller_state(controller_id)(s),
        Cluster::every_in_flight_msg_has_unique_id()(s),
        Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_builtin_object_in_etcd_is_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
        Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id)(s),
        Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)(s),
        Cluster::etcd_is_finite()(s),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd_with_key(controller_id, key, s),
        s.ongoing_reconciles(controller_id).contains_key(key),
        s_prime.ongoing_reconciles(controller_id).contains_key(key),
    ensures vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd_with_key(controller_id, key, s_prime),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    VDeploymentView::marshal_preserves_integrity();
    if s.ongoing_reconciles(controller_id).contains_key(key) {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        let state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
        let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
        let controller_owner_singleton = seq![triggering_cr.controller_owner_ref()];
        let reconcile_step = state.reconcile_step;
        match step {
            Step::ControllerStep((id, _, cr_key_opt)) => {
                let cr_key = cr_key_opt->0;
                if id == controller_id && cr_key == key {
                    let cr_msg = step->ControllerStep_0.1->0;
                    if reconcile_step == VDeploymentReconcileStepView::AfterListVRS && is_ok_resp(cr_msg.content->APIResponse_0) {
                        let req_msg = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0;
                        let objs = cr_msg.content.get_list_response().res.unwrap();
                        let vrs_list_or_none = objects_to_vrs_list(objs);
                        let vrs_list = vrs_list_or_none.unwrap();
                        let filtered_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, triggering_cr));
                        let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(triggering_cr, filtered_vrs_list);
                        assert({
                            &&& s.in_flight().contains(cr_msg)
                            &&& cr_msg.src is APIServer
                            &&& resp_msg_matches_req_msg(cr_msg, req_msg)
                            &&& is_ok_resp(cr_msg.content->APIResponse_0)
                        });
                        assert(vrs_list_or_none is Some);
                        assert forall |i| #![trigger filtered_vrs_list[i]] 0 <= i < filtered_vrs_list.len() implies {
                            let controller_owners = filtered_vrs_list[i].metadata.owner_references->0.filter(controller_owner_filter());
                            &&& filtered_vrs_list[i].metadata.owner_references is Some
                            &&& filtered_vrs_list[i].object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                            &&& controller_owners == controller_owner_singleton
                        } by {
                            seq_filter_contains_implies_seq_contains(
                                vrs_list,
                                |vrs: VReplicaSetView| valid_owned_vrs(vrs, triggering_cr),
                                filtered_vrs_list[i]
                            );
                            // Show that vrs_list[idx1] and filtered_vrs_list[i] have the same metadata.
                            let idx1 = choose |j| 0 <= j < vrs_list.len() && vrs_list[j] == filtered_vrs_list[i];
                            assert(vrs_list[idx1].metadata == filtered_vrs_list[i].metadata);
                            assert(objs.filter(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err()).len() == 0 );
                            assert(objs.len() == vrs_list.len());
                            // Show that vrs_list[idx1] and objs[idx1] have the same metadata.
                            seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                objs, |o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err()
                            );
                            assert(objs.contains(objs[idx1]));
                            assert(VReplicaSetView::unmarshal(objs[idx1]).is_ok());
                            let unwrap_obj = |o: DynamicObjectView| VReplicaSetView::unmarshal(o).unwrap();
                            assert(vrs_list == objs.map_values(unwrap_obj));
                            assert(objs.contains(objs[idx1]));
                            assert(objs[idx1].metadata == vrs_list[idx1].metadata);
                            // Show owner reference properties.
                            let controller_owners = filtered_vrs_list[i].metadata.owner_references->0.filter(controller_owner_filter());
                            assert(triggering_cr.controller_owner_ref().controller is Some);
                            assert(triggering_cr.controller_owner_ref().controller->0);
                            assert(controller_owners.contains(triggering_cr.controller_owner_ref()));
                            assert(controller_owners.len() == 1);
                            assert(controller_owners[0] == triggering_cr.controller_owner_ref());
                            assert(controller_owners == controller_owner_singleton);
                        }
                        if new_vrs is Some {
                            let owners = new_vrs->0.metadata.owner_references->0;
                            let controller_owners = owners.filter(controller_owner_filter());
                            assert(filtered_vrs_list.contains(new_vrs->0)) by {
                                seq_filter_is_a_subset_of_original_seq(
                                    filtered_vrs_list,
                                    match_template_without_hash(triggering_cr.spec.template)
                                );
                                let nonempty_vrs_filter = |vrs: VReplicaSetView| vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0;
                                seq_filter_is_a_subset_of_original_seq(
                                    filtered_vrs_list.filter(match_template_without_hash(triggering_cr.spec.template)),
                                    nonempty_vrs_filter
                                );
                            }
                            assert(controller_owners == controller_owner_singleton);
                        }
                        assert forall |i| #![trigger old_vrs_list[i]] 0 <= i < old_vrs_list.len() implies {
                            let controller_owners = old_vrs_list[i].metadata.owner_references->0.filter(controller_owner_filter());
                            &&& old_vrs_list[i].metadata.owner_references is Some
                            &&& old_vrs_list[i].object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                            &&& controller_owners == controller_owner_singleton
                        } by {
                            assert(old_vrs_list.contains(old_vrs_list[i]));
                            seq_filter_contains_implies_seq_contains(
                                filtered_vrs_list,
                                |vrs: VReplicaSetView| {
                                    &&& new_vrs is None || vrs.metadata.uid != new_vrs->0.metadata.uid
                                    &&& vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0
                                },
                                old_vrs_list[i]
                            );
                        }
                    }
                    if reconcile_step == VDeploymentReconcileStepView::AfterCreateNewVRS && is_ok_resp(cr_msg.content->APIResponse_0) {
                        let resp_obj = cr_msg.content.get_create_response().res.unwrap();
                        let new_vrs = VReplicaSetView::unmarshal(resp_obj)->Ok_0;
                        let controller_owners = new_vrs.metadata.owner_references->0.filter(controller_owner_filter());
                        assert({
                            &&& new_vrs.metadata.owner_references is Some
                            &&& new_vrs.object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                            &&& controller_owners == controller_owner_singleton
                        });
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
                    if state.reconcile_step == VDeploymentReconcileStepView::AfterCreateNewVRS || state.reconcile_step == VDeploymentReconcileStepView::AfterListVRS {
                        let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                        assert(forall |msg| {
                            &&& #[trigger] s_prime.in_flight().contains(msg)
                            &&& msg.src is APIServer
                            &&& resp_msg_matches_req_msg(msg, req_msg)
                        } ==> s.in_flight().contains(msg));
                    }
                }
            },
            Step::APIServerStep(req_msg_opt) => {
                let current_req_msg = req_msg_opt.unwrap();
                let new_msgs = s_prime.in_flight().sub(s.in_flight());
                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                let well_formed_resp_objs = |resp_objs: Seq<DynamicObjectView>| (forall |i| #![trigger resp_objs[i]] 0 <= i < resp_objs.len() ==> {
                    let owners = resp_objs[i].metadata.owner_references->0;
                    let controller_owners = owners.filter(controller_owner_filter());
                    &&& resp_objs[i].metadata.namespace.is_some()
                    &&& resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                    &&& resp_objs[i].kind == VReplicaSetView::kind()
                    &&& resp_objs[i].metadata.owner_references is Some ==> controller_owners.len() <= 1
                });
                if state.reconcile_step == VDeploymentReconcileStepView::AfterListVRS {
                    assert forall |msg| {
                        &&& #[trigger] s_prime.in_flight().contains(msg)
                        &&& msg.src is APIServer
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                        &&& is_ok_resp(msg.content->APIResponse_0)
                    } implies {
                        let resp_objs = msg.content.get_list_response().res.unwrap();
                        &&& resp_objs.filter(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err()).len() == 0 
                        &&& well_formed_resp_objs(resp_objs)
                    } by {
                        if (new_msgs.contains(msg)) {
                            if current_req_msg == req_msg {
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                assert forall |o: DynamicObjectView| #[trigger] resp_objs.contains(o)
                                implies !VReplicaSetView::unmarshal(o).is_err() by {
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
                                    |o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err()
                                );
                                assert forall |i| #![trigger resp_objs[i]] 0 <= i < resp_objs.len() implies {
                                    let controller_owners = resp_objs[i].metadata.owner_references->0.filter(controller_owner_filter());
                                    &&& resp_objs[i].metadata.namespace.is_some()
                                    &&& resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                                    &&& resp_objs[i].kind == VReplicaSetView::kind()
                                    &&& resp_objs[i].metadata.owner_references is Some ==> controller_owners.len() <= 1
                                } by {
                                    let selector = |o: DynamicObjectView| {
                                        &&& o.object_ref().namespace == req_msg.content.get_list_request().namespace
                                        &&& o.object_ref().kind == req_msg.content.get_list_request().kind
                                    };
                                    let selected_elements = s.resources().values().filter(selector);
                                    lemma_values_finite(s.resources());
                                    element_in_seq_exists_in_original_finite_set(selected_elements, resp_objs[i]);
                                    lemma_filter_set(s.resources().values(), selector);
                                }
                            } else {
                                assert(s.in_flight().contains(current_req_msg));
                                assert(current_req_msg.rpc_id != req_msg.rpc_id);
                            }
                        } else {
                            let msg_antecedent = {
                                &&& s.in_flight().contains(msg)
                                &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                                &&& msg.src is APIServer
                                &&& resp_msg_matches_req_msg(msg, req_msg)
                            };
                            if msg_antecedent {
                                let resp_objs = msg.content.get_list_response().res.unwrap();
                                assert({
                                    &&& msg.content.is_list_response()
                                    &&& msg.content.get_list_response().res is Ok
                                    &&& resp_objs.filter(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err()).len() == 0
                                });
                                assert(well_formed_resp_objs(resp_objs));
                            }
                        }
                    }
                }
                // similar to api_actions::lemma_create_new_vrs_request_returns_ok
                if state.reconcile_step == VDeploymentReconcileStepView::AfterCreateNewVRS {
                    assert forall |msg| {
                        &&& #[trigger] s_prime.in_flight().contains(msg)
                        &&& msg.src is APIServer
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                        &&& is_ok_resp(msg.content->APIResponse_0)
                    } implies {
                        let resp_obj = msg.content.get_create_response().res.unwrap();
                        let new_vrs = VReplicaSetView::unmarshal(resp_obj)->Ok_0;
                        let controller_owners = new_vrs.metadata.owner_references->0.filter(controller_owner_filter());
                        &&& VReplicaSetView::unmarshal(resp_obj) is Ok
                        &&& new_vrs.metadata.owner_references is Some
                        &&& new_vrs.object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                        &&& controller_owners == controller_owner_singleton
                    } by {
                        let resp_obj = msg.content.get_create_response().res.unwrap();
                        let new_vrs = VReplicaSetView::unmarshal(resp_obj)->Ok_0;
                        let controller_owners = new_vrs.metadata.owner_references->0.filter(controller_owner_filter());
                        if (new_msgs.contains(msg)) {
                            if current_req_msg == req_msg {
                                // emulate handle_create_request
                                let req = req_msg.content->APIRequest_0->CreateRequest_0;
                                assert(req == CreateRequest {
                                    namespace: triggering_cr.metadata.namespace.unwrap(),
                                    obj: make_replica_set(triggering_cr).marshal()
                                });
                                assert(create_request_admission_check(cluster.installed_types, req, s.api_server) is None) by {
                                    // harden assertions
                                    VReplicaSetView::marshal_preserves_integrity();
                                    assert(req.obj.metadata.generate_name is Some);
                                    assert(req.obj.metadata.namespace is Some);
                                    assert(req.namespace == req.obj.metadata.namespace->0);
                                    assert(unmarshallable_object(req.obj, cluster.installed_types));
                                    assert(req.obj.metadata.name is None);
                                }
                                let generate_name_field = triggering_cr.metadata.name->0 + "-"@ + int_to_string_view(triggering_cr.metadata.resource_version->0);
                                let created_obj = DynamicObjectView {
                                    kind: req.obj.kind,
                                    metadata: ObjectMetaView {
                                        name: Some(generate_name(s.api_server, generate_name_field)),
                                        namespace: Some(req.namespace),
                                        resource_version: Some(s.api_server.resource_version_counter),
                                        uid: Some(s.api_server.uid_counter),
                                        deletion_timestamp: None,
                                        ..req.obj.metadata
                                    },
                                    spec: req.obj.spec,
                                    status: marshalled_default_status(req.obj.kind, cluster.installed_types), // Overwrite the status with the default one
                                };
                                assert(!s.resources().contains_key(created_obj.object_ref())) by {
                                    assert(created_obj.object_ref().name == generate_name(s.api_server, generate_name_field));
                                    generated_name_spec(s.api_server, generate_name_field);
                                    if s.resources().contains_key(created_obj.object_ref()) {
                                        assert(false);
                                    }
                                }
                                assert(created_object_validity_check(created_obj, cluster.installed_types) is None) by {
                                    assert(metadata_validity_check(created_obj) is None) by {
                                        assert(created_obj.metadata.owner_references is Some);
                                        assert(created_obj.metadata.owner_references->0.len() == 1);
                                    }
                                    assert(valid_object(created_obj, cluster.installed_types));
                                }
                                assert(resp_obj == created_obj);
                                assert(resp_obj.kind == VReplicaSetView::kind());
                                assert(resp_obj.metadata.owner_references is Some);
                                assert(resp_obj.metadata.owner_references->0.filter(controller_owner_filter()) == controller_owner_singleton) by {
                                    assert(make_replica_set(triggering_cr).metadata.owner_references == Some(controller_owner_singleton));
                                    lemma_filter_push(Seq::empty(), controller_owner_filter(), triggering_cr.controller_owner_ref());
                                    assert(req.obj.metadata.owner_references->0.filter(controller_owner_filter()) == controller_owner_singleton);
                                }
                                assert(resp_obj.metadata == new_vrs.metadata);
                            } else {
                                assert(s.in_flight().contains(current_req_msg));
                                assert(current_req_msg.rpc_id != req_msg.rpc_id);
                            }
                        }
                    }
                }
            },
            _ => {
                let req_msg = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                if state.reconcile_step == VDeploymentReconcileStepView::AfterCreateNewVRS
                    || state.reconcile_step == VDeploymentReconcileStepView::AfterListVRS {
                    assert(forall |msg| {
                        &&& #[trigger] s_prime.in_flight().contains(msg)
                        &&& msg.src is APIServer
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                        &&& is_ok_resp(msg.content->APIResponse_0)
                    } ==> s.in_flight().contains(msg));
                }
            }
        }
    }
}

pub proof fn lemma_always_every_msg_from_vd_controller_carries_vd_key(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    ensures
        spec.entails(always(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)))),
{
    let inv = every_msg_from_vd_controller_carries_vd_key(controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(
        spec, controller_id
    );

    VDeploymentReconcileState::marshal_preserves_integrity();
    VDeploymentView::marshal_preserves_integrity();

    assert forall|s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime)
        implies inv(s_prime) by {
        let new_msgs = s_prime.in_flight().sub(s.in_flight());

        assert forall |msg: Message|
            inv(s)
            && #[trigger] s_prime.in_flight().contains(msg)
            && msg.src is Controller
            && msg.src->Controller_0 == controller_id
            implies msg.src->Controller_1.kind == VDeploymentView::kind() by {
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

pub proof fn lemma_eventually_always_vd_in_schedule_does_not_have_deletion_timestamp(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(desired_state_is(vd)))),
    spec.entails(cluster.schedule_controller_reconcile().weak_fairness((controller_id, vd.object_ref()))),
    cluster.controller_models.contains_key(controller_id),
    cluster.controller_models[controller_id].reconcile_model.kind == VDeploymentView::kind(),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id))))),
{
    let p_prime = |s: ClusterState| desired_state_is(vd)(s);
    let q = vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& desired_state_is(vd)(s)
        &&& desired_state_is(vd)(s_prime)
    };
    always_to_always_later(spec, lift_state(desired_state_is(vd)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(desired_state_is(vd)),
        later(lift_state(desired_state_is(vd)))
    );

    cluster.schedule_controller_reconcile().wf1(
        (controller_id, vd.object_ref()),
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
        lift_state(desired_state_is(vd))
    );
    simplify_predicate(spec, always(lift_state(p_prime)));
}

// TODO: investigate flaky proof.
#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id)))),
    spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())))),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id))))),
{
    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref());
    let q = vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id))
    );

    leads_to_weaken(
        spec,
        true_pred(), lift_state(reconcile_idle),
        true_pred(), lift_state(q)
    );
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(q));
}

pub proof fn lemma_always_there_is_no_request_msg_to_external_from_controller(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
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

    VDeploymentReconcileState::marshal_preserves_integrity();
    VDeploymentView::marshal_preserves_integrity();

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

pub proof fn lemma_eventually_always_vd_in_schedule_has_the_same_spec_uid_name_namespace_and_labels_as_vd(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(desired_state_is(vd)))),
    spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vd_in_schedule_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id))))),
{
    let p = |s| desired_state_is(vd)(s);
    let q = vd_in_schedule_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& desired_state_is(vd)(s)
        &&& desired_state_is(vd)(s_prime)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    };
    always_to_always_later(spec, lift_state(desired_state_is(vd)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(desired_state_is(vd)),
        later(lift_state(desired_state_is(vd))),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
    );
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, vd.object_ref(), stronger_next, p, q);
    temp_pred_equality(true_pred().and(lift_state(desired_state_is(vd))), lift_state(p));
    leads_to_by_borrowing_inv(spec, true_pred(), lift_state(q), lift_state(desired_state_is(vd)));
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(q));
}

#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(desired_state_is(vd)))),
    spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(vd_in_schedule_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)))),
    spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, vd.object_ref())))),
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id))))),
{
    let not_scheduled_or_reconcile = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
        &&& !s.scheduled_reconciles(controller_id).contains_key(vd.object_ref())
    };
    let scheduled_and_not_reconcile = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(vd.object_ref())
    };
    always_to_always_later(spec, lift_state(desired_state_is(vd)));
    assert(spec.entails(lift_state(not_scheduled_or_reconcile).leads_to(lift_state(scheduled_and_not_reconcile)))) by {
        let (pre, post) = (not_scheduled_or_reconcile, scheduled_and_not_reconcile);
        let stronger_next = |s, s_prime| {
            &&& cluster.next()(s, s_prime)
            &&& desired_state_is(vd)(s)
            &&& desired_state_is(vd)(s_prime)
            &&& Cluster::there_is_the_controller_state(controller_id)(s)
        };
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(desired_state_is(vd)),
            later(lift_state(desired_state_is(vd))),
            lift_state(Cluster::there_is_the_controller_state(controller_id))
        );
        let stronger_pre = and!(pre, desired_state_is(vd));
        cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, vd.object_ref(), stronger_next, stronger_pre, post);
        temp_pred_equality(lift_state(pre).and(lift_state(desired_state_is(vd))), lift_state(stronger_pre));
        leads_to_by_borrowing_inv(spec, lift_state(pre), lift_state(post), lift_state(desired_state_is(vd)));
    }
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& vd_in_schedule_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(vd_in_schedule_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    assert(spec.entails(lift_state(scheduled_and_not_reconcile).leads_to(lift_state(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id))))) by {
        let pre = scheduled_and_not_reconcile;
        let post = vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id);
        assert(forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, None, Some(vd.object_ref())))(s, s_prime) ==> post(s_prime));
        cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, (None, Some(vd.object_ref())), stronger_next, ControllerStep::RunScheduledReconcile, pre, post);
    }
    leads_to_trans(spec, lift_state(not_scheduled_or_reconcile), lift_state(scheduled_and_not_reconcile), lift_state(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)));
    assert(spec.entails(true_pred().leads_to(always(lift_state(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)))))) by {
        let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()); // Cluster::reconcile_idle
        or_leads_to_combine_and_equality!(
            spec, lift_state(reconcile_idle),
            lift_state(scheduled_and_not_reconcile), lift_state(not_scheduled_or_reconcile);
            lift_state(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id))
        );
        leads_to_trans(spec, true_pred(), lift_state(reconcile_idle), lift_state(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)));
        leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)));
    }
}

pub proof fn lemma_spec_entails_lifted_cluster_invariants_since_reconciliation(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id)))),
ensures
    spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
    spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
    spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)))),
    spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    spec.entails(always(lift_state(Cluster::etcd_objects_have_unique_uids()))),
    spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
    spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()))),
    spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()))),
    spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)))),
    spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
    spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
    spec.entails(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id)))),
    spec.entails(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)))),
    spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
    spec.entails(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
    spec.entails(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)))),
    spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id)))),
    spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
    spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
    spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)))),
    spec.entails(always(lift_state(desired_state_is(vd)))),
    spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vd.object_ref())))),
    spec.entails(always(lift_state(no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id)))),
    spec.entails(always(lift_state(garbage_collector_does_not_delete_vd_vrs_objects(vd)))),
    spec.entails(always(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)))),
    spec.entails(always(lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)))),
    spec.entails(always(lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()))),
    spec.entails(always(lift_state(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)))),
{
    let p = lift_state(cluster_invariants_since_reconciliation(cluster, vd, controller_id));
    always_weaken(spec, p, lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec, p, lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec, p, lift_state(Cluster::pod_monkey_disabled()));
    always_weaken(spec, p, lift_state(Cluster::every_in_flight_msg_has_unique_id()));
    always_weaken(spec, p, lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()));
    always_weaken(spec, p, lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)));
    always_weaken(spec, p, lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_weaken(spec, p, lift_state(Cluster::etcd_objects_have_unique_uids()));
    always_weaken(spec, p, lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()));
    always_weaken(spec, p, lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()));
    always_weaken(spec, p, lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()));
    always_weaken(spec, p, lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)));
    always_weaken(spec, p, lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()));
    always_weaken(spec, p, lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()));
    always_weaken(spec, p, lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VDeploymentView>(controller_id)));
    always_weaken(spec, p, lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)));
    always_weaken(spec, p, lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)));
    always_weaken(spec, p, lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)));
    always_weaken(spec, p, lift_state(Cluster::ongoing_reconciles_is_finite(controller_id)));
    always_weaken(spec, p, lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VDeploymentView>(controller_id)));
    always_weaken(spec, p, lift_state(Cluster::etcd_is_finite()));
    always_weaken(spec, p, lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())));
    always_weaken(spec, p, lift_state(Cluster::there_is_the_controller_state(controller_id)));
    always_weaken(spec, p, lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)));
    always_weaken(spec, p, lift_state(Cluster::cr_states_are_unmarshallable::<VDeploymentReconcileState, VDeploymentView>(controller_id)));
    always_weaken(spec, p, lift_state(desired_state_is(vd)));
    always_weaken(spec, p, lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vd.object_ref())));
    always_weaken(spec, p, lift_state(no_other_pending_request_interferes_with_vd_reconcile(vd, controller_id)));
    always_weaken(spec, p, lift_state(garbage_collector_does_not_delete_vd_vrs_objects(vd)));
    always_weaken(spec, p, lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)));
    always_weaken(spec, p, lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)));
    always_weaken(spec, p, lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()));
    always_weaken(spec, p, lift_state(vd_in_reconciles_has_the_same_spec_uid_name_namespace_and_labels_as_vd(vd, controller_id)));
}
}
