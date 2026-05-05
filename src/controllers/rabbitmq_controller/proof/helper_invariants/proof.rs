// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::predicate::*;
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, owner_reference::*, prelude::*, resource::*, label_selector::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
    api_server::state_machine::*,
};
use crate::kubernetes_cluster::proof::api_server::*;
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::rabbitmq_controller::{
    model::resource::*,
    proof::{
        predicate::*, resource::*, helper_lemmas::*, guarantee::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*, rely_guarantee::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib::*, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};
use crate::reconciler::spec::io::*;

verus! {


pub proof fn lemma_eventually_always_every_valid_resource_update_request_sets_owner_references_to_current_cr_forall(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id, sub_resource, rabbitmq)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id, sub_resource, rabbitmq))))) by {
        lemma_eventually_always_every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id, sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_every_valid_resource_update_request_sets_owner_references_to_current_cr(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)))),
        // rely
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id, sub_resource, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let requirements = |msg: Message, s: ClusterState| {
        let req = msg.content.get_get_then_update_request();
        &&& resource_get_then_update_request_msg(resource_key)(msg) && req.owner_ref.controller == Some(true) && req.owner_ref.kind == RabbitmqClusterView::kind()
        ==> {
            &&& at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
            &&& msg.content.get_get_then_update_request().obj.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
        }
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)(s)
        &&& Cluster::desired_state_is(rabbitmq)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
    };
    assert forall |s, s_prime| #[trigger] stronger_next(s, s_prime)
    implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            let req = msg.content.get_get_then_update_request();
            if resource_get_then_update_request_msg(resource_key)(msg) && req.owner_ref.controller == Some(true) && req.owner_ref.kind == RabbitmqClusterView::kind() {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                if !s.in_flight().contains(msg) {
                    RabbitmqReconcileState::marshal_preserves_integrity();
                    lemma_resource_get_then_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                } else {
                    assert(requirements(msg, s));
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    invariant_n!(spec,
        lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id))),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id))
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);

    temp_pred_equality(
        lift_state(every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id, sub_resource, rabbitmq)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)));
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(100))]
#[verifier(external_body)] // FIXME: add stronger internal-rely-guarantee?
pub proof fn lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
{
    // they are proved together because there are dependencies in between
    let inv = resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq);
    let resource_key = get_request(sub_resource, rabbitmq).key;
    // lemma_always_resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers_nor_deletion_timestamp(controller_id, cluster, spec, sub_resource, rabbitmq);
    guarantee_condition_holds(spec, cluster, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_no_pending_request_to_api_server_from_api_server_or_external(spec);
    cluster.lemma_always_all_requests_from_pod_monkey_are_api_pod_requests(spec);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    cluster.lemma_always_cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    always_to_always_later(spec, lift_state(rmq_guarantee(controller_id)));
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    always_to_always_later(spec, lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()));
    always_to_always_later(spec, lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()));
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        // &&& resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers_nor_deletion_timestamp(sub_resource, rabbitmq)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& rmq_guarantee(controller_id)(s)
        &&& rmq_guarantee(controller_id)(s_prime)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& Cluster::cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        // lift_state(resource_object_create_or_update_request_msg_has_one_controller_ref_and_no_finalizers_nor_deletion_timestamp(sub_resource, rabbitmq)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(rmq_guarantee(controller_id)),
        later(lift_state(rmq_guarantee(controller_id))),
        lift_state(rmq_rely_conditions(cluster, controller_id)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id))),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        later(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests())),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        later(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())
    );
    let resource_key = get_request(sub_resource, rabbitmq).key;
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        if s.resources().contains_key(resource_key) {
            let etcd_obj = s.resources()[resource_key];
            let owner_ref = choose |owner_reference: OwnerReferenceView| {
                &&& etcd_obj.metadata.owner_references == Some(seq![owner_reference])
                &&& #[trigger] owner_reference_eq_without_uid(owner_reference, rabbitmq.controller_owner_ref())
            };
            let some_rmq = RabbitmqClusterView {
                metadata: ObjectMetaView {
                    name: Some(rabbitmq.metadata.name->0),
                    uid: Some(owner_ref.uid),
                    ..rabbitmq.metadata
                },
                ..rabbitmq
            };
            assert(etcd_obj.metadata.owner_references->0[0] == some_rmq.controller_owner_ref());
            assert(etcd_obj.metadata.owner_references->0.contains(etcd_obj.metadata.owner_references->0[0]));
            assert(etcd_obj.metadata.owner_references_contains(some_rmq.controller_owner_ref()));
            assert(exists |rabbitmq: RabbitmqClusterView| #[trigger] etcd_obj.metadata.owner_references_contains(rabbitmq.controller_owner_ref()));
        }
        lemma_resource_key_has_rmq_prefix(sub_resource, rabbitmq);
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                match msg.src {
                    HostId::Controller(id, _) => {
                        if id == controller_id {
                            assert(rmq_guarantee(controller_id)(s));
                            assume(false);
                        } else {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(rmq_rely(id)(s));
                            match msg.content->APIRequest_0 {
                                APIRequest::CreateRequest(req) => {
                                    if is_rmq_managed_kind(req.obj.kind) {
                                        if req.obj.metadata.name is Some {
                                            if req.key() == resource_key {
                                                assert(false);
                                            }
                                        } else if req.obj.metadata.generate_name is Some {
                                            let name = generated_name(s.api_server, req.obj.metadata.generate_name->0);
                                            if has_rmq_prefix(name) {
                                                generated_name_spec(s.api_server, req.obj.metadata.generate_name->0);
                                                let generated_suffix = choose |suffix: StringView| #[trigger] dash_free(suffix) &&
                                                    name == req.obj.metadata.generate_name->0 + suffix;
                                                generated_name_reflects_prefix(s.api_server, req.obj.metadata.generate_name->0, RabbitmqClusterView::kind()->CustomResourceKind_0);
                                                assert(false);
                                            }
                                            assert(name != resource_key.name);
                                        }
                                    }
                                },
                                APIRequest::UpdateRequest(req) => {
                                    if s.resources().contains_key(resource_key) {
                                        if req.key() == resource_key {
                                            assert(update_request_admission_check(cluster.installed_types, req, s.api_server) is Some);
                                            assert(s_prime.resources() == s.resources());
                                        } else {
                                            assert(req.key() != resource_key);
                                        }
                                    }
                                },
                                APIRequest::GetThenUpdateRequest(req) => {
                                    if req.key() == resource_key && s.resources().contains_key(resource_key) {
                                        let etcd_obj = s.resources()[resource_key];
                                        let owner_refs = etcd_obj.metadata.owner_references->0;
                                        if owner_refs.contains(req.owner_ref) {
                                            lemma_singleton_contains_at_most_one_element(owner_refs, req.owner_ref, owner_refs[0]);
                                        }
                                        assert(s_prime.resources() == s.resources());
                                    }
                                },
                                _ => {}
                            }
                        }
                    },
                    _ => {},
                }
            },
            _ => {},
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
pub proof fn lemma_resource_get_then_update_request_msg_implies_key_in_reconcile_equals(controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, s: ClusterState, s_prime: ClusterState, msg: Message, step: Step)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, rabbitmq)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id) ==> #[trigger] rmq_rely(other_id)(s_prime),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        cluster.next_step(s, s_prime, step),
        resource_get_then_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg),
        // owner_ref kind/controller is required: only such get_then_update can target our resource_key.
        msg.content.get_get_then_update_request().owner_ref.kind == RabbitmqClusterView::kind(),
        msg.content.get_get_then_update_request().owner_ref.controller == Some(true),
    ensures
        step is ControllerStep,
        step->ControllerStep_0.0 == controller_id,
        step->ControllerStep_0.2->0 == rabbitmq.object_ref(),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s_prime),
        Cluster::pending_req_msg_is(controller_id, s_prime, rabbitmq.object_ref(), msg),
        msg.src == HostId::Controller(controller_id, rabbitmq.object_ref()),
        msg.content.get_get_then_update_request().owner_ref == rabbitmq.controller_owner_ref(),
{
    assert(step is ControllerStep);
    let (id, _, cr_key_opt) = step->ControllerStep_0;
    if id != controller_id { // other controller, call rely condition to derive contradiction
        assert(cluster.controller_models.remove(controller_id).contains_key(id));
        assert(rmq_rely(id)(s_prime));
        lemma_resource_key_has_rmq_prefix(sub_resource, rabbitmq);
        assert(false);
    }
    let cr_key = cr_key_opt->0;
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    RabbitmqReconcileState::marshal_preserves_integrity();
    assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
    let local_step = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    let local_step_prime = RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    assert(local_step is AfterKRequestStep && local_step->AfterKRequestStep_0 == ActionKind::Get);
    match local_step_prime {
        RabbitmqReconcileStep::AfterKRequestStep(action, res) => {
            match action {
                ActionKind::Update => {},
                _ => {
                    assert(!msg.content.is_get_then_update_request());
                    assert(!resource_get_then_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg));
                },
            }
        },
        _ => {}
    }
    assert(local_step_prime is AfterKRequestStep && local_step_prime->AfterKRequestStep_0 == ActionKind::Update);
    // 1. lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key: eliminates the "wrong sub-resource"
    //    case for sub-resources sharing the same Kind (e.g., PluginsConfigMap vs ServerConfigMap).
    // 2. lemma_cr_name_neq_implies_resource_key_name_neq (contrapositive): if the resource key names
    //    are equal, then cr_key.name == key.name.
    let local_step_sub_resource = local_step->AfterKRequestStep_1;
    // Eliminate the case where the controller creates a different sub-resource type.
    if local_step_sub_resource != sub_resource {
        lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key(cr_key, key, local_step_sub_resource, sub_resource);
    }
    // Now local_step_sub_resource == sub_resource. Prove cr_key.name == key.name by contrapositive.
    match sub_resource {
        SubResource::ServerConfigMap => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server-conf"@);
            }
        },
        SubResource::PluginsConfigMap => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-plugins-conf"@);
            }
        },
        SubResource::ErlangCookieSecret => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-erlang-cookie"@);
            }
        },
        SubResource::DefaultUserSecret => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-default-user"@);
            }
        },
        SubResource::HeadlessService => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-nodes"@);
            }
        },
        SubResource::Service => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-client"@);
            }
        },
        SubResource::RoleBinding | SubResource::ServiceAccount | SubResource::VStatefulSetView => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server"@);
            }
        },
        SubResource::Role => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-peer-discovery"@);
            }
        },
    }
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
pub proof fn lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id: int, cluster: Cluster, sub_resource: SubResource, rabbitmq: RabbitmqClusterView, s: ClusterState, s_prime: ClusterState, msg: Message, step: Step)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id) ==> #[trigger] rmq_rely(other_id)(s_prime),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        cluster.next_step(s, s_prime, step),
        resource_create_request_msg(get_request(sub_resource, rabbitmq).key)(msg),
    ensures
        step is ControllerStep,
        step->ControllerStep_0.0 == controller_id,
        step->ControllerStep_0.2->0 == rabbitmq.object_ref(),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, sub_resource))(s),
        at_rabbitmq_step(rabbitmq.object_ref(), controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Create, sub_resource))(s_prime),
        Cluster::pending_req_msg_is(controller_id, s_prime, rabbitmq.object_ref(), msg),
        exists |owner_reference: OwnerReferenceView| {
            &&& msg.content.get_create_request().obj.metadata.owner_references == Some(seq![owner_reference])
            &&& #[trigger] owner_reference_eq_without_uid(owner_reference, rabbitmq.controller_owner_ref())
        },
{
    // Since we know that this step creates a sub resource create request message, it is easy to see that it's a controller action.
    // This action creates a resource, and there may be sub-resources sharing the same Kind, so we have to show that only the correct sub-resource
    // is possible by extra reasoning about the strings.
    assert(step is ControllerStep);
    let (id, _, cr_key_opt) = step->ControllerStep_0;

    if id != controller_id { // other controller, call rely condition to derive contradiction
        assert(cluster.controller_models.remove(controller_id).contains_key(id));
        // rmq_rely(other_id)(s_prime): msg IS in s_prime.in_flight(), so rely applies
        assert(rmq_rely(id)(s_prime));
        // resource_create_request_msg gives us: req.obj.metadata.name is Some, name == resource_key.name.
        // resource_key.name has rabbitmq prefix; req.obj.kind == resource_key.kind is rabbitmq-managed.
        // rmq_rely_create_req: is_rmq_managed_kind(req.obj.kind) ==> name has no rabbitmq prefix. Contradiction.
        lemma_resource_key_has_rmq_prefix(sub_resource, rabbitmq);
        assert(false);
    }
    let cr_key = cr_key_opt->0;
    let cr = RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr)->Ok_0;
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let local_step = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    let local_step_prime = RabbitmqReconcileState::unmarshal(s_prime.ongoing_reconciles(controller_id)[cr_key].local_state)->Ok_0.reconcile_step;
    RabbitmqReconcileState::marshal_preserves_integrity();
    RabbitmqClusterView::marshal_preserves_integrity();
    assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
    assert(local_step is AfterKRequestStep && local_step->AfterKRequestStep_0 == ActionKind::Get);
    assert(local_step_prime is AfterKRequestStep && local_step_prime->AfterKRequestStep_0 == ActionKind::Create);
    assert(msg.content.get_create_request().obj.metadata.owner_references == Some(seq![cr.controller_owner_ref()]));
    // It's easy for the verifier to know that cr_key has the same kind and namespace as key.
    // We use two helper lemmas:
    // 1. lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key: eliminates the "wrong sub-resource"
    //    case for sub-resources sharing the same Kind (e.g., PluginsConfigMap vs ServerConfigMap).
    // 2. lemma_cr_name_neq_implies_resource_key_name_neq (contrapositive): if the resource key names
    //    are equal, then cr_key.name == key.name.
    let local_step_sub_resource = local_step->AfterKRequestStep_1;
    // Eliminate the case where the controller creates a different sub-resource type.
    if local_step_sub_resource != sub_resource {
        lemma_sub_resource_neq_implies_resource_key_neq_given_cr_key(cr_key, key, local_step_sub_resource, sub_resource);
    }
    // Now local_step_sub_resource == sub_resource. Prove cr_key.name == key.name by contrapositive.
    match sub_resource {
        SubResource::ServerConfigMap => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server-conf"@);
            }
        },
        SubResource::PluginsConfigMap => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-plugins-conf"@);
            }
        },
        SubResource::ErlangCookieSecret => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-erlang-cookie"@);
            }
        },
        SubResource::DefaultUserSecret => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-default-user"@);
            }
        },
        SubResource::HeadlessService => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-nodes"@);
            }
        },
        SubResource::Service => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-client"@);
            }
        },
        SubResource::RoleBinding | SubResource::ServiceAccount | SubResource::VStatefulSetView => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-server"@);
            }
        },
        SubResource::Role => {
            if cr_key.name != key.name {
                lemma_cr_name_neq_implies_resource_key_name_neq(cr_key.name, key.name, "-peer-discovery"@);
            }
        },
    }
    assert(cr_key == rabbitmq.object_ref());
    assert(owner_reference_eq_without_uid(cr.controller_owner_ref(), rabbitmq.controller_owner_ref()));
}

pub proof fn lemma_eventually_always_no_delete_resource_request_msg_from_gc_in_flight_forall(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| lift_state(no_delete_resource_request_msg_from_gc_in_flight(sub_resource, rabbitmq)))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] no_delete_resource_request_msg_from_gc_in_flight(sub_resource, rabbitmq))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(res, rabbitmq)), sub_resource);
        lemma_eventually_always_no_delete_resource_request_msg_from_gc_in_flight(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(no_delete_resource_request_msg_from_gc_in_flight(sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
proof fn lemma_eventually_always_no_delete_resource_request_msg_from_gc_in_flight(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_delete_resource_request_msg_from_gc_in_flight(sub_resource, rabbitmq))))),
{
    let key = rabbitmq.object_ref();
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let requirements = |msg: Message, s: ClusterState| !(msg.src == HostId::BuiltinController && resource_delete_request_msg(resource_key)(msg));

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(rabbitmq)(s)
        &&& resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::no_pending_request_to_api_server_from_non_controllers()(s_prime)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
    };
    assert forall |s: ClusterState, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if s.in_flight().contains(msg) {
                assert(requirements(msg, s));
                assert(requirements(msg, s_prime));
            } else {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::BuiltinControllersStep(_) => {
                        if s.resources().contains_key(resource_key) {
                            assert(cluster.etcd_object_is_well_formed(key)(s));
                            let owner_refs = s.resources()[resource_key].metadata.owner_references;
                            assert(owner_refs == Some(seq![rabbitmq.controller_owner_ref()]));
                            assert(owner_reference_to_object_reference(owner_refs->0[0], key.namespace) == key);
                        }
                    },
                    _ => {
                        assert(msg.src != HostId::BuiltinController);
                    }, // no_pending_request_to_api_server_from_non_controllers
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()));
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    invariant_n!(spec,
        lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        later(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())),
        later(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_delete_resource_request_msg_from_gc_in_flight(sub_resource, rabbitmq)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

// TODO: inline
pub proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr_forall(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(rmq_guarantee(controller_id)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(Cluster::every_create_msg_sets_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq)))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq)))))),
        spec.entails(always(tla_forall(|sub_resource: SubResource| lift_state(every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id, sub_resource, rabbitmq))))),
    ensures spec.entails(true_pred().leads_to(always(tla_forall(|sub_resource: SubResource| (lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))))),
{
    assert forall |sub_resource: SubResource| spec.entails(true_pred().leads_to(always(lift_state(#[trigger] resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))) by {
        always_tla_forall_apply(spec, |res: SubResource| lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(res, rabbitmq)), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource| lift_state(Cluster::every_create_msg_sets_owner_references_as(get_request(res, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq))), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource| lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(get_request(res, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq))), sub_resource);
        always_tla_forall_apply(spec, |res: SubResource| lift_state(every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id, res, rabbitmq)), sub_resource);
        lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(controller_id, cluster, spec, sub_resource, rabbitmq);
    }
    leads_to_always_tla_forall_subresource(spec, true_pred(), |sub_resource: SubResource| lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)));
}

#[verifier(spinoff_prover)]
proof fn lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView
)
    requires
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
        spec.entails(always(lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(Cluster::every_create_msg_sets_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq))))),
        spec.entails(always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(get_request(sub_resource, rabbitmq).key, owner_ref_is_current_cr_only(rabbitmq))))),
        spec.entails(always(lift_state(every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id, sub_resource, rabbitmq)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        spec.entails(always(lift_state(rmq_guarantee(controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq))))),
{
    let resource_key = get_request(sub_resource, rabbitmq).key;
    let eventual_owner_ref = owner_ref_is_current_cr_only(rabbitmq);
    // Derive `every_valid_update_msg_sets_owner_references_as` from the update-side invariant
    // and rely conditions; the create-side invariants come directly from the preconditions.
    assert forall |s: ClusterState|
        #[trigger] resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)(s)
        && every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id, sub_resource, rabbitmq)(s)
        && rmq_rely_conditions(cluster, controller_id)(s)
        && rmq_guarantee(controller_id)(s)
        && cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        && Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        && Cluster::no_pending_request_to_api_server_from_non_controllers()(s)
        && Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        implies Cluster::every_valid_update_msg_sets_owner_references_as(cluster.installed_types, resource_key, eventual_owner_ref)(s) by {
        if s.resources().contains_key(resource_key) {
            let etcd_obj = s.resources()[resource_key];
            let owner_ref = choose |owner_reference: OwnerReferenceView| {
                &&& etcd_obj.metadata.owner_references == Some(seq![owner_reference])
                &&& #[trigger] owner_reference_eq_without_uid(owner_reference, rabbitmq.controller_owner_ref())
            };
            let some_rmq = RabbitmqClusterView {
                metadata: ObjectMetaView {
                    name: Some(rabbitmq.metadata.name->0),
                    uid: Some(owner_ref.uid),
                    ..rabbitmq.metadata
                },
                ..rabbitmq
            };
            assert(etcd_obj.metadata.owner_references->0[0] == some_rmq.controller_owner_ref());
            assert(etcd_obj.metadata.owner_references->0.contains(etcd_obj.metadata.owner_references->0[0]));
            assert(etcd_obj.metadata.owner_references_contains(some_rmq.controller_owner_ref()));
            assert(exists |rabbitmq: RabbitmqClusterView| #[trigger] etcd_obj.metadata.owner_references_contains(rabbitmq.controller_owner_ref()));
        }
        assert forall |msg: Message| s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(resource_key)(msg)
            && update_request_admission_check(cluster.installed_types, msg.content.get_update_request(), s.api_server) is None
            implies false by {
            match msg.src {
                HostId::Controller(id, _) => {
                    if id != controller_id {
                        assert(cluster.controller_models.remove(controller_id).contains_key(id));
                        assert(rmq_rely(id)(s));
                        lemma_resource_key_has_rmq_prefix(sub_resource, rabbitmq);
                        assert(s.resources().contains_key(msg.content.get_update_request().key()));
                        assert(false);
                    }
                },
                _=> {},
            }
        }
        assert forall |msg: Message| {
            let req = msg.content.get_get_then_update_request();
            &&& s.in_flight().contains(msg)
            &&& #[trigger] resource_get_then_update_request_msg(resource_key)(msg)
            &&& req.well_formed()
            &&& s.resources().contains_key(req.key())
            &&& s.resources()[req.key()].metadata.owner_references_contains(req.owner_ref)
        } implies eventual_owner_ref(msg.content.get_get_then_update_request().obj.metadata.owner_references) by {
            match msg.src {
                HostId::Controller(id, _) => {
                    if id != controller_id {
                        assert(cluster.controller_models.remove(controller_id).contains_key(id));
                        assert(rmq_rely(id)(s));
                        lemma_resource_key_has_rmq_prefix(sub_resource, rabbitmq);
                        assert(s.resources().contains_key(msg.content.get_get_then_update_request().key()));
                        assert(false);
                    }
                },
                _=> {},
            }
        }
    }
    combine_spec_entails_always_n!(spec,
        lift_state(Cluster::every_valid_update_msg_sets_owner_references_as(cluster.installed_types, resource_key, eventual_owner_ref)),
        lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)),
        lift_state(every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id, sub_resource, rabbitmq)),
        lift_state(rmq_rely_conditions(cluster, controller_id)),
        lift_state(rmq_guarantee(controller_id))
    );
    always_weaken(spec,
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)),
        lift_state(Cluster::object_has_no_finalizers(resource_key))
    );

    let state = |s: ClusterState| {
        Cluster::desired_state_is(rabbitmq)(s)
        && resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq)(s)
    };
    invariant_n!(
        spec, lift_state(state), lift_state(Cluster::objects_owner_references_violates(resource_key, eventual_owner_ref)).implies(lift_state(Cluster::garbage_collector_deletion_enabled(resource_key))),
        lift_state(Cluster::desired_state_is(rabbitmq)),
        lift_state(resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource, rabbitmq))
    );
    cluster.lemma_eventually_objects_owner_references_satisfies(spec, resource_key, eventual_owner_ref);
    temp_pred_equality(
        lift_state(resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource, rabbitmq)),
        lift_state(Cluster::objects_owner_references_satisfies(resource_key, eventual_owner_ref))
    );
}

pub proof fn leads_to_always_tla_forall_subresource(spec: TempPred<ClusterState>, p: TempPred<ClusterState>, a_to_p: spec_fn(SubResource)->TempPred<ClusterState>)
    requires forall |a: SubResource| spec.entails(p.leads_to(always(#[trigger] a_to_p(a)))),
    ensures spec.entails(p.leads_to(always(tla_forall(a_to_p)))),
{
    leads_to_always_tla_forall(
        spec, p, a_to_p,
        set![SubResource::HeadlessService, SubResource::Service, SubResource::ErlangCookieSecret, SubResource::DefaultUserSecret,
        SubResource::PluginsConfigMap, SubResource::ServerConfigMap, SubResource::ServiceAccount, SubResource::Role,
        SubResource::RoleBinding, SubResource::VStatefulSetView]
    );
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
pub proof fn lemma_always_there_is_no_request_msg_to_external_from_controller(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>,
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
{
    let inv = Cluster::there_is_no_request_msg_to_external_from_controller(controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    RabbitmqReconcileState::marshal_preserves_integrity();
    RabbitmqClusterView::marshal_preserves_integrity();
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime)
        implies inv(s_prime) by {
        let new_msgs = s_prime.in_flight().sub(s.in_flight());
        assert forall |msg: Message|
            inv(s)
            && #[trigger] s_prime.in_flight().contains(msg)
            && msg.src.is_controller_id(controller_id)
            implies msg.dst != HostId::External(controller_id) by {
            if s.in_flight().contains(msg) {}
            if new_msgs.contains(msg) {}
        }
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

pub open spec fn sts_create_request_msg_has_correct_selector_with_rabbitmq_name(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let sts_key = make_stateful_set_key(rabbitmq);
        forall |msg: Message| s.in_flight().contains(msg) && resource_create_request_msg(sts_key)(msg)
        ==> {
            let sts = VStatefulSetView::unmarshal(msg.content.get_create_request().obj)->Ok_0;
            &&& VStatefulSetView::unmarshal(msg.content.get_create_request().obj) is Ok
            &&& sts.spec.selector == LabelSelectorView::default().with_match_labels(Map::empty().insert("app"@, rabbitmq.metadata.name->0))
        }
    }
}

pub proof fn lemma_always_sts_create_request_msg_has_correct_selector_with_rabbitmq_name(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(always(lift_state(sts_create_request_msg_has_correct_selector_with_rabbitmq_name(rabbitmq)))),
{
    let sts_key = make_stateful_set_key(rabbitmq);
    let inv = sts_create_request_msg_has_correct_selector_with_rabbitmq_name(rabbitmq);
    let requirements = |msg: Message| resource_create_request_msg(sts_key)(msg)
    ==> {
        let sts = VStatefulSetView::unmarshal(msg.content.get_create_request().obj)->Ok_0;
        &&& VStatefulSetView::unmarshal(msg.content.get_create_request().obj) is Ok
        &&& sts.spec.selector == LabelSelectorView::default().with_match_labels(Map::empty().insert("app"@, rabbitmq.metadata.name->0))
    };
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
    };
    cluster.lemma_always_every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_cr_states_are_unmarshallable::<RabbitmqReconciler, RabbitmqReconcileState, RabbitmqClusterView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(spec, controller_id);
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) implies requirements(msg) by {
            if !s.in_flight().contains(msg) && resource_create_request_msg(sts_key)(msg) {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::ControllerStep((id, _, cr_key_opt)) => {
                        let req = msg.content.get_create_request();
                        if id == controller_id {
                            RabbitmqClusterView::marshal_preserves_integrity();
                            RabbitmqReconcileState::marshal_preserves_integrity();
                            VStatefulSetView::marshal_preserves_integrity();
                            let cr_key = cr_key_opt->0;
                            let cr = RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                            let local_state = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            lemma_resource_create_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, SubResource::VStatefulSetView, rabbitmq, s, s_prime, msg, step);
                            assert(cr.object_ref() == rabbitmq.object_ref());
                            assert(req.obj == make(SubResource::VStatefulSetView, cr, local_state)->Ok_0);
                            assert(req.obj.metadata.finalizers is None);
                            assert(req.obj.metadata.owner_references == Some(seq![cr.controller_owner_ref()]));
                        } else if is_rmq_managed_kind(req.obj.kind) {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(rmq_rely(id)(s_prime));
                            // id != controller_id: use rely.
                            if req.obj.metadata.name is Some {
                                if req.key() == sts_key {
                                    lemma_resource_key_has_rmq_prefix(SubResource::VStatefulSetView, rabbitmq);
                                    assert(false);
                                }
                            } else if req.obj.metadata.generate_name is Some {
                                let name = generated_name(s.api_server, req.obj.metadata.generate_name->0);
                                if has_rmq_prefix(name) {
                                    generated_name_spec(s.api_server, req.obj.metadata.generate_name->0);
                                    let generated_suffix = choose |suffix: StringView| #[trigger] dash_free(suffix) &&
                                        name == req.obj.metadata.generate_name->0 + suffix;
                                    generated_name_reflects_prefix(s.api_server, req.obj.metadata.generate_name->0, RabbitmqClusterView::kind()->CustomResourceKind_0);
                                    assert(false);
                                }
                                assert(name != sts_key.name);
                            }
                        }
                    },
                    _ => {}
                }
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// similar to resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref
#[verifier(spinoff_prover)]
#[verifier(rlimit(50))]
pub proof fn lemma_always_sts_in_etcd_with_rmq_key_match_rmq_selector(
    controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(sts_in_etcd_with_rmq_key_match_rmq_selector(rabbitmq)))),
{
    let sts_key = make_stateful_set_key(rabbitmq);
    let inv = sts_in_etcd_with_rmq_key_match_rmq_selector(rabbitmq);
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s_prime)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& sts_create_request_msg_has_correct_selector_with_rabbitmq_name(rabbitmq)(s)
        &&& rmq_guarantee(controller_id)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
    };
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_cr_states_are_unmarshallable::<RabbitmqReconciler, RabbitmqReconcileState, RabbitmqClusterView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>(spec);
    cluster.lemma_always_all_requests_from_pod_monkey_are_api_pod_requests(spec);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    cluster.lemma_always_no_pending_request_to_api_server_from_api_server_or_external(spec);
    guarantee_condition_holds(spec, cluster, controller_id);
    lemma_always_resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(controller_id, cluster, spec, SubResource::VStatefulSetView, rabbitmq);
    lemma_always_sts_create_request_msg_has_correct_selector_with_rabbitmq_name(controller_id, cluster, spec, rabbitmq);
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    always_to_always_later(spec, lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        later(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>())),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(sts_create_request_msg_has_correct_selector_with_rabbitmq_name(rabbitmq)),
        lift_state(rmq_guarantee(controller_id)),
        lift_state(rmq_rely_conditions(cluster, controller_id)),
        later(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                match msg.content->APIRequest_0 {
                    APIRequest::CreateRequest(req) => {
                        if req.obj.metadata.name is Some {
                            if !s.resources().contains_key(sts_key) && resource_create_request_msg(sts_key)(msg) && s_prime.resources().contains_key(sts_key) {
                                VStatefulSetView::marshal_preserves_integrity();
                            }
                        } else if resource_create_request_msg_without_name(sts_key.kind, sts_key.namespace)(msg) {
                            match msg.src {
                                HostId::Controller(id, _) => {
                                    if id != controller_id && !s.resources().contains_key(sts_key) && s_prime.resources().contains_key(sts_key) {
                                        assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                        assert(rmq_rely(id)(s));
                                        lemma_resource_key_has_rmq_prefix(SubResource::VStatefulSetView, rabbitmq);
                                        generated_name_reflects_prefix(s.api_server, req.obj.metadata.generate_name->0, RabbitmqClusterView::kind()->CustomResourceKind_0);
                                        assert(false);
                                    }
                                },
                                _ => {assert(false);}
                            }
                        }
                    },
                    APIRequest::GetThenUpdateRequest(req) => {
                        if resource_get_then_update_request_msg(sts_key)(msg) {
                            // by transition validation
                        } else {
                            assert(req.key() != sts_key);
                        }
                    },
                    _ => {}
                }
            },
            _ => {},
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
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
