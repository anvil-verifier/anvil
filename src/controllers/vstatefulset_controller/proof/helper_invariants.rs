use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::{
    proof::api_server::*,
    spec::{
        api_server::{state_machine::*, types::InstalledTypes},
        cluster::*,
        controller::types::ControllerStep,
        message::*,
    },
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    trusted::{
        liveness_theorem::*, 
        rely_guarantee, 
        spec_types::*, 
        step::*
    },
    proof::{
        predicate::*,
        guarantee,
        helper_lemmas::*,
        internal_rely_guarantee,
    },
};
use crate::vstd_ext::{seq_lib::*, string_view::*};
use deps_hack::kube_core::Object;
use vstd::prelude::*;

verus! {

// name collision prevention invariant, eventually holds
// In the corner case when one vsts was created and then deleted, just before
// another vsts with the same name comes, GC will delete pods owned by the previous vsts
pub open spec fn all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |pod_key: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(pod_key)
            &&& pod_key.kind == Kind::PodKind
            &&& pod_key.namespace == vsts.object_ref().namespace
            &&& pod_name_match(pod_key.name, vsts.object_ref().name)
        } ==> {
            let obj = s.resources()[pod_key];
            &&& obj.metadata.deletion_timestamp is None
            &&& obj.metadata.finalizers is None
            &&& obj.metadata.owner_references == Some(Seq::empty().push(vsts.controller_owner_ref()))
        }
    }
}

pub open spec fn all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |pod_key: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(pod_key)
            &&& pod_key.kind == Kind::PodKind
            &&& pod_key.namespace == vsts.object_ref().namespace
            &&& pod_name_match(pod_key.name, vsts.object_ref().name)
        } ==> {
            let obj = s.resources()[pod_key];
            &&& obj.metadata.deletion_timestamp is None
            &&& obj.metadata.finalizers is None
            &&& exists |owner_reference: OwnerReferenceView| {
                &&& obj.metadata.owner_references == Some(Seq::empty().push(owner_reference))
                &&& #[trigger] owner_reference_eq_without_uid(owner_reference, vsts.controller_owner_ref())
            }
        }
    }
}

pub open spec fn is_vsts_pod_key(vsts: VStatefulSetView) -> spec_fn(ObjectRef) -> bool {
    |key: ObjectRef| key.kind == Kind::PodKind && key.namespace == vsts.object_ref().namespace && pod_name_match(key.name, vsts.object_ref().name)
}

pub proof fn lemma_always_all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(always(lift_state(rely_guarantee::vsts_rely_conditions_pod_monkey()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)))),
{
    let inv = all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& rely_guarantee::vsts_rely_conditions(cluster, controller_id)(s)
        &&& rely_guarantee::vsts_rely_conditions_pod_monkey()(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)(s)
        &&& every_msg_from_vsts_controller_carries_vsts_key(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_no_pending_request_to_api_server_from_api_server_or_external(spec);
    cluster.lemma_always_all_requests_from_pod_monkey_are_api_pod_requests(spec);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    internal_rely_guarantee::internal_guarantee_condition_holds_on_all_vsts(spec, cluster, controller_id);
    lemma_always_every_msg_from_vsts_controller_carries_vsts_key(spec, cluster, controller_id);

    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime)
        implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                let resp_msg = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
                assert(msg.content is APIRequest);
                assert(resp_msg.content is APIResponse);
                if is_ok_resp(resp_msg.content->APIResponse_0) { // otherwise, etcd is not changed
                    assert(msg.content is APIRequest);
                    assert forall |pod_key: ObjectRef| {
                        &&& #[trigger] s_prime.resources().contains_key(pod_key)
                        &&& pod_key.kind == Kind::PodKind
                        &&& pod_key.namespace == vsts.object_ref().namespace
                        &&& pod_name_match(pod_key.name, vsts.object_ref().name)
                    } implies {
                        let obj = s_prime.resources()[pod_key];
                        &&& obj.metadata.deletion_timestamp is None
                        &&& obj.metadata.finalizers is None
                        &&& exists |owner_reference: OwnerReferenceView| {
                            &&& obj.metadata.owner_references == Some(Seq::empty().push(owner_reference))
                            &&& #[trigger] owner_reference_eq_without_uid(owner_reference, vsts.controller_owner_ref())
                        }
                    } by {
                        let obj_prime = s_prime.resources()[pod_key];
                        let post = {
                            &&& obj_prime.metadata.deletion_timestamp is None
                            &&& obj_prime.metadata.finalizers is None
                            &&& exists |owner_reference: OwnerReferenceView| {
                                &&& obj_prime.metadata.owner_references == Some(Seq::empty().push(owner_reference))
                                &&& #[trigger] owner_reference_eq_without_uid(owner_reference, vsts.controller_owner_ref())
                            }
                        };
                        match msg.src {
                            HostId::Controller(other_id, cr_key) => {
                                if other_id != controller_id {
                                    assert(cluster.controller_models.remove(controller_id).contains_key(other_id));
                                    assert(rely_guarantee::vsts_rely(other_id)(s));
                                    match (msg.content->APIRequest_0) {
                                        APIRequest::CreateRequest(req) => {
                                            if req.key().kind == Kind::PodKind {
                                                assert(rely_guarantee::rely_create_req(req));
                                                let name = if req.obj.metadata.name is Some {
                                                    req.obj.metadata.name->0
                                                } else {
                                                    generated_name(s.api_server, req.obj.metadata.generate_name->0)
                                                };
                                                assert(!has_vsts_prefix(name)) by {
                                                    if req.obj.metadata.name is Some {
                                                        assert(!has_vsts_prefix(req.obj.metadata.name->0));
                                                    } else {
                                                        assert(!has_vsts_prefix(req.obj.metadata.generate_name->0));
                                                        generated_name_reflects_prefix(s.api_server, req.obj.metadata.generate_name->0, VStatefulSetView::kind()->CustomResourceKind_0);
                                                    }
                                                }
                                            }
                                        },
                                        _ => {}
                                    }
                                } else if cr_key != vsts.object_ref() {
                                    let vsts_with_key = VStatefulSetView {
                                        metadata: ObjectMetaView {
                                            name: Some(cr_key.name),
                                            namespace: Some(cr_key.namespace),
                                            ..ObjectMetaView::default()
                                        },
                                        ..VStatefulSetView::default()
                                    };
                                    assert(vsts_with_key.object_ref() == cr_key);
                                    assert(internal_rely_guarantee::no_interfering_request_between_vsts(controller_id, vsts_with_key)(s));
                                    assert(s.in_flight().contains(msg)); // trigger
                                    if msg.content.is_create_request() {
                                        let req = msg.content.get_create_request();
                                        assert(internal_rely_guarantee::vsts_internal_guarantee_create_req(req, vsts_with_key));
                                        if req.key() == pod_key {
                                            if cr_key.namespace == vsts.object_ref().namespace {
                                                assert(cr_key.name != vsts.object_ref().name);
                                                assert(pod_name_match(req.obj.metadata.name->0, cr_key.name));
                                                vsts_name_neq_implies_no_pod_name_match(req.obj.metadata.name->0, cr_key.name, vsts.object_ref().name);
                                                assert(req.key() != pod_key);
                                            }
                                        }
                                    }
                                } else {
                                    assert(internal_rely_guarantee::no_interfering_request_between_vsts(controller_id, vsts)(s));
                                }
                            },
                            HostId::BuiltinController => {}, // must be delete requests
                            HostId::PodMonkey => {
                                assert(rely_guarantee::vsts_rely_conditions_pod_monkey()(s));
                                if msg.content.is_create_request() {
                                    let req = msg.content.get_create_request();
                                    assert(rely_guarantee::rely_create_req(req));
                                    let name = if req.obj.metadata.name is Some {
                                        req.obj.metadata.name->0
                                    } else {
                                        generated_name(s.api_server, req.obj.metadata.generate_name->0)
                                    };
                                    assert(!has_vsts_prefix(name)) by {
                                        if req.obj.metadata.name is Some {
                                            assert(!has_vsts_prefix(req.obj.metadata.name->0));
                                        } else {
                                            assert(!has_vsts_prefix(req.obj.metadata.generate_name->0));
                                            generated_name_reflects_prefix(s.api_server, req.obj.metadata.generate_name->0, VStatefulSetView::kind()->CustomResourceKind_0);
                                        }
                                    }
                                } else {} // Deletion/Update/UpdateStatus are not possible
                            }, // must be pod requests
                            _ => {}
                        }
                    }
                } else {
                    assert(s_prime.resources() == s.resources());
                }
            },
            _ => {}
        }
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)),
        lift_state(rely_guarantee::vsts_rely_conditions_pod_monkey()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)),
        lift_state(every_msg_from_vsts_controller_carries_vsts_key(controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// only contains one owner_ref, so GC can delete it when the vsts is deleted
pub open spec fn vsts_pods_only_have_one_vsts_owner_ref() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |pod_key: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(pod_key)
            &&& pod_key.kind == Kind::PodKind
            &&& has_vsts_prefix(pod_key.name)
        } ==> exists |vsts: VStatefulSetView| {
            let obj = s.resources()[pod_key];
            &&& pod_key.namespace == vsts.object_ref().namespace
            &&& obj.metadata.owner_references == Some(seq![#[trigger] vsts.controller_owner_ref()])
        }
    }
}

// same as owner_references_contains
pub open spec fn owner_reference_requirements(vsts: VStatefulSetView) ->spec_fn(Option<Seq<OwnerReferenceView>>) -> bool {
    |owner_references: Option<Seq<OwnerReferenceView>>| owner_references == Some(seq![vsts.controller_owner_ref()])
}

pub open spec fn all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts: VStatefulSetView, controller_id: int) -> spec_fn(Message, ClusterState) -> bool {
    |msg: Message, s: ClusterState| {
        msg.src == HostId::Controller(controller_id, vsts.object_ref()) ==> match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) =>
                req.obj.kind == Kind::PodKind ==> req.obj.metadata.owner_references == Some(seq![vsts.controller_owner_ref()]),
            APIRequest::GetThenUpdateRequest(req) =>
                req.obj.kind == Kind::PodKind && req.obj.metadata.owner_references == Some(seq![vsts.controller_owner_ref()]),
            APIRequest::GetThenDeleteRequest(_) => true,
            _ => false,
        }
    }
}

#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
    spec.entails(always(lift_state(vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id)))))),
{
    let requirements = all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vsts)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)(s)
        &&& vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id)(s)
    };
    assert forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
            implies requirements(msg, s_prime) by {
            if !s.in_flight().contains(msg) && msg.src == HostId::Controller(controller_id, vsts.object_ref()) {
                let triggering_cr = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr)->Ok_0;
                assert(triggering_cr.controller_owner_ref() == vsts.controller_owner_ref());
            }
        }
    };
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vsts)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)),
        lift_state(vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id))
    );
    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id)))
    );
}

proof fn lemma_eventually_always_every_create_msg_with_generate_name_matching_key_set_owner_references_as_for_all(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
    spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)))),
    spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
    spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
    spec.entails(always(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as_for_all(
        is_vsts_pod_key(vsts),
        owner_reference_requirements(vsts)
    )))))
{
    let requirements = |msg: Message, s: ClusterState| {
        resource_create_request_msg_without_name(Kind::PodKind, vsts.object_ref().namespace)(msg)
        && has_vsts_prefix(msg.content.get_create_request().obj.metadata.generate_name->0)
            ==> owner_reference_requirements(vsts)(msg.content.get_create_request().obj.metadata.owner_references)
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)(s)
        &&& Cluster::no_pending_request_to_api_server_from_non_controllers()(s_prime)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s_prime)
        &&& internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)(s_prime)
        &&& rely_guarantee::vsts_rely_conditions(cluster, controller_id)(s_prime)
    };
    assert forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
            implies requirements(msg, s_prime) by {
            if !s.in_flight().contains(msg) && resource_create_request_msg_without_name(Kind::PodKind, vsts.object_ref().namespace)(msg) {
                let req = msg.content.get_create_request();
                match msg.src {
                    HostId::Controller(id, cr_key) => {
                        if id == controller_id {
                            let other_vsts = VStatefulSetView {
                                metadata: ObjectMetaView {
                                    name: Some(cr_key.name),
                                    namespace: Some(cr_key.namespace),
                                    ..ObjectMetaView::default()
                                },
                                ..VStatefulSetView::default()
                            };
                            assert(internal_rely_guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s_prime));
                            assert(internal_rely_guarantee::vsts_internal_guarantee_create_req(req, vsts));
                        } else {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(rely_guarantee::vsts_rely(id)(s_prime));
                            assert(!has_vsts_prefix(req.obj.metadata.generate_name->0));
                        }
                    },
                    _ => {}
                }
            }
        }
    }
    always_to_always_later(spec, lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()));
    always_to_always_later(spec, lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()));
    always_to_always_later(spec, lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)));
    always_to_always_later(spec, lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)));
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)),
        later(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())),
        later(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        later(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id))),
        later(lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)))
    );
    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)).satisfied_by(ex)
        implies lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as_for_all(is_vsts_pod_key(vsts), owner_reference_requirements(vsts))).satisfied_by(ex) by {
        let s = ex.head();
        assert forall |key: ObjectRef| #[trigger] is_vsts_pod_key(vsts)(key) implies
            Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(key, owner_reference_requirements(vsts))(s) by {
            assert forall |msg: Message| {
                &&& #[trigger] s.in_flight().contains(msg)
                &&& msg.dst is APIServer && msg.content is APIRequest
            } implies {
                resource_create_request_msg_without_name(key.kind, key.namespace)(msg)
                ==> generated_name(s.api_server, msg.content.get_create_request().obj.metadata.generate_name->0) == key.name
                    ==> owner_reference_requirements(vsts)(msg.content.get_create_request().obj.metadata.owner_references)
            } by {
                if generated_name(s.api_server, msg.content.get_create_request().obj.metadata.generate_name->0) == key.name {
                    generated_name_reflects_prefix(s.api_server, msg.content.get_create_request().obj.metadata.generate_name->0, VStatefulSetView::kind()->CustomResourceKind_0);
                    assert(requirements(msg, s));
                }
            };
        };
    };
    entails_preserved_by_always(
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)),
        lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as_for_all(is_vsts_pod_key(vsts), owner_reference_requirements(vsts)))
    );
    entails_implies_leads_to(spec,
        always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))),
        always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as_for_all(is_vsts_pod_key(vsts), owner_reference_requirements(vsts))))
    );
    leads_to_trans(spec,
        true_pred(),
        always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))),
        always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as_for_all(is_vsts_pod_key(vsts), owner_reference_requirements(vsts))))
    );
}

proof fn lemma_eventually_always_every_create_msg_sets_owner_references_as_for_all(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)))),
    spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
    spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))))),
    spec.entails(always(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(Cluster::every_create_msg_sets_owner_references_as_for_all(
        is_vsts_pod_key(vsts),
        owner_reference_requirements(vsts)
    ))))),
{
    let key_cond = |key: ObjectRef| { 
        &&& key.kind == Kind::PodKind
        &&& key.namespace == vsts.object_ref().namespace
        &&& pod_name_match(key.name, vsts.object_ref().name)
    };
    let requirements = |msg: Message, s: ClusterState|
        forall |key: ObjectRef| (key_cond(key) && resource_create_request_msg(key)(msg)) ==> owner_reference_requirements(vsts)(msg.content.get_create_request().obj.metadata.owner_references);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vsts)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)(s)
        &&& Cluster::no_pending_request_to_api_server_from_non_controllers()(s_prime)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s_prime)
        &&& Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))(s_prime)
        &&& internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)(s_prime)
        &&& rely_guarantee::vsts_rely_conditions(cluster, controller_id)(s_prime)
    };
    assert forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
            implies requirements(msg, s_prime) by {
            assert forall |key: ObjectRef| (key_cond(key) && resource_create_request_msg(key)(msg)) implies owner_reference_requirements(vsts)(msg.content.get_create_request().obj.metadata.owner_references) by {
                if !s.in_flight().contains(msg) && resource_create_request_msg(key)(msg) {
                    match msg.src {
                        HostId::Controller(id, cr_key) => {
                            if id == controller_id {
                                if cr_key == vsts.object_ref() {
                                    assert(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id)(msg, s_prime));
                                } else if resource_create_request_msg(key)(msg) {
                                    let other_vsts = VStatefulSetView {
                                        metadata: ObjectMetaView {
                                            name: Some(cr_key.name),
                                            namespace: Some(cr_key.namespace),
                                            ..ObjectMetaView::default()
                                        },
                                        ..VStatefulSetView::default()
                                    };
                                    assert(internal_rely_guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s_prime));
                                    vsts_name_neq_implies_no_pod_name_match(key.name, other_vsts.object_ref().name, vsts.object_ref().name);
                                    assert(false);
                                }
                            } else {
                                let req = msg.content.get_create_request();
                                if msg.content is APIRequest && req.key() == key && req.obj.metadata.name is Some {
                                    assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                    assert(rely_guarantee::vsts_rely(id)(s_prime));
                                    assert(false);
                                }
                            }
                        },
                        _ => {}
                    }
                }
            }
        }
    };
    always_to_always_later(spec, lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()));
    always_to_always_later(spec, lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()));
    always_to_always_later(spec, lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))));
    always_to_always_later(spec, lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)));
    always_to_always_later(spec, lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)));
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vsts)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)),
        later(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())),
        later(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        later(lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id)))),
        later(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id))),
        later(lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)))
    );
    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(Cluster::every_create_msg_sets_owner_references_as_for_all(is_vsts_pod_key(vsts), owner_reference_requirements(vsts))),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

proof fn lemma_eventually_always_every_update_msg_sets_owner_references_as_for_all(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)))),
    spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
    spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))))),
    spec.entails(always(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(Cluster::every_update_msg_sets_owner_references_as_for_all(
        is_vsts_pod_key(vsts),
        owner_reference_requirements(vsts)
    )))))
{
    let key_cond = |key: ObjectRef| {
        &&& key.kind == Kind::PodKind
        &&& key.namespace == vsts.object_ref().namespace
        &&& pod_name_match(key.name, vsts.object_ref().name)
    };
    let requirements = |msg: Message, s: ClusterState| {
        forall |key: ObjectRef| key_cond(key) ==> {
            &&& resource_update_request_msg(key)(msg) ==> false
            &&& resource_get_then_update_request_msg(key)(msg) ==> owner_reference_requirements(vsts)(msg.content.get_get_then_update_request().obj.metadata.owner_references)
        }
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vsts)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)(s)
        &&& Cluster::no_pending_request_to_api_server_from_non_controllers()(s_prime)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s_prime)
        &&& Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))(s_prime)
        &&& internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)(s_prime)
        &&& rely_guarantee::vsts_rely_conditions(cluster, controller_id)(s_prime)
    };
    assert forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
            implies requirements(msg, s_prime) by {
            assert forall |key: ObjectRef| key_cond(key) implies {
                &&& resource_update_request_msg(key)(msg) ==> false
                &&& resource_get_then_update_request_msg(key)(msg) ==> owner_reference_requirements(vsts)(msg.content.get_get_then_update_request().obj.metadata.owner_references)
            } by {
                if !s.in_flight().contains(msg) {
                    match msg.src {
                        HostId::Controller(id, cr_key) => {
                            if id == controller_id {
                                if cr_key == vsts.object_ref() {
                                    assert(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id)(msg, s_prime));
                                } else {
                                    let other_vsts = VStatefulSetView {
                                        metadata: ObjectMetaView {
                                            name: Some(cr_key.name),
                                            namespace: Some(cr_key.namespace),
                                            ..ObjectMetaView::default()
                                        },
                                        ..VStatefulSetView::default()
                                    };
                                    assert(internal_rely_guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s_prime));
                                    if resource_get_then_update_request_msg(key)(msg) {
                                        vsts_name_neq_implies_no_pod_name_match(key.name, other_vsts.object_ref().name, vsts.object_ref().name);
                                        assert(false);
                                    } else if resource_update_request_msg(key)(msg) {
                                        assert(false);
                                    }
                                }
                            } else {
                                assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                assert(rely_guarantee::vsts_rely(id)(s_prime));
                            }
                        },
                        _ => {}
                    }
                }
            }
        }
    };
    always_to_always_later(spec, lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()));
    always_to_always_later(spec, lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()));
    always_to_always_later(spec, lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))));
    always_to_always_later(spec, lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)));
    always_to_always_later(spec, lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)));
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vsts)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)),
        later(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())),
        later(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        later(lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id)))),
        later(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id))),
        later(lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)))
    );
    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)).satisfied_by(ex)
        implies lift_state(Cluster::every_update_msg_sets_owner_references_as_for_all(is_vsts_pod_key(vsts), owner_reference_requirements(vsts))).satisfied_by(ex) by {
        let s = ex.head();
        assert forall |key: ObjectRef| #[trigger] is_vsts_pod_key(vsts)(key) implies Cluster::every_update_msg_sets_owner_references_as(key, owner_reference_requirements(vsts))(s) by {
            assert forall |msg: Message| s.in_flight().contains(msg) && #[trigger] resource_update_request_msg(key)(msg)
                implies owner_reference_requirements(vsts)(msg.content.get_update_request().obj.metadata.owner_references) by {
                assert(key_cond(key));
                assert(requirements(msg, s));
                assert(false);
            };
            assert forall |msg: Message| s.in_flight().contains(msg) && #[trigger] resource_get_then_update_request_msg(key)(msg)
                implies owner_reference_requirements(vsts)(msg.content.get_get_then_update_request().obj.metadata.owner_references) by {
                assert(key_cond(key));
                assert(requirements(msg, s));
            };
        };
    };
    entails_preserved_by_always(
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)),
        lift_state(Cluster::every_update_msg_sets_owner_references_as_for_all(is_vsts_pod_key(vsts), owner_reference_requirements(vsts)))
    );
    entails_implies_leads_to(spec,
        always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))),
        always(lift_state(Cluster::every_update_msg_sets_owner_references_as_for_all(is_vsts_pod_key(vsts), owner_reference_requirements(vsts))))
    );
    leads_to_trans(spec,
        true_pred(),
        always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))),
        always(lift_state(Cluster::every_update_msg_sets_owner_references_as_for_all(is_vsts_pod_key(vsts), owner_reference_requirements(vsts))))
    );
}

pub proof fn lemma_eventually_always_all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
    spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    spec.entails(always(lift_state(Cluster::etcd_is_finite()))),
    spec.entails(always(lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)))),
    spec.entails(always(lift_state(Cluster::every_create_msg_sets_owner_references_as_for_all(
        |key: ObjectRef| key.kind == Kind::PodKind && key.namespace == vsts.object_ref().namespace && pod_name_match(key.name, vsts.object_ref().name),
        owner_reference_requirements(vsts)
    )))),
    spec.entails(always(lift_state(Cluster::every_update_msg_sets_owner_references_as_for_all(
        |key: ObjectRef| key.kind == Kind::PodKind && key.namespace == vsts.object_ref().namespace && pod_name_match(key.name, vsts.object_ref().name),
        owner_reference_requirements(vsts)
    )))),
    spec.entails(always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as_for_all(
        |key: ObjectRef| key.kind == Kind::PodKind && key.namespace == vsts.object_ref().namespace && pod_name_match(key.name, vsts.object_ref().name),
        owner_reference_requirements(vsts)
    )))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts)))))
{
    let cond = |key: ObjectRef| key.kind == Kind::PodKind && key.namespace == vsts.object_ref().namespace && pod_name_match(key.name, vsts.object_ref().name);
    let req = owner_reference_requirements(vsts);

    assert forall |ex: Execution<ClusterState>|
        #[trigger] lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)).satisfied_by(ex)
        implies lift_state(Cluster::object_has_no_finalizers_for_all(cond)).satisfied_by(ex) by {
        let s = ex.head();
        assert forall |key: ObjectRef| #[trigger] cond(key) implies Cluster::object_has_no_finalizers(key)(s) by {
            if s.resources().contains_key(key) {
                assert(s.resources()[key].metadata.finalizers is None);
            }
        };
    };
    entails_preserved_by_always(
        lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)),
        lift_state(Cluster::object_has_no_finalizers_for_all(cond))
    );
    entails_trans(spec,
        always(lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts))),
        always(lift_state(Cluster::object_has_no_finalizers_for_all(cond)))
    );

    let partial_spec = lift_state(and!(
        Cluster::desired_state_is(vsts),
        all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts),
        Cluster::every_create_msg_sets_owner_references_as_for_all(cond, req),
        Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as_for_all(cond, req)
    ));
    invariant_n!(spec, partial_spec,
        lift_state(Cluster::gc_is_enabled_for_all_keys_violating_owner_ref_requirements(cond, req)),
        lift_state(Cluster::desired_state_is(vsts)),
        lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)),
        lift_state(Cluster::every_create_msg_sets_owner_references_as_for_all(cond, req)),
        lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as_for_all(cond, req))
    );

    cluster.lemma_eventually_objects_owner_references_satisfies_for_all(spec, cond, req);

    assert(lift_state(Cluster::objects_owner_references_satisfies_for_all(cond, req))
        .and(lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)))
        .entails(lift_state(all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts)))) by {
        assert forall |ex: Execution<ClusterState>|
            (lift_state(Cluster::objects_owner_references_satisfies_for_all(cond, req))
            .and(lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)))).satisfied_by(ex)
            implies #[trigger] lift_state(all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts)).satisfied_by(ex) by {
            let s = ex.head();
            assert forall |pod_key: ObjectRef| {
                &&& #[trigger] s.resources().contains_key(pod_key)
                &&& pod_key.kind == Kind::PodKind
                &&& pod_key.namespace == vsts.object_ref().namespace
                &&& pod_name_match(pod_key.name, vsts.object_ref().name)
            } implies {
                let obj = s.resources()[pod_key];
                &&& obj.metadata.deletion_timestamp is None
                &&& obj.metadata.finalizers is None
                &&& obj.metadata.owner_references == Some(Seq::empty().push(vsts.controller_owner_ref()))
            } by {
                assert(cond(pod_key));
            };
        };
    };
    leads_to_always_enhance(spec,
        lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)),
        true_pred(),
        lift_state(Cluster::objects_owner_references_satisfies_for_all(cond, req)),
        lift_state(all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts))
    );
}

// stronger version of all_requests_from_builtin_controllers_are_api_delete_requests
// as guaranteed by rely_guarantee condition, PVC's owner_references remains None
pub open spec fn buildin_controllers_do_not_delete_pvcs_owned_by_vsts() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src is BuiltinController
        } ==> {
            let key = msg.content.get_delete_request().key;
            &&& msg.dst is APIServer
            &&& msg.content.is_delete_request()
            &&& !(key.kind == Kind::PersistentVolumeClaimKind
                && exists |vsts_name: StringView| pvc_name_match(key.name, vsts_name))
        }
    }
}

pub open spec fn buildin_controllers_do_not_delete_pods_owned_by_vsts(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src is BuiltinController
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
        } ==> {
            let req = msg.content.get_delete_request();
            &&& msg.content.is_delete_request()
            &&& req.preconditions is Some
            &&& req.preconditions.unwrap().uid is Some
            &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
            &&& s.resources().contains_key(req.key) ==> {
                let obj = s.resources()[req.key];
                // this object is not owned by vsts
                ||| !(obj.metadata.owner_references_contains(vsts.controller_owner_ref())
                        && obj.kind == PodView::kind()
                        && obj.metadata.namespace == vsts.metadata.namespace)
                // this object is created later with different uid, deletion fails
                ||| obj.metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap()
            }
        }
    }
}

#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_buildin_controllers_do_not_delete_pods_owned_by_vsts(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
    spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
    spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
    spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
    spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
    spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<VStatefulSetView>(controller_id)))),
    spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())))),
    spec.entails(always(lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(always(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(buildin_controllers_do_not_delete_pods_owned_by_vsts(vsts))))),
{
    let requirements = |msg: Message, s: ClusterState| {
        &&& s.in_flight().contains(msg)
        &&& msg.src is BuiltinController
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
    } ==> {
        let req = msg.content.get_delete_request();
        &&& msg.content.is_delete_request()
        &&& req.preconditions is Some
        &&& req.preconditions.unwrap().uid is Some
        &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
        &&& s.resources().contains_key(req.key) ==> {
            let obj = s.resources()[req.key];
            // this object is not owned by vsts
            ||| !(obj.metadata.owner_references_contains(vsts.controller_owner_ref())
                    && obj.kind == PodView::kind()
                    && obj.metadata.namespace == vsts.metadata.namespace)
            // this object is created later with different uid, deletion fails
            ||| obj.metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap()
        }
    };
    let requirements_antecedent = |msg: Message| {
        &&& msg.src is BuiltinController
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::desired_state_is(vsts)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::no_pending_request_to_api_server_from_non_controllers()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::every_in_flight_msg_from_controller_has_kind_as::<VStatefulSetView>(controller_id)(s)
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& forall |vsts| internal_rely_guarantee::no_interfering_request_between_vsts(controller_id, vsts)(s)
        &&& forall |other_id: int| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] rely_guarantee::vsts_rely(other_id)(s)
    };
    assert forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            let key = msg.content.get_delete_request().key;
            match step {
                Step::BuiltinControllersStep(..) => {
                    if (!s.in_flight().contains(msg) && requirements_antecedent(msg)) {
                        let obj = s.resources()[key];
                        let owner_references = obj.metadata.owner_references->0;
                        assert(forall |i| #![trigger owner_references[i]] 0 <= i < owner_references.len() ==> {
                            // the referred owner object does not exist in the cluster state
                            ||| !s.resources().contains_key(owner_reference_to_object_reference(owner_references[i], key.namespace))
                            // or it exists but has a different uid
                            // (which means the actual owner was deleted and another object with the same name gets created again)
                            ||| s.resources()[owner_reference_to_object_reference(owner_references[i], key.namespace)].metadata.uid != Some(owner_references[i].uid)
                        });
                        if obj.metadata.owner_references_contains(vsts.controller_owner_ref())
                            && obj.kind == Kind::PodKind
                            && obj.metadata.namespace == vsts.metadata.namespace {
                            let idx = choose |i| 0 <= i < owner_references.len() && owner_references[i] == vsts.controller_owner_ref();
                            assert(s.resources().contains_key(vsts.object_ref()));
                        }
                    }
                },
                Step::APIServerStep(req_msg_opt) => {
                    let req_msg = req_msg_opt.unwrap();
                    if s.in_flight().contains(msg) && requirements(msg, s) && s_prime.resources().contains_key(key) {
                        if s.resources().contains_key(key) {
                            let obj = s.resources()[key];
                            let owner_references = obj.metadata.owner_references->0;
                            if obj.kind == Kind::PodKind && obj.metadata.namespace == vsts.metadata.namespace {
                                if obj.metadata.owner_references_contains(vsts.controller_owner_ref()) {
                                    let idx = choose |i| 0 <= i < owner_references.len() && owner_references[i] == vsts.controller_owner_ref();
                                    assert(s.resources().contains_key(vsts.object_ref()));
                                } else {
                                    let obj_prime = s_prime.resources()[key];
                                    if obj_prime.metadata.owner_references_contains(vsts.controller_owner_ref()) {
                                        match req_msg.src {
                                            HostId::Controller(id, cr_key) => {
                                                if id == controller_id {
                                                    let other_vsts = VStatefulSetView {
                                                        metadata: ObjectMetaView {
                                                            name: Some(cr_key.name),
                                                            namespace: Some(cr_key.namespace),
                                                            ..ObjectMetaView::default()
                                                        },
                                                        ..VStatefulSetView::default()
                                                    };
                                                    assert(other_vsts.object_ref() == cr_key);
                                                    assert(internal_rely_guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s));
                                                    if resource_get_then_update_request_msg(key)(req_msg) {
                                                        let req = req_msg.content.get_get_then_update_request();
                                                        if req.owner_ref == vsts.controller_owner_ref() {}
                                                    }
                                                } else {
                                                    assert(rely_guarantee::vsts_rely(id)(s));
                                                    if resource_update_request_msg(key)(req_msg) {
                                                        assert(req_msg.content.get_update_request()
                                                            .obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
                                                        assert(false);
                                                    } else if resource_get_then_update_request_msg(key)(req_msg) {
                                                        assert(req_msg.content.get_get_then_update_request()
                                                            .obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
                                                        assert(false);

                                                    }
                                                }
                                            },
                                            HostId::BuiltinController => {
                                                assert(req_msg.content.is_delete_request());
                                            },
                                            _ => { // no_pending_request_to_api_server_from_non_controllers
                                                assert(false);
                                            }
                                        }
                                    }
                                }
                            } 
                        }
                    }
                },
                _ => {}
            }
        }
    };
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::desired_state_is(vsts)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<VStatefulSetView>(controller_id)),
        lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)),
        lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id))
    );
    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(buildin_controllers_do_not_delete_pods_owned_by_vsts(vsts)),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_always_buildin_controllers_do_not_delete_pvcs_owned_by_vsts(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(always(lift_state(rely_guarantee::vsts_rely_conditions_pod_monkey()))),
    spec.entails(always(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(buildin_controllers_do_not_delete_pvcs_owned_by_vsts()))),
{
    let inv = buildin_controllers_do_not_delete_pvcs_owned_by_vsts();
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref()(s)
    };
    lemma_always_all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref(spec, cluster, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: Message| {
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.src is BuiltinController
        } implies {
            let key = msg.content.get_delete_request().key;
            &&& msg.dst is APIServer
            &&& msg.content.is_delete_request()
            &&& !(key.kind == Kind::PersistentVolumeClaimKind
                && exists |vsts_name: StringView| pvc_name_match(key.name, vsts_name))
        } by {
            if s.in_flight().contains(msg) {} else {}
        }
    };
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// similar to above, but for PVCs
// rely_guarantee conditions already prevent other controllers from creating or updating PVCs
// and VSTS controller's internal guarantee says all pvcs it creates have no owner refs
pub open spec fn all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |pvc_key: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(pvc_key)
            &&& pvc_key.kind == Kind::PersistentVolumeClaimKind
            &&& exists |vsts_name: StringView| #[trigger] pvc_name_match(pvc_key.name, vsts_name)
        } ==> {
            let pvc_obj = s.resources()[pvc_key];
            &&& pvc_obj.metadata.owner_references is None
            &&& pvc_obj.metadata.deletion_timestamp is None
            &&& pvc_obj.metadata.finalizers is None
        }
    }
}

#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
pub proof fn lemma_always_all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(always(lift_state(rely_guarantee::vsts_rely_conditions_pod_monkey()))),
    spec.entails(always(lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref()))),
{
    let inv = all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref();
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& rely_guarantee::vsts_rely_conditions(cluster, controller_id)(s)
        &&& rely_guarantee::vsts_rely_conditions_pod_monkey()(s)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)(s)
        &&& every_msg_from_vsts_controller_carries_vsts_key(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_no_pending_request_to_api_server_from_api_server_or_external(spec);
    cluster.lemma_always_all_requests_from_pod_monkey_are_api_pod_requests(spec);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    internal_rely_guarantee::internal_guarantee_condition_holds_on_all_vsts(spec, cluster, controller_id);
    lemma_always_every_msg_from_vsts_controller_carries_vsts_key(spec, cluster, controller_id);

    assert forall|s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                let resp_msg = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
                assert(msg.content is APIRequest);
                assert(resp_msg.content is APIResponse);
                if is_ok_resp(resp_msg.content->APIResponse_0) { // otherwise, etcd is not changed
                    match msg.src {
                        HostId::Controller(other_id, cr_key) => {
                            if other_id != controller_id {
                                assert(cluster.controller_models.remove(controller_id).contains_key(other_id));
                                assert(rely_guarantee::vsts_rely(other_id)(s));
                                assert forall |pvc_key: ObjectRef| {
                                    &&& #[trigger] s_prime.resources().contains_key(pvc_key)
                                    &&& pvc_key.kind == Kind::PersistentVolumeClaimKind
                                    &&& exists |vsts_name: StringView| #[trigger] pvc_name_match(pvc_key.name, vsts_name)
                                } implies {
                                    let pvc_obj = s_prime.resources()[pvc_key];
                                    &&& pvc_obj.metadata.owner_references is None
                                    &&& pvc_obj.metadata.deletion_timestamp is None
                                    &&& pvc_obj.metadata.finalizers is None
                                } by {
                                    pvc_name_match_implies_has_vsts_prefix(pvc_key.name);
                                    match (msg.content->APIRequest_0) {
                                        APIRequest::CreateRequest(req) => {
                                            if req.key().kind == Kind::PersistentVolumeClaimKind {
                                                assert(rely_guarantee::rely_create_req(req));
                                                let name = if req.obj.metadata.name is Some {
                                                    req.obj.metadata.name->0
                                                } else {
                                                    generated_name(s.api_server, req.obj.metadata.generate_name->0)
                                                };
                                                assert(!has_vsts_prefix(name)) by {
                                                    if req.obj.metadata.name is Some {
                                                        assert(!has_vsts_prefix(req.obj.metadata.name->0));
                                                    } else {
                                                        assert(req.obj.metadata.generate_name is Some);
                                                        assert(!has_vsts_prefix(req.obj.metadata.generate_name->0));
                                                        generated_name_reflects_prefix(s.api_server, req.obj.metadata.generate_name->0, VStatefulSetView::kind()->CustomResourceKind_0);
                                                    }
                                                }
                                                let created_obj_key = ObjectRef {
                                                    kind: Kind::PersistentVolumeClaimKind,
                                                    namespace: req.namespace,
                                                    name: name,
                                                };
                                                assert(s_prime.resources().contains_key(created_obj_key));
                                                no_vsts_prefix_implies_no_pvc_name_match(name);
                                                if pvc_key == created_obj_key {
                                                    assert(!exists |vsts_name: StringView| #[trigger] pvc_name_match(name, vsts_name));
                                                    assert(false);
                                                }
                                            }
                                        },
                                        _ => {},
                                    }
                                }
                            } else {
                                let any_vsts = make_vsts();
                                let vsts_with_key = VStatefulSetView {
                                    metadata: ObjectMetaView {
                                        name: Some(cr_key.name),
                                        namespace: Some(cr_key.namespace),
                                        ..any_vsts.metadata
                                    },
                                    ..any_vsts
                                };
                                assert(internal_rely_guarantee::no_interfering_request_between_vsts(controller_id, vsts_with_key)(s));
                                assert(s.in_flight().contains(msg)); // trigger
                            }
                        },
                        HostId::BuiltinController => {}, // must be delete requests
                        HostId::PodMonkey => {}, // must be pod requests
                        _ => {}
                    }
                } else {
                    assert(s_prime.resources() == s.resources());
                }
            },
            _ => {}
        }
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(rely_guarantee::vsts_rely_conditions(cluster, controller_id)),
        lift_state(rely_guarantee::vsts_rely_conditions_pod_monkey()),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(internal_rely_guarantee::vsts_internal_guarantee_conditions(controller_id)),
        lift_state(every_msg_from_vsts_controller_carries_vsts_key(controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

pub proof fn lemma_always_there_is_no_request_msg_to_external_from_controller(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
{
    let inv = Cluster::there_is_no_request_msg_to_external_from_controller(controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);

    VStatefulSetReconcileState::marshal_preserves_integrity();
    VStatefulSetView::marshal_preserves_integrity();

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

pub open spec fn every_msg_from_vsts_controller_carries_vsts_key(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            let content = msg.content;
            &&& s.in_flight().contains(msg)
            &&& msg.src is Controller
            &&& msg.src->Controller_0 == controller_id
        } ==> msg.src->Controller_1.kind == VStatefulSetView::kind()
    }
}

pub proof fn lemma_always_every_msg_from_vsts_controller_carries_vsts_key(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(every_msg_from_vsts_controller_carries_vsts_key(controller_id)))),
{
    let inv = every_msg_from_vsts_controller_carries_vsts_key(controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime)
        implies inv(s_prime) by {
        let new_msgs = s_prime.in_flight().sub(s.in_flight());

        assert forall |msg: Message|
            inv(s)
            && #[trigger] s_prime.in_flight().contains(msg)
            && msg.src.is_controller_id(controller_id)
            implies msg.src->Controller_1.kind == VStatefulSetView::kind() by {
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

pub open spec fn vsts_in_schedule_has_no_deletion_timestamp(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| s.scheduled_reconciles(controller_id).contains_key(vsts.object_ref()) ==> {
        &&& s.scheduled_reconciles(controller_id)[vsts.object_ref()].metadata.deletion_timestamp is None
        &&& VStatefulSetView::unmarshal(s.scheduled_reconciles(controller_id)[vsts.object_ref()]).unwrap().metadata().deletion_timestamp is None
    }
}

pub open spec fn vsts_in_ongoing_reconciles_has_no_deletion_timestamp(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()) ==> {
        &&& s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr.metadata.deletion_timestamp is None
        &&& VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr).unwrap().metadata().deletion_timestamp is None
    }
}

pub open spec fn vsts_in_schedule_has_the_same_name_and_namespace_as_vsts(
    vsts: VStatefulSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| s.scheduled_reconciles(controller_id).contains_key(vsts.object_ref()) ==> {
        let scheduled_cr = VStatefulSetView::unmarshal(s.scheduled_reconciles(controller_id)[vsts.object_ref()]).unwrap();
        &&& vsts.metadata.name is Some
        &&& vsts.metadata.namespace is Some
        &&& scheduled_cr.metadata.name->0 == vsts.metadata.name->0
        &&& scheduled_cr.metadata.namespace->0 == vsts.metadata.namespace->0
    }
}

pub open spec fn vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(
    vsts: VStatefulSetView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()) ==> {
        let triggering_cr = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts.object_ref()].triggering_cr).unwrap();
        &&& vsts.metadata.name is Some
        &&& vsts.metadata.namespace is Some
        &&& triggering_cr.metadata.name->0 == vsts.metadata.name->0
        &&& triggering_cr.metadata.namespace->0 == vsts.metadata.namespace->0
    }
}

pub proof fn lemma_eventually_always_vsts_in_schedule_has_the_same_name_and_namespace_as_vsts(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vsts_in_schedule_has_the_same_name_and_namespace_as_vsts(vsts, controller_id))))),
{
    let p = |s| Cluster::desired_state_is(vsts)(s);
    let q = vsts_in_schedule_has_the_same_name_and_namespace_as_vsts(vsts, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::desired_state_is(vsts)(s)
        &&& Cluster::desired_state_is(vsts)(s_prime)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    };
    always_to_always_later(spec, lift_state(Cluster::desired_state_is(vsts)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::desired_state_is(vsts)),
        later(lift_state(Cluster::desired_state_is(vsts))),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
    );
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, vsts.object_ref(), stronger_next, p, q);
    temp_pred_equality(true_pred().and(lift_state(Cluster::desired_state_is(vsts))), lift_state(p));
    leads_to_by_borrowing_inv(spec, true_pred(), lift_state(q), lift_state(Cluster::desired_state_is(vsts)));
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(q));
}

#[verifier(rlimit(100))]
#[verifier(spinoff_prover)]
pub proof fn lemma_eventually_always_vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(vsts_in_schedule_has_the_same_name_and_namespace_as_vsts(vsts, controller_id)))),
    spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, vsts.object_ref())))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id))))),
{
    let not_scheduled_or_reconcile = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())
        &&& !s.scheduled_reconciles(controller_id).contains_key(vsts.object_ref())
    };
    let scheduled_and_not_reconcile = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(vsts.object_ref())
    };
    always_to_always_later(spec, lift_state(Cluster::desired_state_is(vsts)));
    assert(spec.entails(lift_state(not_scheduled_or_reconcile).leads_to(lift_state(scheduled_and_not_reconcile)))) by {
        let (pre, post) = (not_scheduled_or_reconcile, scheduled_and_not_reconcile);
        let stronger_next = |s, s_prime| {
            &&& cluster.next()(s, s_prime)
            &&& Cluster::desired_state_is(vsts)(s)
            &&& Cluster::desired_state_is(vsts)(s_prime)
            &&& Cluster::there_is_the_controller_state(controller_id)(s)
        };
        combine_spec_entails_always_n!(
            spec, lift_action(stronger_next),
            lift_action(cluster.next()),
            lift_state(Cluster::desired_state_is(vsts)),
            later(lift_state(Cluster::desired_state_is(vsts))),
            lift_state(Cluster::there_is_the_controller_state(controller_id))
        );
        let stronger_pre = and!(pre, Cluster::desired_state_is(vsts));
        cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, vsts.object_ref(), stronger_next, stronger_pre, post);
        temp_pred_equality(lift_state(pre).and(lift_state(Cluster::desired_state_is(vsts))), lift_state(stronger_pre));
        leads_to_by_borrowing_inv(spec, lift_state(pre), lift_state(post), lift_state(Cluster::desired_state_is(vsts)));
    }
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& vsts_in_schedule_has_the_same_name_and_namespace_as_vsts(vsts, controller_id)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(vsts_in_schedule_has_the_same_name_and_namespace_as_vsts(vsts, controller_id)),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    assert(spec.entails(lift_state(scheduled_and_not_reconcile).leads_to(lift_state(vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id))))) by {
        let pre = scheduled_and_not_reconcile;
        let post = vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id);
        assert(forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && cluster.controller_next().forward((controller_id, None, Some(vsts.object_ref())))(s, s_prime) ==> post(s_prime));
        cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, (None, Some(vsts.object_ref())), stronger_next, ControllerStep::RunScheduledReconcile, pre, post);
    }
    leads_to_trans(spec, lift_state(not_scheduled_or_reconcile), lift_state(scheduled_and_not_reconcile), lift_state(vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id)));
    assert(spec.entails(true_pred().leads_to(always(lift_state(vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id)))))) by {
        let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()); // Cluster::reconcile_idle
        or_leads_to_combine_and_equality!(
            spec, lift_state(reconcile_idle),
            lift_state(scheduled_and_not_reconcile), lift_state(not_scheduled_or_reconcile);
            lift_state(vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id))
        );
        leads_to_trans(spec, true_pred(), lift_state(reconcile_idle), lift_state(vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id)));
        leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(vsts_in_reconciles_has_the_same_name_and_namespace_as_vsts(vsts, controller_id)));
    }
}

pub proof fn lemma_eventually_always_vsts_in_schedule_has_no_deletion_timestamp(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vsts_in_schedule_has_no_deletion_timestamp(vsts, controller_id))))),
{
    let p = |s| Cluster::desired_state_is(vsts)(s);
    let q = vsts_in_schedule_has_no_deletion_timestamp(vsts, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::desired_state_is(vsts)(s)
        &&& Cluster::desired_state_is(vsts)(s_prime)
    };
    always_to_always_later(spec, lift_state(Cluster::desired_state_is(vsts)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::desired_state_is(vsts)),
        later(lift_state(Cluster::desired_state_is(vsts)))
    );

    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, vsts.object_ref(), stronger_next, p, q);
    temp_pred_equality(true_pred().and(lift_state(Cluster::desired_state_is(vsts))), lift_state(p));
    leads_to_by_borrowing_inv(spec, true_pred(), lift_state(q), lift_state(Cluster::desired_state_is(vsts)));
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(q));
}

pub proof fn lemma_eventually_always_vsts_in_ongoing_reconciles_has_no_deletion_timestamp(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(vsts_in_schedule_has_no_deletion_timestamp(vsts, controller_id)))),
    spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())))),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vsts_in_ongoing_reconciles_has_no_deletion_timestamp(vsts, controller_id))))),
{
    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref());
    let q = vsts_in_ongoing_reconciles_has_no_deletion_timestamp(vsts, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vsts)(s)
        &&& Cluster::desired_state_is(vsts)(s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& vsts_in_schedule_has_no_deletion_timestamp(vsts, controller_id)(s)
    };
    always_to_always_later(spec, lift_state(Cluster::desired_state_is(vsts)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vsts)),
        later(lift_state(Cluster::desired_state_is(vsts))),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(vsts_in_schedule_has_no_deletion_timestamp(vsts, controller_id))
    );
    leads_to_weaken(
        spec,
        true_pred(), lift_state(reconcile_idle),
        true_pred(), lift_state(q)
    );
    assert forall |s, s_prime| q(s) && #[trigger] stronger_next(s, s_prime) implies q(s_prime) by {
        if s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()) {}
    }
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(q));
}

}
