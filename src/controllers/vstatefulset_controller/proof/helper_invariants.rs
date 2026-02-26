use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::{
    spec::{
        api_server::{state_machine::*, types::InstalledTypes}, 
        cluster::*, 
        message::*,
        controller::types::ControllerStep,
    },
    proof::api_server::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    trusted::{
        liveness_theorem::*, 
        rely::*, 
        spec_types::*, 
        step::*
    },
    proof::{
        predicate::*,
        guarantee,
        helper_lemmas::*,
    },
};
use crate::vstd_ext::{seq_lib::*, string_view::*};
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
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        }
    }
}

// TODO: strengthen to be resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref
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
            &&& exists |uid: int| #![trigger dummy(uid)] obj.metadata.owner_references == Some(seq![OwnerReferenceView{
                uid: uid,
                ..vsts.controller_owner_ref()
            }])
        }
    }
}

#[verifier(external_body)]
proof fn lemma_always_all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(always(lift_state(vsts_rely_conditions_pod_monkey(cluster.installed_types)))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)))),
{
    let inv = all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& vsts_rely_conditions(cluster, controller_id)(s)
        &&& vsts_rely_conditions_pod_monkey(cluster.installed_types)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& guarantee::vsts_internal_guarantee_conditions(controller_id)(s)
        &&& every_msg_from_vsts_controller_carries_vsts_key(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_no_pending_request_to_api_server_from_api_server_or_external(spec);
    cluster.lemma_always_all_requests_from_pod_monkey_are_api_pod_requests(spec);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    guarantee::internal_guarantee_condition_holds_on_all_vsts(spec, cluster, controller_id);
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
                    assert forall |pod_key: ObjectRef| {
                        &&& #[trigger] s_prime.resources().contains_key(pod_key)
                        &&& pod_key.kind == Kind::PodKind
                        &&& pod_key.namespace == vsts.object_ref().namespace
                        &&& pod_name_match(pod_key.name, vsts.object_ref().name)
                    } implies {
                        let obj = s_prime.resources()[pod_key];
                        &&& obj.metadata.deletion_timestamp is None
                        &&& obj.metadata.finalizers is None
                        &&& exists |old_vsts: VStatefulSetView| { // have same key, but potentailly different uid
                            &&& obj.metadata.owner_references_contains(#[trigger] old_vsts.controller_owner_ref())
                            &&& old_vsts.metadata.namespace == vsts.metadata.namespace
                            &&& old_vsts.metadata.name == vsts.metadata.name
                        }
                    } by {
                        let obj_prime = s_prime.resources()[pod_key];
                        match msg.src {
                            HostId::Controller(other_id, cr_key) => {
                                if other_id != controller_id {
                                    assert(cluster.controller_models.remove(controller_id).contains_key(other_id));
                                    assert(vsts_rely(other_id, cluster.installed_types)(s));
                                    match (msg.content->APIRequest_0) {
                                        APIRequest::CreateRequest(req) => {
                                            if req.key().kind == Kind::PodKind {
                                                assert(rely_create_pod_req(req));
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
                                                        no_vsts_prefix_implies_no_vsts_previx_in_generate_name_field(s.api_server, req.obj.metadata.generate_name->0);
                                                    }
                                                }
                                                let created_obj_key = ObjectRef {
                                                    kind: Kind::PodKind,
                                                    namespace: req.namespace,
                                                    name: name,
                                                };
                                                assert(s_prime.resources().contains_key(created_obj_key));
                                                // no_vsts_prefix_implies_no_pod_name_match(name);
                                                if pod_key != created_obj_key {
                                                    assert(s.resources().contains_key(pod_key));
                                                } else {
                                                    assert(!pod_name_match(name, vsts.object_ref().name));
                                                    assert(false);
                                                }
                                            }
                                        },
                                        APIRequest::UpdateRequest(req) => {
                                            if req.key().kind == Kind::PodKind {
                                                assert(rely_update_pod_req(req)(s));
                                            }
                                        },
                                        APIRequest::DeleteRequest(req) => {
                                            if req.key.kind == Kind::PodKind {
                                                assert(rely_delete_pod_req(req)(s));
                                            }
                                        },
                                        APIRequest::GetThenUpdateRequest(req) => {
                                            if req.key().kind == Kind::PodKind {
                                                assert(rely_get_then_update_pod_req(req));
                                                assert(req.owner_ref.kind != VStatefulSetView::kind());
                                                if req.key() == pod_key && s.resources()[req.key()].metadata.owner_references_contains(req.owner_ref) && req.owner_ref.controller == Some(true) {
                                                    let obj = s.resources()[pod_key];
                                                    let old_vsts = choose |old_vsts: VStatefulSetView| {
                                                        &&& obj.metadata.owner_references_contains(#[trigger] old_vsts.controller_owner_ref())
                                                        &&& old_vsts.metadata.namespace == vsts.metadata.namespace
                                                        &&& old_vsts.metadata.name == vsts.metadata.name
                                                    };
                                                    lemma_singleton_contains_at_most_one_element(
                                                        obj.metadata.owner_references->0.filter(controller_owner_filter()),
                                                        req.owner_ref,
                                                        old_vsts.controller_owner_ref()
                                                    );
                                                } else {
                                                    assert(s_prime.resources()[pod_key] == s.resources()[pod_key]);
                                                }
                                            }
                                        },
                                        APIRequest::GetThenDeleteRequest(req) => {
                                            if req.key().kind == Kind::PodKind {
                                                assert(rely_get_then_delete_pod_req(req));
                                            }
                                        },
                                        _ => {}
                                    }
                                } else if cr_key != vsts.object_ref() {
                                    let havoc_vsts = make_vsts();
                                    let vsts_with_key = VStatefulSetView {
                                        metadata: ObjectMetaView {
                                            name: Some(cr_key.name),
                                            namespace: Some(cr_key.namespace),
                                            ..havoc_vsts.metadata
                                        },
                                        ..havoc_vsts
                                    };
                                    assert(vsts_with_key.object_ref() == cr_key);
                                    assert(guarantee::no_interfering_request_between_vsts(controller_id, vsts_with_key)(s));
                                    assert(s.in_flight().contains(msg)); // trigger
                                    if msg.content.is_get_then_update_request() {
                                        let req = msg.content.get_get_then_update_request();
                                        assert(guarantee::vsts_internal_guarantee_get_then_update_req(req, vsts_with_key));
                                        if req.key() == pod_key {
                                            if cr_key.namespace == vsts.object_ref().namespace {
                                                assert(cr_key.name != vsts.object_ref().name);
                                                assert(pod_name_match(req.obj.metadata.name->0, cr_key.name));
                                                vsts_name_non_eq_implies_no_pod_name_match(req.obj.metadata.name->0, cr_key.name, vsts.object_ref().name);
                                                assert(req.key() != pod_key);
                                            }
                                        }
                                    } else if msg.content.is_create_request() {
                                        let req = msg.content.get_create_request();
                                        assert(guarantee::vsts_internal_guarantee_create_req(req, vsts_with_key));
                                        if req.key() == pod_key {
                                            if cr_key.namespace == vsts.object_ref().namespace {
                                                assert(cr_key.name != vsts.object_ref().name);
                                                assert(pod_name_match(req.obj.metadata.name->0, cr_key.name));
                                                vsts_name_non_eq_implies_no_pod_name_match(req.obj.metadata.name->0, cr_key.name, vsts.object_ref().name);
                                                assert(req.key() != pod_key);
                                            }
                                        }
                                    }
                                } else {
                                    assert(guarantee::no_interfering_request_between_vsts(controller_id, vsts)(s));
                                    if s.resources().contains_key(pod_key) && msg.content.is_get_then_update_request() {
                                        let obj = s.resources()[pod_key];
                                        let req = msg.content.get_get_then_update_request();
                                        if req.key() == pod_key {
                                            if !obj.metadata.owner_references_contains(req.owner_ref) {
                                                assert(!is_ok_resp(resp_msg.content->APIResponse_0));
                                                assert(false);
                                            }
                                            if req.owner_ref != obj.metadata.owner_references->0[0] {
                                                lemma_singleton_contains_at_most_one_element(
                                                    obj.metadata.owner_references->0.filter(controller_owner_filter()),
                                                    req.owner_ref,
                                                    obj.metadata.owner_references->0[0]
                                                );
                                            }
                                            let obj_prime = s_prime.resources()[pod_key];
                                            assert(guarantee::vsts_internal_guarantee_get_then_update_req(req, vsts));
                                            assert(obj_prime.metadata.owner_references_contains(req.owner_ref)) by {
                                                let singleton = Seq::empty().push(req.owner_ref);
                                                assert(singleton.contains(req.owner_ref)) by {
                                                    assert(singleton[0] == req.owner_ref);
                                                }
                                                seq_filter_contains_implies_seq_contains(
                                                    req.obj.metadata.owner_references->0, controller_owner_filter(), req.owner_ref
                                                );
                                            }
                                        } else {}
                                    } else if !s.resources().contains_key(pod_key) && msg.content.is_create_request() {
                                        let req = msg.content.get_create_request();
                                        if req.key() == pod_key {
                                            assert(guarantee::vsts_internal_guarantee_create_req(req, vsts));
                                            let owner_reference = choose |owner_reference: OwnerReferenceView| {
                                                &&& req.obj.metadata.owner_references == Some(Seq::empty().push(owner_reference))
                                                &&& #[trigger] owner_reference_eq_without_uid(owner_reference, vsts.controller_owner_ref())
                                            } ;
                                            let new_vsts = VStatefulSetView {
                                                metadata: ObjectMetaView {
                                                    name: vsts.metadata.name,
                                                    namespace: vsts.metadata.namespace,
                                                    uid: Some(owner_reference.uid),
                                                    ..vsts.metadata
                                                },
                                                ..vsts
                                            };
                                            assert(new_vsts.controller_owner_ref() == owner_reference);
                                            assert(req.obj.metadata.owner_references_contains(new_vsts.controller_owner_ref())) by {
                                                assert(req.obj.metadata.owner_references->0[0] == new_vsts.controller_owner_ref());
                                            }
                                            let obj_prime = s_prime.resources()[pod_key];
                                            assert(obj_prime.metadata.owner_references == req.obj.metadata.owner_references) by {
                                                assert(obj_prime.metadata.owner_references is Some);
                                                assert(obj_prime.metadata.owner_references->0.len() == 1);
                                                assert(obj_prime.metadata.owner_references->0[0] == new_vsts.controller_owner_ref());
                                            }
                                        }
                                    } // GetThenDeleteRequest is trivial to proof
                                }
                            },
                            HostId::BuiltinController => {}, // must be delete requests   
                            HostId::PodMonkey => {
                                assert(vsts_rely_conditions_pod_monkey(cluster.installed_types)(s));
                                if msg.content.is_create_request() {
                                    let req = msg.content.get_create_request();
                                    assert(rely_create_pod_req(req));
                                    let name = if req.obj.metadata.name is Some {
                                        req.obj.metadata.name->0
                                    } else {
                                        generated_name(s.api_server, req.obj.metadata.generate_name->0)
                                    };
                                    assert(!pod_name_match(name, vsts.object_ref().name)) by {
                                        if req.obj.metadata.name is Some {
                                            no_vsts_prefix_implies_no_pod_name_match(req.obj.metadata.name->0);
                                        } else {
                                            no_vsts_prefix_implies_no_vsts_previx_in_generate_name_field(s.api_server, req.obj.metadata.generate_name->0);
                                            let generate_name = generated_name(s.api_server, req.obj.metadata.generate_name->0);
                                            no_vsts_prefix_implies_no_pod_name_match(generate_name);
                                        }
                                    }
                                } else {
                                    // Deletion/Update/UpdateStatus are not possible
                                }
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
        lift_state(vsts_rely_conditions(cluster, controller_id)),
        lift_state(vsts_rely_conditions_pod_monkey(cluster.installed_types)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)),
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
proof fn lemma_eventually_always_all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(
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

proof fn lemma_eventually_always_every_create_msg_sets_owner_references_as(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView, key: ObjectRef
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)))),
    spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
    spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    key.kind == Kind::PodKind,
    key.namespace == vsts.object_ref().namespace,
    pod_name_match(key.name, vsts.object_ref().name),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(Cluster::every_create_msg_sets_owner_references_as(key, owner_reference_requirements(vsts)))))),
{
    let requirements = |msg: Message, s: ClusterState|
        resource_create_request_msg(key)(msg) ==> owner_reference_requirements(vsts)(msg.content.get_create_request().obj.metadata.owner_references);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vsts)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)(s)
        &&& Cluster::no_pending_request_to_api_server_from_non_controllers()(s_prime)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s_prime)
        &&& Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))(s_prime)
        &&& guarantee::vsts_internal_guarantee_conditions(controller_id)(s_prime)
        &&& vsts_rely_conditions(cluster, controller_id)(s_prime)
    };
    assert forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
            implies requirements(msg, s_prime) by {
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
                                assert(guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s_prime));
                                vsts_name_non_eq_implies_no_pod_name_match(key.name, other_vsts.object_ref().name, vsts.object_ref().name);
                                assert(false);
                            }
                        } else {
                            let req = msg.content.get_create_request();
                            if msg.content is APIRequest && req.key() == key && req.obj.metadata.name is Some {
                                assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                assert(vsts_rely(id)(s_prime));
                                assert(false);
                            }
                        }
                    },
                    _ => {}
                }
            }
        }
    };
    always_to_always_later(spec, lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()));
    always_to_always_later(spec, lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()));
    always_to_always_later(spec, lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))));
    always_to_always_later(spec, lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)));
    always_to_always_later(spec, lift_state(vsts_rely_conditions(cluster, controller_id)));
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vsts)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)),
        later(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())),
        later(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        later(lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id)))),
        later(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id))),
        later(lift_state(vsts_rely_conditions(cluster, controller_id)))
    );
    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(Cluster::every_create_msg_sets_owner_references_as(key, owner_reference_requirements(vsts))),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

proof fn lemma_eventually_always_every_update_msg_sets_owner_references_as(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView, key: ObjectRef
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)))),
    spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
    spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    key.kind == Kind::PodKind,
    key.namespace == vsts.object_ref().namespace,
    pod_name_match(key.name, vsts.object_ref().name),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(Cluster::every_update_msg_sets_owner_references_as(key, owner_reference_requirements(vsts)))))),
{
    assert(has_vsts_prefix(key.name));
    let requirements = |msg: Message, s: ClusterState| {
        &&& resource_update_request_msg(key)(msg) ==> false // no update request is sent
        &&& resource_get_then_update_request_msg(key)(msg) ==> owner_reference_requirements(vsts)(msg.content.get_get_then_update_request().obj.metadata.owner_references)
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vsts)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)(s)
        &&& Cluster::no_pending_request_to_api_server_from_non_controllers()(s_prime)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s_prime)
        &&& Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))(s_prime)
        &&& guarantee::vsts_internal_guarantee_conditions(controller_id)(s_prime)
        &&& vsts_rely_conditions(cluster, controller_id)(s_prime)
    };
    assert forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
            implies requirements(msg, s_prime) by {
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
                                assert(guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s_prime));
                                if resource_get_then_update_request_msg(key)(msg) {
                                    vsts_name_non_eq_implies_no_pod_name_match(key.name, other_vsts.object_ref().name, vsts.object_ref().name);
                                    assert(false);
                                } else if resource_get_then_update_request_msg(key)(msg) {
                                    assert(false);
                                }
                            }
                        } else {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(vsts_rely(id)(s_prime));
                        }
                    },
                    _ => {}
                }
            }
        }
    };
    always_to_always_later(spec, lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()));
    always_to_always_later(spec, lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()));
    always_to_always_later(spec, lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id))));
    always_to_always_later(spec, lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)));
    always_to_always_later(spec, lift_state(vsts_rely_conditions(cluster, controller_id)));
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vsts)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)),
        later(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())),
        later(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        later(lift_state(Cluster::every_in_flight_req_msg_satisfies(all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref(vsts, controller_id)))),
        later(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id))),
        later(lift_state(vsts_rely_conditions(cluster, controller_id)))
    );
    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    entails_preserved_by_always(
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)),
        lift_state(Cluster::every_update_msg_sets_owner_references_as(key, owner_reference_requirements(vsts)))
    );
    entails_implies_leads_to(spec,
        always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))),
        always(lift_state(Cluster::every_update_msg_sets_owner_references_as(key, owner_reference_requirements(vsts))))
    );
    leads_to_trans(spec,
        true_pred(),
        always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))),
        always(lift_state(Cluster::every_update_msg_sets_owner_references_as(key, owner_reference_requirements(vsts))))
    );
}

pub proof fn lemma_eventually_always_every_create_msg_with_generate_name_matching_key_set_owner_references_as(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView, key: ObjectRef
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
    spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)))),
    spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers()))),
    spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
    spec.entails(always(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)))),
    spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    key.kind == Kind::PodKind,
    key.namespace == vsts.object_ref().namespace,
    pod_name_match(key.name, vsts.object_ref().name),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(key, owner_reference_requirements(vsts)))))),
{
    // this is weaker than the pre in every_create_msg_with_generate_name_matching_key_set_owner_references_as
    // resulting in stronger post
    let requirements = |msg: Message, s: ClusterState| {
        resource_create_request_msg_without_name(key.kind, key.namespace)(msg)
        && has_vsts_prefix(msg.content.get_create_request().obj.metadata.generate_name->0)
            ==> owner_reference_requirements(vsts)(msg.content.get_create_request().obj.metadata.owner_references)
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)(s)
        &&& Cluster::no_pending_request_to_api_server_from_non_controllers()(s_prime)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s_prime)
        &&& guarantee::vsts_internal_guarantee_conditions(controller_id)(s_prime)
        &&& vsts_rely_conditions(cluster, controller_id)(s_prime)
    };
    assert forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
            implies requirements(msg, s_prime) by {
            if !s.in_flight().contains(msg) && resource_create_request_msg_without_name(key.kind, key.namespace)(msg) {
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
                            assert(guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s_prime));
                            assert(guarantee::vsts_internal_guarantee_create_req(req, vsts));
                        } else {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(vsts_rely(id)(s_prime));
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
    always_to_always_later(spec, lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)));
    always_to_always_later(spec, lift_state(vsts_rely_conditions(cluster, controller_id)));
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as(controller_id, vsts)),
        later(lift_state(Cluster::no_pending_request_to_api_server_from_non_controllers())),
        later(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        later(lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id))),
        later(lift_state(vsts_rely_conditions(cluster, controller_id)))
    );
    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)).satisfied_by(ex)
        implies lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(key, owner_reference_requirements(vsts))).satisfied_by(ex) by {
        let s = ex.head();
        assert forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst is APIServer && msg.content is APIRequest
            &&& requirements(msg, s)
        } implies {
            resource_create_request_msg_without_name(key.kind, key.namespace)(msg)
            ==> generated_name(s.api_server, msg.content.get_create_request().obj.metadata.generate_name->0) == key.name
                ==> owner_reference_requirements(vsts)(msg.content.get_create_request().obj.metadata.owner_references)
        } by {
            if generated_name(s.api_server, msg.content.get_create_request().obj.metadata.generate_name->0) == key.name {
                generated_name_reflects_prefix(s.api_server, msg.content.get_create_request().obj.metadata.generate_name->0, "vstatefulset"@);
            }
        }
    };
    entails_preserved_by_always(
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements)),
        lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(key, owner_reference_requirements(vsts)))
    );
    entails_implies_leads_to(spec,
        always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))),
        always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(key, owner_reference_requirements(vsts))))
    );
    leads_to_trans(spec,
        true_pred(),
        always(lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))),
        always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(key, owner_reference_requirements(vsts))))
    );
}

// TODO: resort to lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr
// I want to use Basilisk but they don't support Verus/liveness verification yet
pub proof fn lemma_eventually_pod_in_etcd_matching_vsts_has_correct_owner_ref(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView, key: ObjectRef
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
    spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
    spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    spec.entails(always(lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)))),
    spec.entails(always(lift_state(Cluster::every_create_msg_sets_owner_references_as(key, owner_reference_requirements(vsts))))),
    spec.entails(always(lift_state(Cluster::every_update_msg_sets_owner_references_as(key, owner_reference_requirements(vsts))))),
    spec.entails(always(lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(key, owner_reference_requirements(vsts))))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    key.kind == Kind::PodKind,
    key.namespace == vsts.object_ref().namespace,
    pod_name_match(key.name, vsts.object_ref().name),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(Cluster::objects_owner_references_satisfies(key, owner_reference_requirements(vsts)))))),
{
    assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)).satisfied_by(ex)
        implies lift_state(Cluster::object_has_no_finalizers(key)).satisfied_by(ex) by {
        let s = ex.head();
        if s.resources().contains_key(key) {
            let obj = s.resources()[key];
            assert(obj.metadata.finalizers is None);
        }
    };
    entails_preserved_by_always(
        lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)),
        lift_state(Cluster::object_has_no_finalizers(key))
    );
    entails_trans(spec,
        always(lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts))),
        always(lift_state(Cluster::object_has_no_finalizers(key)))
    );
    let partial_spec = lift_state(and!(
        Cluster::desired_state_is(vsts),
        all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts),
        Cluster::every_create_msg_sets_owner_references_as(key, owner_reference_requirements(vsts)),
        Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(key, owner_reference_requirements(vsts))
    ));
    invariant_n!(spec, partial_spec,
        lift_state(Cluster::objects_owner_references_violates(key, owner_reference_requirements(vsts))).implies(lift_state(Cluster::garbage_collector_deletion_enabled(key))),
        lift_state(Cluster::desired_state_is(vsts)),
        lift_state(all_pods_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_and_one_owner_ref(vsts)),
        lift_state(Cluster::every_create_msg_sets_owner_references_as(key, owner_reference_requirements(vsts))),
        lift_state(Cluster::every_create_msg_with_generate_name_matching_key_set_owner_references_as(key, owner_reference_requirements(vsts)))
    );
    cluster.lemma_eventually_objects_owner_references_satisfies(spec, key, owner_reference_requirements(vsts));
}

// stronger version of all_requests_from_builtin_controllers_are_api_delete_requests
// as guaranteed by rely condition, PVC's owner_references remains None
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

pub open spec fn buildin_controllers_do_not_delete_pods_owned_by_vsts(vsts_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src is BuiltinController
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
        } ==> {
            let key = msg.content.get_delete_request().key;
            &&& msg.content.is_delete_request()
            &&& !{
                &&& key.kind == Kind::PodKind
                &&& key.namespace == vsts_key.namespace
                &&& pod_name_match(key.name, vsts_key.name)
            }
        }
    }
}

pub proof fn lemma_eventually_buildin_controllers_do_not_delete_pods_owned_by_vsts(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
    spec.entails(always(lift_state(all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(buildin_controllers_do_not_delete_pods_owned_by_vsts(vsts.object_ref()))))),
{
    let requirements = |msg: Message, s: ClusterState| {
        &&& s.in_flight().contains(msg)
        &&& msg.src is BuiltinController
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
    } ==> {
        let key = msg.content.get_delete_request().key;
        &&& msg.content.is_delete_request()
        &&& !{
            &&& key.kind == Kind::PodKind
            &&& key.namespace == vsts.object_ref().namespace
            &&& pod_name_match(key.name, vsts.object_ref().name)
        }
    };
    let requirements_antecedent = |msg: Message, s: ClusterState| {
        &&& s.in_flight().contains(msg)
        &&& msg.src is BuiltinController
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
    };
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::desired_state_is(vsts)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts)(s)
    };
    assert forall |s, s_prime: ClusterState| #[trigger] stronger_next(s, s_prime) implies Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)(s, s_prime) by {
        assert forall |msg: Message| (!s.in_flight().contains(msg) || requirements(msg, s)) && #[trigger] s_prime.in_flight().contains(msg)
        implies requirements(msg, s_prime) by {
            if !s.in_flight().contains(msg) && requirements_antecedent(msg, s_prime) {
                let key = msg.content.get_delete_request().key;
                if {
                    &&& key.kind == Kind::PodKind
                    &&& key.namespace == vsts.object_ref().namespace
                    &&& pod_name_match(key.name, vsts.object_ref().name)
                    &&& s.resources().contains_key(key)
                } {
                    let obj = s.resources()[key];
                    seq_filter_contains_implies_seq_contains(obj.metadata.owner_references->0, controller_owner_filter(), vsts.controller_owner_ref());
                    assert(false);
                }
            }
        }
    };
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::desired_state_is(vsts)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts))
    );
    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(buildin_controllers_do_not_delete_pods_owned_by_vsts(vsts.object_ref())),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

pub proof fn lemma_always_buildin_controllers_do_not_delete_pvcs_owned_by_vsts(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(always(lift_state(vsts_rely_conditions_pod_monkey()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(buildin_controllers_do_not_delete_pvcs_owned_by_vsts()))),
{
    let inv = buildin_controllers_do_not_delete_pvcs_owned_by_vsts();
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& all_pvcs_in_etcd_matching_vsts_have_no_owner_ref()(s)
    };
    lemma_always_all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(spec, cluster, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(all_pvcs_in_etcd_matching_vsts_have_no_owner_ref())
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
// rely conditions already prevent other controllers from creating or updating PVCs
// and VSTS controller's internal guarantee says all pvcs it creates have no owner refs
pub open spec fn all_pvcs_in_etcd_matching_vsts_have_no_owner_ref() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |pvc_key: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(pvc_key)
            &&& pvc_key.kind == Kind::PersistentVolumeClaimKind
            &&& exists |vsts_name: StringView| #[trigger] pvc_name_match(pvc_key.name, vsts_name)
        } ==> {
            let pvc_obj = s.resources()[pvc_key];
            &&& pvc_obj.metadata.owner_references is None
        }
    }
}

pub proof fn lemma_always_all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(always(lift_state(vsts_rely_conditions_pod_monkey()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(all_pvcs_in_etcd_matching_vsts_have_no_owner_ref()))),
{
    let inv = all_pvcs_in_etcd_matching_vsts_have_no_owner_ref();
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& vsts_rely_conditions(cluster, controller_id)(s)
        &&& vsts_rely_conditions_pod_monkey()(s)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& guarantee::vsts_internal_guarantee_conditions(controller_id)(s)
        &&& every_msg_from_vsts_controller_carries_vsts_key(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_no_pending_request_to_api_server_from_api_server_or_external(spec);
    cluster.lemma_always_all_requests_from_pod_monkey_are_api_pod_requests(spec);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    guarantee::internal_guarantee_condition_holds_on_all_vsts(spec, cluster, controller_id);
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
                                assert(vsts_rely(other_id)(s));
                                match (msg.content->APIRequest_0) {
                                    APIRequest::CreateRequest(req) => {
                                        if req.key().kind == Kind::PersistentVolumeClaimKind {
                                            assert(rely_create_req(req));
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
                                                    no_vsts_prefix_implies_no_vsts_previx_in_generate_name_field(s.api_server, req.obj.metadata.generate_name->0);
                                                }
                                            }
                                            let created_obj_key = ObjectRef {
                                                kind: Kind::PersistentVolumeClaimKind,
                                                namespace: req.namespace,
                                                name: name,
                                            };
                                            assert(s_prime.resources().contains_key(created_obj_key));
                                            no_vsts_prefix_implies_no_pvc_name_match(name);
                                            assert forall |pvc_key: ObjectRef| {
                                                &&& #[trigger] s_prime.resources().contains_key(pvc_key)
                                                &&& pvc_key.kind == Kind::PersistentVolumeClaimKind
                                                &&& exists |vsts_name: StringView| #[trigger] pvc_name_match(pvc_key.name, vsts_name)
                                            } implies {
                                                let pvc_obj = s_prime.resources()[pvc_key];
                                                &&& pvc_obj.metadata.owner_references is None
                                            } by {
                                                if pvc_key != created_obj_key {
                                                    assert(s.resources().contains_key(pvc_key));
                                                } else {
                                                    assert(!exists |vsts_name: StringView| #[trigger] pvc_name_match(name, vsts_name));
                                                    assert(false);
                                                }
                                            }
                                        }
                                    },
                                    APIRequest::UpdateRequest(req) => {
                                        if req.key().kind == Kind::PersistentVolumeClaimKind {
                                            assert(rely_update_req(req));
                                        }
                                    },
                                    APIRequest::DeleteRequest(req) => {
                                        if req.key.kind == Kind::PersistentVolumeClaimKind {
                                            assert(rely_delete_req(req));
                                        }
                                    },
                                    _ => {}
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
                                assert(guarantee::no_interfering_request_between_vsts(controller_id, vsts_with_key)(s));
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
        lift_state(vsts_rely_conditions(cluster, controller_id)),
        lift_state(vsts_rely_conditions_pod_monkey()),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)),
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

// we don't need to talk about ongoing_reconcile as it's covered by at_vsts_step
pub open spec fn vsts_in_reconciles_has_no_deletion_timestamp(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| s.scheduled_reconciles(controller_id).contains_key(vsts.object_ref()) ==> {
        &&& s.scheduled_reconciles(controller_id)[vsts.object_ref()].metadata.deletion_timestamp is None
        &&& VStatefulSetView::unmarshal(s.scheduled_reconciles(controller_id)[vsts.object_ref()]).unwrap().metadata().deletion_timestamp is None
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

}
