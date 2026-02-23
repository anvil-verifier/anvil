use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::InstalledTypes}, 
    cluster::*, 
    message::*
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

// TODO: resort to lemma_eventually_always_resource_object_only_has_owner_reference_pointing_to_current_cr
// I want to use Basilisk but they don't support Verus/liveness verification yet

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

pub proof fn lemma_always_buildin_controllers_do_not_delete_pvcs_owned_by_vsts(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(always(lift_state(vsts_rely_conditions_pod_monkey(cluster.installed_types)))),
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
    spec.entails(always(lift_state(vsts_rely_conditions_pod_monkey(cluster.installed_types)))),
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
        &&& vsts_rely_conditions_pod_monkey(cluster.installed_types)(s)
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

    assert forall|s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime)
        implies inv(s_prime) by {
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
                                assert(vsts_rely(other_id, cluster.installed_types)(s));
                                match (msg.content->APIRequest_0) {
                                    APIRequest::CreateRequest(req) => {
                                        if req.key().kind == Kind::PersistentVolumeClaimKind {
                                            assert(rely_create_pvc_req(req));
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
                                            assert(rely_update_pvc_req(req));
                                        }
                                    },
                                    APIRequest::DeleteRequest(req) => {
                                        if req.key.kind == Kind::PersistentVolumeClaimKind {
                                            assert(rely_delete_pvc_req(req));
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
        lift_state(vsts_rely_conditions_pod_monkey(cluster.installed_types)),
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

}
