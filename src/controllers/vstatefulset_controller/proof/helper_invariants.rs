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
use crate::vstd_ext::string_view::*;
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
            &&& pod_key.namespace == vsts.metadata.namespace->0
            &&& pod_name_match(pod_key.name, vsts.metadata.name->0)
        } ==> {
            let obj = s.resources()[pod_key];
            &&& obj.metadata.deletion_timestamp is None
            &&& obj.metadata.finalizers is None
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
        }
    }
}

pub open spec fn all_pods_in_etcd_matching_vsts_have_no_deletion_timestamp_and_owner_ref_matching_some_vsts(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |pod_key: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(pod_key)
            &&& pod_key.kind == Kind::PodKind
            &&& pod_key.namespace == vsts.metadata.namespace->0
            &&& pod_name_match(pod_key.name, vsts.metadata.name->0)
        } ==> {
            let obj = s.resources()[pod_key];
            &&& obj.metadata.deletion_timestamp is None
            &&& obj.metadata.finalizers is None
            &&& exists |old_vsts: VStatefulSetView| { // have same key, but potentailly different uid
                &&& obj.metadata.owner_references_contains(#[trigger] old_vsts.controller_owner_ref())
                &&& old_vsts.metadata.namespace == vsts.metadata.namespace
                &&& old_vsts.metadata.name == vsts.metadata.name
            }
        }
    }
}

#[verifier(rlimit(100))]
pub proof fn lemma_always_all_pods_in_etcd_matching_vsts_have_no_deletion_timestamp_and_owner_ref_matching_some_vsts(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(always(lift_state(vsts_rely_conditions_pod_monkey(cluster.installed_types)))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(all_pods_in_etcd_matching_vsts_have_no_deletion_timestamp_and_owner_ref_matching_some_vsts(vsts)))),
{
    let inv = all_pods_in_etcd_matching_vsts_have_no_deletion_timestamp_and_owner_ref_matching_some_vsts(vsts);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& vsts_rely_conditions(cluster, controller_id)(s)
        &&& vsts_rely_conditions_pod_monkey(cluster.installed_types)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
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
                    match msg.src {
                        HostId::Controller(other_id, cr_key) => {
                            if other_id != controller_id {
                                assume(false);
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
                                            assert forall |pod_key: ObjectRef| {
                                                &&& #[trigger] s_prime.resources().contains_key(pod_key)
                                                &&& pod_key.kind == Kind::PodKind
                                                &&& pod_key.namespace == vsts.metadata.namespace->0
                                                &&& pod_name_match(pod_key.name, vsts.metadata.name->0)
                                            } implies {
                                                let obj = s_prime.resources()[pod_key];
                                                let pod = PodView::unmarshal(obj)->Ok_0;
                                                &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
                                                &&& obj.metadata.deletion_timestamp is None
                                                &&& obj.metadata.finalizers is None
                                                &&& PodView::unmarshal(s.resources()[pod_key]) is Ok
                                                &&& vsts.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                            } by {
                                                if pod_key != created_obj_key {
                                                    assert(s.resources().contains_key(pod_key));
                                                } else {
                                                    assert(!pod_name_match(name, vsts.metadata.name->0));
                                                    assert(false);
                                                }
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
                                    _ => {}
                                }
                            } else if cr_key != vsts.object_ref() {
                                assume(false);
                                let havoc_vsts = make_vsts();
                                let vsts_with_key = VStatefulSetView {
                                    metadata: ObjectMetaView {
                                        name: Some(cr_key.name),
                                        namespace: Some(cr_key.namespace),
                                        ..havoc_vsts.metadata
                                    },
                                    ..havoc_vsts
                                };
                                assert(guarantee::no_interfering_request_between_vsts(controller_id, vsts_with_key)(s));
                                assert(s.in_flight().contains(msg)); // trigger
                                assert forall |pod_key: ObjectRef| {
                                    &&& #[trigger] s_prime.resources().contains_key(pod_key)
                                    &&& pod_key.kind == Kind::PodKind
                                    &&& pod_key.namespace == vsts.metadata.namespace->0
                                    &&& pod_name_match(pod_key.name, vsts.metadata.name->0)
                                } implies {
                                    let obj = s_prime.resources()[pod_key];
                                    &&& obj.metadata.deletion_timestamp is None
                                    &&& obj.metadata.finalizers is None
                                    &&& exists |old_vsts: VStatefulSetView| { // have same key, but potentailly different uid
                                        &&& obj.metadata.owner_references_contains(#[trigger] old_vsts.controller_owner_ref())
                                        &&& old_vsts.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
                                        &&& old_vsts.metadata.namespace == vsts.metadata.namespace
                                        &&& old_vsts.metadata.name == vsts.metadata.name
                                    }
                                } by {
                                    let resp = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
                                    if is_ok_resp(resp.content->APIResponse_0) {
                                        if s.resources().contains_key(pod_key) {
                                            if msg.content.is_get_then_update_request() {
                                                let req = msg.content.get_get_then_update_request();
                                                assert(req.owner_ref != vsts.controller_owner_ref()) by {
                                                    assume(false);
                                                }
                                            } else {
                                                // Deletion is allowed, Creation is not possible
                                            }
                                        } else {
                                            assume(false);
                                            if msg.content.is_create_request() {}
                                        }
                                    }
                                }
                            } else {
                                assert forall |pod_key: ObjectRef| {
                                    &&& #[trigger] s_prime.resources().contains_key(pod_key)
                                    &&& pod_key.kind == Kind::PodKind
                                    &&& pod_key.namespace == vsts.metadata.namespace->0
                                    &&& pod_name_match(pod_key.name, vsts.metadata.name->0)
                                } implies {
                                    let obj = s_prime.resources()[pod_key];
                                    &&& obj.metadata.deletion_timestamp is None
                                    &&& obj.metadata.finalizers is None
                                    &&& exists |old_vsts: VStatefulSetView| { // have same key, but potentailly different uid
                                        &&& obj.metadata.owner_references_contains(#[trigger] old_vsts.controller_owner_ref())
                                        &&& old_vsts.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
                                        &&& old_vsts.metadata.namespace == vsts.metadata.namespace
                                        &&& old_vsts.metadata.name == vsts.metadata.name
                                    }
                                } by {
                                    assert(guarantee::no_interfering_request_between_vsts(controller_id, vsts)(s));
                                    if s.resources().contains_key(pod_key) && msg.content.is_get_then_update_request() {
                                        let obj = s.resources()[pod_key];
                                        let req = msg.content.get_get_then_update_request();
                                        let new_vsts = VStatefulSetView {
                                            metadata: ObjectMetaView {
                                                name: Some(cr_key.name),
                                                namespace: Some(cr_key.namespace),
                                                uid: Some(req.owner_ref.uid),
                                                ..vsts.metadata
                                            },
                                            ..vsts
                                        };
                                        let obj_prime = s_prime.resources()[pod_key];
                                        assert(obj_prime.metadata.owner_references_contains(new_vsts.controller_owner_ref()));
                                    } else if !s.resources().contains_key(pod_key) && msg.content.is_create_request() {
                                        assume(false);
                                    } // GetThenDeleteRequest is trivial to proof
                                }
                            }
                        },
                        HostId::BuiltinController => {}, // must be delete requests
                        HostId::PodMonkey => {
                            assert(vsts_rely_conditions_pod_monkey(cluster.installed_types)(s));
                            assert forall |pod_key: ObjectRef| {
                                &&& #[trigger] s_prime.resources().contains_key(pod_key)
                                &&& pod_key.kind == Kind::PodKind
                                &&& pod_key.namespace == vsts.metadata.namespace->0
                                &&& pod_name_match(pod_key.name, vsts.metadata.name->0)
                            } implies {
                                let obj = s_prime.resources()[pod_key];
                                &&& obj.metadata.deletion_timestamp is None
                                &&& obj.metadata.finalizers is None
                                &&& exists |old_vsts: VStatefulSetView| { // have same key, but potentailly different uid
                                    &&& obj.metadata.owner_references_contains(#[trigger] old_vsts.controller_owner_ref())
                                    &&& old_vsts.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
                                    &&& old_vsts.metadata.namespace == vsts.metadata.namespace
                                    &&& old_vsts.metadata.name == vsts.metadata.name
                                }
                            } by {
                                let resp = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
                                if is_ok_resp(resp.content->APIResponse_0) {
                                    if s.resources().contains_key(pod_key) {
                                        let obj = s.resources()[pod_key];
                                        let old_vsts = choose |old_vsts: VStatefulSetView| {
                                            &&& obj.metadata.owner_references_contains(#[trigger] old_vsts.controller_owner_ref())
                                            &&& old_vsts.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
                                            &&& old_vsts.metadata.namespace == vsts.metadata.namespace
                                            &&& old_vsts.metadata.name == vsts.metadata.name
                                        };
                                        if msg.content.is_update_request() {
                                            let req = msg.content.get_update_request();
                                            assert(pod_key != req.key()) by {
                                                let old_obj = s.resources()[pod_key];
                                                assert(rely_update_pod_req(req)(s));
                                                assert(old_obj.metadata.owner_references_contains(#[trigger] old_vsts.controller_owner_ref()));
                                            }
                                        } else {
                                            // Deletion/UpdateStatus requests are allowed
                                            // Creation is not possible
                                        }
                                    } else {
                                        if msg.content.is_create_request() {
                                            let req = msg.content.get_create_request();
                                            assert(rely_create_pod_req(req));
                                            let name = if req.obj.metadata.name is Some {
                                                req.obj.metadata.name->0
                                            } else {
                                                generated_name(s.api_server, req.obj.metadata.generate_name->0)
                                            };
                                            assert(!pod_name_match(name, vsts.metadata.name->0)) by {
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
                                    }
                                }
                            }
                        }, // must be pod requests
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
        lift_state(vsts_rely_conditions(cluster, controller_id)),
        lift_state(vsts_rely_conditions_pod_monkey(cluster.installed_types)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(guarantee::vsts_internal_guarantee_conditions(controller_id)),
        lift_state(every_msg_from_vsts_controller_carries_vsts_key(controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// similar to above, but for PVCs
// rely conditions already prevent other controllers from creating or updating PVCs
// and VSTS controller's internal guarantee says all pvcs it creates have no owner refs
pub open spec fn all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |pvc_key: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(pvc_key)
            &&& pvc_key.kind == Kind::PersistentVolumeClaimKind
            &&& pvc_key.namespace == vsts.metadata.namespace->0
            &&& exists |vsts_name| pvc_name_match(pvc_key.name, vsts_name)
        } ==> {
            let pvc_obj = s.resources()[pvc_key];
            &&& pvc_obj.metadata.owner_references is None
        }
    }
}

pub proof fn lemma_always_all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(always(lift_state(vsts_rely_conditions_pod_monkey(cluster.installed_types)))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(vsts)))),
{
    let inv = all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(vsts);
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
                                                &&& pvc_key.namespace == vsts.metadata.namespace->0
                                                &&& pvc_name_match(pvc_key.name, vsts.metadata.name->0)
                                            } implies {
                                                let pvc_obj = s_prime.resources()[pvc_key];
                                                &&& pvc_obj.metadata.owner_references is None
                                            } by {
                                                if pvc_key != created_obj_key {
                                                    assert(s.resources().contains_key(pvc_key));
                                                } else {
                                                    assert(!pvc_name_match(name, vsts.metadata.name->0));
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
                                assert(guarantee::no_interfering_request_between_vsts(controller_id, vsts_with_key)(s));
                                assert(s.in_flight().contains(msg)); // trigger
                            } else {
                                assert(guarantee::no_interfering_request_between_vsts(controller_id, vsts)(s));
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

pub open spec fn garbage_collector_does_not_delete_vsts_pvc_objects(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src is BuiltinController
        } ==> {
            let req = msg.content.get_delete_request(); 
            &&& msg.dst is APIServer
            &&& msg.content.is_delete_request()
            &&& s.resources().contains_key(req.key) ==> {
                let obj = s.resources()[req.key];
                &&& !(obj.kind == Kind::PersistentVolumeClaimKind
                    && obj.metadata.namespace == vsts.metadata.namespace
                    && pvc_name_match(obj.metadata.name->0, vsts.metadata.name->0))
            }
        }
    }
}

pub open spec fn garbage_collector_does_not_delete_vsts_pod_objects(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src is BuiltinController
        } ==> {
            let req = msg.content.get_delete_request(); 
            &&& msg.dst is APIServer
            &&& msg.content.is_delete_request()
            &&& s.resources().contains_key(req.key) ==> {
                let obj = s.resources()[req.key];
                &&& !(obj.metadata.owner_references_contains(vsts.controller_owner_ref())
                    && obj.kind == Kind::PodKind
                    && obj.metadata.namespace == vsts.metadata.namespace)
                // ||| obj.metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap()
                &&& !(obj.kind == Kind::PersistentVolumeClaimKind
                    && obj.metadata.namespace == vsts.metadata.namespace
                    && obj.metadata.owner_references is None)
                    // && pvc_name_match(obj.metadata.name->0, vsts.metadata.name->0)
            }
        }
    }
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
