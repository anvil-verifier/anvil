use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*,
    api_server::{state_machine::*, types::InstalledTypes},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    proof::{predicate::*, guarantee, helper_invariants, helper_lemmas::*},
    trusted::{rely::*, spec_types::*, liveness_theorem::*, step::VStatefulSetReconcileStepView::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*, string_view::*};
use vstd::{seq_lib::*, map_lib::*, set_lib::*};
use vstd::prelude::*;

verus! {

// Before proving the shield lemma, we need to establish some rely-guarantee conditions
// about VSTS controller itself and other non-controller components in the cluster
// So in total we have
// 1. rely conditions for other controllers (rely::vsts_rely)
// 2. VSTS internal rely-guarantee (guarantee::guarantee::no_interfering_request_between_vsts)
// 3.a rely conditions for builtin controllers (rely::garbage_collector_does_not_delete_vsts_pod_objects)
// 3.b pod monkey, API server and external controllers (Cluster::no_pending_request_to_api_server_from_non_controllers)

// Shield lemma:
// All Pods and PVCs owned by VSTS controller are not mutated by others
// or by VSTS controller itself during reconciliation of other VSTS CRs
// in other words, let =~= denotes weakly_eq,
// forall Pod p owned by vsts: p =~= p'
// forall PVC v owned by vsts: v =~= v'
pub proof fn lemma_no_interference_on_pods(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    cluster.each_builtin_object_in_etcd_is_well_formed()(s),
    cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s),
    Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)(s),
    cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
    Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
    Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())(s),
    Cluster::there_is_the_controller_state(controller_id)(s),
    Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref())(s),
    Cluster::pod_monkey_disabled()(s),
    Cluster::req_drop_disabled()(s),
    guarantee::every_msg_from_vsts_controller_carries_vsts_key(controller_id)(s),
    helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(vsts)(s),
    helper_invariants::all_pods_in_etcd_matching_vsts_have_correct_owner_ref_labels_and_no_deletion_timestamp(vsts)(s),
    helper_invariants::garbage_collector_does_not_delete_vsts_pod_objects(vsts)(s),
    // 1. rely conditions for other controllers
    forall |other_id| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id)
        ==> vsts_rely(other_id, cluster.installed_types)(s),
    // 2. VSTS internal rely-guarantee across different CRs
    forall |vsts| #[trigger] guarantee::no_interfering_request_between_vsts(controller_id, vsts)(s),
    Cluster::no_pending_request_to_api_server_from_non_controllers()(s),
    // msg is sent by other controllers or VSTS controller for other CRs
    msg.src != HostId::Controller(controller_id, vsts.object_ref()),
    vsts.metadata.name is Some,
    vsts.metadata.namespace is Some, // well_formed is too strong as it has no rv
ensures
    forall |k: ObjectRef| { // ==>
        &&& #[trigger] s.resources().contains_key(k)
        &&& k.kind == Kind::PodKind
        &&& k.namespace == vsts.metadata.namespace->0
        &&& (pod_name_match(k.name, vsts.metadata.name->0) ||
            s.resources()[k].metadata.owner_references_contains(vsts.controller_owner_ref()))
    } ==> {
        &&& s_prime.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    },
    forall |k: ObjectRef| { // <==
        &&& #[trigger] s_prime.resources().contains_key(k)
        &&& k.kind == Kind::PodKind
        &&& k.namespace == vsts.metadata.namespace->0
        &&& (pod_name_match(k.name, vsts.metadata.name->0) ||
            s_prime.resources()[k].metadata.owner_references_contains(vsts.controller_owner_ref()))
    } ==> {
        &&& s.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    },
{
    assert(s.in_flight().contains(msg));
    assert forall |k: ObjectRef| { // ==>
        let obj = s.resources()[k];
        &&& k.kind == Kind::PodKind
        &&& #[trigger] s.resources().contains_key(k)
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& (pod_name_match(k.name, vsts.metadata.name->0) ||
            s.resources()[k].metadata.owner_references_contains(vsts.controller_owner_ref()))
    } implies {
        &&& s_prime.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    } by {
        let post = {
            &&& s_prime.resources().contains_key(k)
            &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
        };
        let obj = s.resources()[k];
        if pod_name_match(k.name, vsts.metadata.name->0) {
            assert(obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
        }
        PodView::marshal_preserves_integrity();
        assert(obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()]) by {
            // broadcast use group_seq_properties; // this increase proof time from 3 to 20s
            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(vsts.controller_owner_ref()));
            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).len() <= 1);
        };
        if msg.content is APIRequest && msg.dst is APIServer {
            if !{ // if request fails, noop
                let resp_msg = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
                &&& resp_msg.content is APIResponse
                &&& is_ok_resp(resp_msg.content->APIResponse_0)
            } {
                assert(s_prime.resources() == s.resources());
                assert(post);
            } else { // if request succeeds
                match msg.src {
                    HostId::Controller(id, cr_key) => {
                        if id == controller_id {
                            assert(cr_key != vsts.object_ref());
                            // same controller, other vsts
                            let cr_key = msg.src->Controller_1;
                            let other_vsts = VStatefulSetView {
                                metadata: ObjectMetaView {
                                    name: Some(cr_key.name),
                                    namespace: Some(cr_key.namespace),
                                    ..make_vsts().metadata
                                },
                                ..make_vsts()
                            };
                            // so msg can only be list, create, get_then_delete and get_then_update
                            assert(guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s));
                            if msg.content.is_get_then_delete_request() || msg.content.is_get_then_update_request() {
                                let req_owner_ref = match msg.content->APIRequest_0 {
                                    APIRequest::GetThenDeleteRequest(r) => r.owner_ref,
                                    APIRequest::GetThenUpdateRequest(r) => r.owner_ref,
                                    _ => OwnerReferenceView::default(),
                                };
                                if cr_key.namespace == vsts.metadata.namespace->0 {
                                    assert(!obj.metadata.owner_references_contains(req_owner_ref)) by {
                                        if obj.metadata.owner_references_contains(req_owner_ref) {
                                            assert(req_owner_ref != vsts.controller_owner_ref());
                                            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req_owner_ref));
                                        }
                                    }
                                } // or else, namespace is different, so should not be touched at all
                            }
                            assert(post);
                        } else { // from other controllers
                            // by every_in_flight_req_msg_from_controller_has_valid_controller_id, used by vsts_rely
                            assert(cluster.controller_models.contains_key(id));
                            assert(vsts_rely(id, cluster.installed_types)(s)); // trigger vsts_rely_condition
                            match msg.content->APIRequest_0 {
                                APIRequest::DeleteRequest(..) | APIRequest::UpdateRequest(..) | APIRequest::CreateRequest(..) => {},
                                APIRequest::GetThenDeleteRequest(req) => {
                                    if req.key.kind == Kind::PodKind {
                                        if obj.metadata.owner_references_contains(req.owner_ref) {
                                            // then the singleton does not match
                                            assert(req.owner_ref != vsts.controller_owner_ref());
                                            assert(!obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                        }
                                    }
                                },
                                APIRequest::GetThenUpdateRequest(req) => {
                                    if req.obj.kind == Kind::PodKind {
                                        // rely condition
                                        assert(req.owner_ref.kind != VStatefulSetView::kind());
                                        if obj.metadata.owner_references_contains(req.owner_ref) {
                                            assert(req.owner_ref != vsts.controller_owner_ref());
                                            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                        }
                                    }
                                },
                                APIRequest::UpdateStatusRequest(req) => {}, // only status and RV updated
                                _ => {}, // Read-only requests
                            }
                        }
                    },
                    _ => {},
                }
            }
        }
    }
    assert forall |k: ObjectRef| { // <==
        let obj = s_prime.resources()[k];
        &&& k.kind == Kind::PodKind
        &&& #[trigger] s_prime.resources().contains_key(k)
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& (pod_name_match(k.name, vsts.metadata.name->0) ||
            s_prime.resources()[k].metadata.owner_references_contains(vsts.controller_owner_ref()))
    } implies {
        &&& s.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    } by {
        let post = {
            &&& s.resources().contains_key(k)
            &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
        };
        let obj = s_prime.resources()[k];
        if pod_name_match(k.name, vsts.metadata.name->0) {
            assert(obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
        }
        PodView::marshal_preserves_integrity();
        if msg.content is APIRequest && msg.dst is APIServer {
            if !{ // if request fails, noop
                let resp_msg = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
                &&& resp_msg.content is APIResponse
                &&& is_ok_resp(resp_msg.content->APIResponse_0)
            } {
                assert(s_prime.resources() == s.resources());
                assert(post);
            } else {
                match msg.src {
                    HostId::Controller(id, cr_key) => {
                        if id == controller_id {
                            assert(cr_key != vsts.object_ref());
                            let other_vsts = VStatefulSetView {
                                metadata: ObjectMetaView {
                                    name: Some(cr_key.name),
                                    namespace: Some(cr_key.namespace),
                                    ..make_vsts().metadata
                                },
                                ..make_vsts()
                            };
                            assert(guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s));
                            if other_vsts.metadata.namespace == vsts.metadata.namespace {
                                assert(other_vsts.controller_owner_ref() != vsts.controller_owner_ref());
                                if msg.content.is_create_request() && !s.resources().contains_key(k) {
                                    let req = msg.content.get_create_request();
                                    assert(req.obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
                                    assert(false);
                                }
                                if msg.content.is_get_then_update_request() && s.resources().contains_key(k) {
                                    let req = msg.content.get_get_then_update_request();
                                    let old_obj = s.resources()[req.key()];
                                    if !old_obj.metadata.owner_references_contains(other_vsts.controller_owner_ref()) && req.key() == k {
                                        assert(req.obj.metadata.owner_references == obj.metadata.owner_references);
                                        assert(false);
                                    }
                                }
                            } // or else, namespace is different, so should not be touched at all
                        } else {
                            assert(cluster.controller_models.contains_key(id));
                            assert(vsts_rely(id, cluster.installed_types)(s)); // trigger vsts_rely_condition
                            match msg.content->APIRequest_0 {
                                APIRequest::CreateRequest(req) => {
                                    if req.obj.kind == Kind::PodKind && !s.resources().contains_key(k) {
                                        assert(vsts_rely(msg.src->Controller_0, cluster.installed_types)(s));
                                        // req succeed
                                        let resp = handle_create_request(cluster.installed_types, req, s.api_server).1;
                                        if resp.res is Ok {
                                            let created_obj = resp.res->Ok_0;
                                            assert(s_prime.resources() == s.resources().insert(created_obj.object_ref(), created_obj));
                                            assert((k, obj) == (created_obj.object_ref(), created_obj));
                                            // trigger rely conditions
                                            assert(req.obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
                                            assert(false);
                                        }
                                        assert(post);
                                    }
                                },
                                APIRequest::GetThenUpdateRequest(req) => {
                                    if s.resources().contains_key(k) && req.key() == k {
                                        assert(cluster.controller_models.contains_key(id));
                                        assert(vsts_rely(id, cluster.installed_types)(s));
                                        let old_obj = s.resources()[k];
                                        if req.key() == k && !old_obj.metadata.owner_references_contains(vsts.controller_owner_ref()) {
                                            assert(req.obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
                                            assert(false);
                                        }
                                    }
                                    assert(post);
                                },
                                APIRequest::UpdateRequest(req) => {
                                    if s.resources().contains_key(k) {
                                        let resp = handle_update_request(cluster.installed_types, req, s.api_server).1;
                                        let old_obj = s.resources()[k];
                                        if req.key() == k && resp.res is Ok {
                                            if old_obj.metadata.owner_references_contains(vsts.controller_owner_ref()) {
                                                assert(false);
                                            } else if req.obj.metadata.owner_references_contains(vsts.controller_owner_ref()) {
                                                assert(false);
                                            }   
                                        } else {
                                            assert(s.resources()[k] == s_prime.resources()[k]);
                                        }
                                    }
                                },
                                _ => {}
                            }
                        }
                    },
                    _ => {},
                }
            }
        }
    }
}

pub proof fn lemma_no_interference_on_pvcs(
    s: ClusterState, s_prime: ClusterState, vsts: VStatefulSetView, cluster: Cluster, controller_id: int, msg: Message
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    cluster.each_builtin_object_in_etcd_is_well_formed()(s),
    cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s),
    Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)(s),
    cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
    Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
    Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())(s),
    Cluster::there_is_the_controller_state(controller_id)(s),
    Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref())(s),
    Cluster::pod_monkey_disabled()(s),
    Cluster::req_drop_disabled()(s),
    guarantee::every_msg_from_vsts_controller_carries_vsts_key(controller_id)(s),
    helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(vsts)(s),
    helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(vsts)(s_prime),
    // 1. rely conditions for other controllers
    forall |other_id| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id)
        ==> vsts_rely(other_id, cluster.installed_types)(s),
    // 2. VSTS internal rely-guarantee across different CRs
    forall |other_vsts| guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s),
    // 3. rely conditions for builtin/external controllers
    Cluster::no_pending_request_to_api_server_from_non_controllers()(s),
    // msg is sent by other controllers or VSTS controller for other CRs
    msg.src != HostId::Controller(controller_id, vsts.object_ref()),
    vsts.metadata.name is Some,
    vsts.metadata.namespace is Some, // well_formed is too strong as it has no rv
ensures
    forall |k: ObjectRef| { // ==>
        &&& #[trigger] s.resources().contains_key(k)
        &&& k.kind == Kind::PersistentVolumeClaimKind
        &&& k.namespace == vsts.metadata.namespace->0
        &&& pvc_name_match(k.name, vsts.metadata.name->0)
        // assumed by all_pvcs_in_etcd_matching_vsts_have_no_owner_ref
        // &&& obj.metadata.owner_references is None // required by GC
    } ==> {
        &&& s_prime.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    },
    forall |k: ObjectRef| { // <==
        &&& #[trigger] s_prime.resources().contains_key(k)
        &&& k.kind == Kind::PersistentVolumeClaimKind
        &&& k.namespace == vsts.metadata.namespace->0
        &&& pvc_name_match(k.name, vsts.metadata.name->0)
    } ==> {
        &&& s.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    },
{
    assert(s.in_flight().contains(msg));
    // PVC
    assert forall |k: ObjectRef| { // ==>
        &&& #[trigger] s.resources().contains_key(k)
        &&& k.kind == Kind::PersistentVolumeClaimKind
        &&& k.namespace == vsts.metadata.namespace->0
        &&& pvc_name_match(k.name, vsts.metadata.name->0)
    } implies {
        &&& s_prime.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    } by {
        // similar proof as Pod
        let post = {
            &&& s_prime.resources().contains_key(k)
            &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
        };
        let obj = s.resources()[k];
        PersistentVolumeClaimView::marshal_preserves_integrity();
        if msg.content is APIRequest && msg.dst is APIServer {
            if !{ // if request fails, noop
                let resp_msg = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
                &&& resp_msg.content is APIResponse
                &&& is_ok_resp(resp_msg.content->APIResponse_0)
            } {
                assert(s_prime.resources() == s.resources());
                assert(post);
            } else { // if request succeeds
                match msg.src {
                    HostId::Controller(id, cr_key) => {
                        if id == controller_id {
                            // currently VSTS controller only sends create request to PVC
                            // so this proof is trivial, we only need to instantiate guarantee::no_interfering_request_between_vsts
                            assert(cr_key != vsts.object_ref());
                            let other_vsts = VStatefulSetView {
                                metadata: ObjectMetaView {
                                    name: Some(cr_key.name),
                                    namespace: Some(cr_key.namespace),
                                    ..make_vsts().metadata
                                },
                                ..make_vsts()
                            };
                            assert(guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s));
                        } else { // from other controllers
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(vsts_rely(id, cluster.installed_types)(s)); // trigger vsts_rely_condition
                            if resource_delete_request_msg(k)(msg) || resource_update_request_msg(k)(msg) {
                                assert(pvc_name_match(k.name, vsts.metadata.name->0));
                                assert(false);
                            }
                        }
                    },
                    _ => {},
                }
            }
        }
    }
    assert forall |k: ObjectRef| { // <==
        &&& #[trigger] s_prime.resources().contains_key(k)
        &&& k.kind == Kind::PersistentVolumeClaimKind
        &&& k.namespace == vsts.metadata.namespace->0
        &&& pvc_name_match(k.name, vsts.metadata.name->0)
    } implies {
        &&& s.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    } by {
        // similar proof as Pod
        let post = {
            &&& s.resources().contains_key(k)
            &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
        };
        let obj = s_prime.resources()[k];
        PersistentVolumeClaimView::marshal_preserves_integrity();
        if msg.content is APIRequest && msg.dst is APIServer {
            if !{ // if request fails, noop
                let resp_msg = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
                &&& resp_msg.content is APIResponse
                &&& is_ok_resp(resp_msg.content->APIResponse_0)
            } {
                assert(s_prime.resources() == s.resources());
                assert(post);
            } else {
                match msg.src {
                    HostId::Controller(id, cr_key) => {
                        if id == controller_id {
                            let other_vsts = VStatefulSetView {
                                metadata: ObjectMetaView {
                                    name: Some(cr_key.name),
                                    namespace: Some(cr_key.namespace),
                                    ..make_vsts().metadata
                                },
                                ..make_vsts()
                            };
                            assert(guarantee::no_interfering_request_between_vsts(controller_id, other_vsts)(s));
                            if other_vsts.metadata.namespace == vsts.metadata.namespace {
                                assert(other_vsts.metadata.name != vsts.metadata.name);
                                if resource_create_request_msg(k)(msg) && !s.resources().contains_key(k) {
                                    vsts_name_non_eq_implies_no_pvc_name_match(
                                        obj.metadata.name->0, other_vsts.metadata.name->0, vsts.metadata.name->0
                                    );
                                } else if resource_get_then_update_request_msg(k)(msg) && s.resources().contains_key(k) {
                                    let req = msg.content.get_get_then_update_request();
                                    // VSTS controller does not send update request to PVC
                                    assert(req.obj.kind == Kind::PodKind);
                                }
                            } // or else, namespace is different, so should not be touched at all
                            assert(post);
                        } else {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(vsts_rely(id, cluster.installed_types)(s)); // trigger vsts_rely_condition
                            if resource_update_request_msg(k)(msg) {
                                assert(pvc_name_match(k.name, vsts.metadata.name->0));
                                assert(false);
                            } else if msg.content.is_create_request() && !s.resources().contains_key(k) {
                                let req = msg.content.get_create_request();
                                if req.obj.metadata.name is Some && req.key() == k {
                                    assert(!pvc_name_match(obj.metadata.name->0, vsts.metadata.name->0)) by {
                                        no_vsts_prefix_implies_no_pvc_name_match(obj.metadata.name->0);
                                    }
                                } else if req.obj.metadata.name is None && req.obj.metadata.generate_name is Some {
                                    let name = generated_name(s.api_server, req.obj.metadata.generate_name->0);
                                    if has_vsts_prefix(name) {
                                        generated_name_spec(s.api_server, req.obj.metadata.generate_name->0);
                                        let generated_suffix = choose |suffix: StringView| #[trigger] dash_free(suffix) &&
                                            name == req.obj.metadata.generate_name->0 + suffix;
                                        generated_name_has_vsts_prefix_implies_generate_name_field_has_vsts_prefix(
                                            name, req.obj.metadata.generate_name->0, generated_suffix
                                        );
                                        assert(false);
                                    }
                                    assert(!pvc_name_match(name, vsts.metadata.name->0)) by {
                                        no_vsts_prefix_implies_no_pvc_name_match(name);
                                    }
                                }
                            } else if resource_get_then_update_request_msg(k)(msg) {}
                            assert(post);
                        }
                    },
                    _ => {},
                }
            }
        }
    }
}

}