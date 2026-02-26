use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*,
    api_server::{state_machine::*, types::InstalledTypes},
};
use crate::kubernetes_cluster::proof::api_server::generated_name_reflects_prefix;
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
// 3.a rely conditions for builtin controllers (buildin_controllers_do_not_delete_{pods|pvcs}_owned_by_vsts)
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
    helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref()(s),
    helper_invariants::all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts)(s),
    helper_invariants::all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_no_deletion_timestamp(vsts)(s_prime),
    helper_invariants::buildin_controllers_do_not_delete_pods_owned_by_vsts(vsts.object_ref())(s),
    // 1. rely conditions for other controllers
    forall |other_id| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id)
        ==> vsts_rely(other_id)(s),
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
        &&& pod_name_match(k.name, vsts.metadata.name->0)
    } ==> {
        &&& s_prime.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    },
    forall |k: ObjectRef| { // <==
        &&& #[trigger] s_prime.resources().contains_key(k)
        &&& k.kind == Kind::PodKind
        &&& k.namespace == vsts.metadata.namespace->0
        &&& pod_name_match(k.name, vsts.metadata.name->0)
    } ==> {
        &&& s.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    },
{
    assert(s.in_flight().contains(msg));
    assert forall |k: ObjectRef| { // ==>
        let obj = s.resources()[k];
        &&& #[trigger] s.resources().contains_key(k)
        &&& k.kind == Kind::PodKind
        &&& k.namespace == vsts.metadata.namespace->0
        &&& pod_name_match(k.name, vsts.metadata.name->0)
    } implies {
        &&& s_prime.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    } by {
        let post = {
            &&& s_prime.resources().contains_key(k)
            &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
        };
        let obj = s.resources()[k];
        assert(obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
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
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(vsts_rely(id)(s)); // trigger vsts_rely_condition
                        }
                    },
                    _ => {},
                }
            }
        }
    }
    assert forall |k: ObjectRef| { // <==
        let obj = s_prime.resources()[k];
        &&& #[trigger] s_prime.resources().contains_key(k)
        &&& k.kind == Kind::PodKind
        &&& k.namespace == vsts.metadata.namespace->0
        &&& pod_name_match(k.name, vsts.metadata.name->0)
    } implies {
        &&& s.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    } by {
        let post = {
            &&& s.resources().contains_key(k)
            &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
        };
        let obj = s_prime.resources()[k];
        pod_name_match_implies_has_vsts_prefix(obj.metadata.name->0);
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
                                if !s.resources().contains_key(k) && resource_create_request_msg(k)(msg) {
                                    let req = msg.content.get_create_request();
                                    vsts_name_neq_implies_no_pod_name_match(req.obj.metadata.name->0, other_vsts.metadata.name->0, vsts.metadata.name->0);
                                    assert(false);
                                }
                                if s.resources().contains_key(k) && resource_get_then_update_request_msg(k)(msg) {
                                    let req = msg.content.get_get_then_update_request();
                                    vsts_name_neq_implies_no_pod_name_match(req.name, other_vsts.object_ref().name, vsts.metadata.name->0);
                                    assert(false);
                                }
                            } // or else, namespace is different, so should not be touched at all
                        } else {
                            assert(cluster.controller_models.remove(controller_id).contains_key(id));
                            assert(vsts_rely(id)(s)); // trigger vsts_rely_condition
                            if !s.resources().contains_key(k) {
                                if msg.content.is_create_request() {
                                    let req = msg.content.get_create_request();
                                    if resource_create_request_msg(k)(msg) {
                                        assert(has_vsts_prefix(req.obj.metadata.name->0));
                                        assert(false);
                                    } else if req.obj.metadata.name is None && req.obj.metadata.generate_name is Some {
                                        generated_name_reflects_prefix(s.api_server, req.obj.metadata.generate_name->0, VStatefulSetView::kind()->CustomResourceKind_0);
                                        assert(false);
                                    }
                                } else {
                                    assert(s.resources().contains_key(k));
                                }
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
    helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref()(s),
    helper_invariants::all_pvcs_in_etcd_matching_vsts_have_no_finalizer_or_deletion_timestamp_or_owner_ref()(s_prime),
    helper_invariants::buildin_controllers_do_not_delete_pvcs_owned_by_vsts()(s),
    // 1. rely conditions for other controllers
    forall |other_id| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id)
        ==> vsts_rely(other_id)(s),
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
        pvc_name_match_implies_has_vsts_prefix(k.name);
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
                            assert(vsts_rely(id)(s)); // trigger vsts_rely_condition
                            if resource_delete_request_msg(k)(msg) || resource_update_request_msg(k)(msg) {
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
        pvc_name_match_implies_has_vsts_prefix(k.name);
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
                                    vsts_name_neq_implies_no_pvc_name_match(
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
                            assert(vsts_rely(id)(s)); // trigger vsts_rely_condition
                            if resource_update_request_msg(k)(msg) {
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
                                        generated_name_reflects_prefix(s.api_server, req.obj.metadata.generate_name->0, VStatefulSetView::kind()->CustomResourceKind_0);
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