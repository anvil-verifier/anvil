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
    proof::predicate::*,
    trusted::{rely_guarantee::*, spec_types::*, liveness_theorem::*, step::VStatefulSetReconcileStepView::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*, string_view::*};
use vstd::{seq_lib::*, map_lib::*, set_lib::*};
use vstd::prelude::*;

verus! {

// Before proving the shield lemma, we need to establish some rely-guarantee conditions
// about VSTS controller itself and other non-controller components in the cluster
// So in total we have
// 1. rely conditions for other controllers (rely_guarantee.rs)
// 2. VSTS internal rely-guarantee
// 3.a rely conditions for builtin controllers
// 3.b pod monkey, API server and external controllers


// 2. VSTS internal rely-guarantee
// all requests sent from one reconciliation do not interfere with other reconciliations on different CRs.
pub open spec fn no_interfering_request_between_vsts(controller_id: int, vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg) 
            &&& msg.content is APIRequest
            &&& msg.src == HostId::Controller(controller_id, vsts.object_ref())
        } ==> match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => {
                &&& req.namespace == vsts.object_ref().namespace
                &&& req.obj.kind == Kind::PodKind ==> {
                    &&& req.obj.metadata.owner_references == Some(Seq::empty().push(vsts.controller_owner_ref()))
                    &&& exists |ord: nat| req.key().name == #[trigger] pod_name(vsts.object_ref().name, ord)
                }
                &&& req.obj.kind == Kind::PersistentVolumeClaimKind ==> {
                    &&& exists |i: (StringView, nat)| req.key().name == #[trigger] pvc_name(i.0, vsts.object_ref().name, i.1)
                }
            },
            APIRequest::GetThenDeleteRequest(req) => {
                &&& req.key().namespace == vsts.object_ref().namespace
                &&& req.key().kind == Kind::PodKind
                &&& exists |ord: nat| req.key().name == #[trigger] pod_name(vsts.object_ref().name, ord)
                &&& req.owner_ref == vsts.controller_owner_ref()
            },
            APIRequest::GetThenUpdateRequest(req) => {
                &&& req.namespace == vsts.object_ref().namespace
                &&& req.obj.kind == Kind::PodKind
                &&& exists |ord: nat| req.name == #[trigger] pod_name(vsts.object_ref().name, ord)
                &&& req.owner_ref == vsts.controller_owner_ref()
                &&& req.obj.metadata.owner_references == Some(seq![vsts.controller_owner_ref()])
            },
            // VSTS controller will not issue DeleteRequest, UpdateRequest and UpdateStatusRequest
            _ => false
        }
    }
}

// 3.a rely conditions for builtin controllers (only GC is supported now)
pub open spec fn garbage_collector_does_not_delete_vsts_pod_objects(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src is BuiltinController
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
        } ==> {
            let req = msg.content.get_delete_request(); 
            &&& msg.content.is_delete_request()
            // &&& req.preconditions is Some
            // &&& req.preconditions.unwrap().uid is Some
            // &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
            &&& s.resources().contains_key(req.key) ==> {
                let obj = s.resources()[req.key];
                &&& !(obj.metadata.owner_references_contains(vsts.controller_owner_ref())
                    && obj.kind == Kind::PodKind
                    && obj.metadata.namespace == vsts.metadata.namespace)
                // ||| obj.metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap()
                &&& !(obj.kind == Kind::PersistentVolumeClaimKind
                    && obj.metadata.namespace == vsts.metadata.namespace
                    && obj.metadata.owner_references is None
                    && pvc_name_match(obj.metadata.name->0, vsts))
            }
        }
    }
}

// 3.b rely conditions for pod monkey, API server and external controllers
pub open spec fn non_controllers_do_not_mutate_pod_and_pvc_objects() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& !(msg.src is Controller || msg.src is BuiltinController)
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
        } ==> {
            let kind = get_kind_of_req(msg.content->APIRequest_0);
            &&& kind != Kind::PodKind
            &&& kind != Kind::PersistentVolumeClaimKind
        }
    }
}

// helper invariant for shield lemma
pub open spec fn every_msg_from_vsts_controller_carries_vsts_key(
    controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            let content = msg.content;
            &&& s.in_flight().contains(msg)
            &&& msg.src.is_controller_id(controller_id)
        } ==> {
            msg.src->Controller_1.kind == VStatefulSetView::kind()
        }
    }
}


uninterp spec fn make_vsts() -> VStatefulSetView;

// Shield lemma:
// All Pods and PVCs owned by VSTS controller are not mutated by others
// or by VSTS controller itself during reconciliation of other VSTS CRs
// or:
// forall Pod p owned by vsts: p =~= p'
// forall PVC v owned by vsts: v =~= v'
pub proof fn lemma_no_interference(
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
    Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)(s),
    Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())(s),
    Cluster::there_is_the_controller_state(controller_id)(s),
    Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vsts.object_ref())(s),
    Cluster::crash_disabled(controller_id)(s),
    Cluster::pod_monkey_disabled()(s),
    Cluster::req_drop_disabled()(s),
    every_msg_from_vsts_controller_carries_vsts_key(controller_id)(s),
    // 1. rely conditions for other controllers
    forall |other_id| vsts_rely(other_id, cluster.installed_types)(s),
    // 2. VSTS internal rely-guarantee across different CRs
    forall |other_vsts| no_interfering_request_between_vsts(controller_id, other_vsts)(s),
    // 3. rely conditions for builtin/external controllers
    garbage_collector_does_not_delete_vsts_pod_objects(vsts)(s),
    non_controllers_do_not_mutate_pod_and_pvc_objects()(s),
    // msg is sent by other controllers or VSTS controller for other CRs
    msg.src != HostId::Controller(controller_id, vsts.object_ref()),
    vsts.well_formed(),
ensures
    forall |k: ObjectRef| { // ==>
        let obj = s.resources()[k];
        &&& k.kind == Kind::PodKind
        &&& #[trigger] s.resources().contains_key(k)
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& obj.metadata.owner_references is Some
        &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()]
    } ==> {
        &&& s_prime.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    },
    forall |k: ObjectRef| { // <==
        let obj = s_prime.resources()[k];
        &&& k.kind == Kind::PodKind
        &&& #[trigger] s_prime.resources().contains_key(k)
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& obj.metadata.owner_references is Some
        &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()]
    } ==> {
        &&& s.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    },
    forall |k: ObjectRef| { // ==>
        let obj = s.resources()[k];
        &&& k.kind == Kind::PersistentVolumeClaimKind
        &&& #[trigger] s.resources().contains_key(k)
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& obj.metadata.owner_references is None // required by GC
        &&& pvc_name_match(obj.metadata.name->0, vsts)
    } ==> {
        &&& s_prime.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    },
    // forall |k: ObjectRef| { // <==
    //     let obj = s_prime.resources()[k];
    //     &&& k.kind == Kind::PersistentVolumeClaimKind
    //     &&& #[trigger] s_prime.resources().contains_key(k)
    //     &&& obj.metadata.namespace == vsts.metadata.namespace
    //     &&& obj.metadata.owner_references is None // required by GC
    //     &&& pvc_name_match(obj.metadata.name->0, vsts)
    // } ==> {
    //     &&& s.resources().contains_key(k)
    //     &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    // },
{
    assert(s.in_flight().contains(msg));
    assert forall |k: ObjectRef| { // ==>
        let obj = s.resources()[k];
        &&& k.kind == Kind::PodKind
        &&& #[trigger] s.resources().contains_key(k)
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& obj.metadata.owner_references is Some
        &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()]
    } implies {
        &&& s_prime.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    } by {
        let post = {
            &&& s_prime.resources().contains_key(k)
            &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
        };
        let obj = s.resources()[k];
        PodView::marshal_preserves_integrity();
        assert(obj.metadata.owner_references->0.contains(vsts.controller_owner_ref())) by {
            broadcast use group_seq_properties;
            seq_filter_contains_implies_seq_contains(obj.metadata.owner_references->0, controller_owner_filter(), vsts.controller_owner_ref());
        }
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
                            assert(no_interfering_request_between_vsts(controller_id, other_vsts)(s));
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
                                            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
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
        &&& obj.metadata.owner_references is Some
        &&& obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()]
    } implies {
        &&& s.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    } by {
        let post = {
            &&& s.resources().contains_key(k)
            &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
        };
        let obj = s_prime.resources()[k];
        PodView::marshal_preserves_integrity();
        assert(obj.metadata.owner_references->0.contains(vsts.controller_owner_ref())) by {
            broadcast use group_seq_properties;
            seq_filter_contains_implies_seq_contains(obj.metadata.owner_references->0, controller_owner_filter(), vsts.controller_owner_ref());
        }
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
                            assert(no_interfering_request_between_vsts(controller_id, other_vsts)(s));
                            if other_vsts.metadata.namespace == vsts.metadata.namespace {
                                assert(other_vsts.controller_owner_ref() != vsts.controller_owner_ref());
                                if msg.content.is_create_request() && !s.resources().contains_key(k) {
                                    let req = msg.content.get_create_request();
                                    seq_filter_contains_implies_seq_contains(req.obj.metadata.owner_references->0, controller_owner_filter(), vsts.controller_owner_ref());
                                    assert(req.obj.metadata.owner_references_contains(vsts.controller_owner_ref()));
                                    assert(false);
                                }
                                if msg.content.is_get_then_update_request() && s.resources().contains_key(k) {
                                    let req = msg.content.get_get_then_update_request();
                                    let old_obj = s.resources()[req.key()];
                                    if !(old_obj.metadata.owner_references is Some && old_obj.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()])
                                        && req.key() == k {
                                        assert(req.obj.metadata.owner_references == obj.metadata.owner_references);
                                        seq_filter_contains_implies_seq_contains(req.obj.metadata.owner_references->0, controller_owner_filter(), vsts.controller_owner_ref());
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
                                            assert(created_obj.metadata.owner_references_contains(vsts.controller_owner_ref())) by {
                                                seq_filter_is_a_subset_of_original_seq(created_obj.metadata.owner_references->0, controller_owner_filter());
                                            }
                                        }
                                        assert(post);
                                    }
                                },
                                APIRequest::GetThenUpdateRequest(req) => {
                                    if s.resources().contains_key(k) && req.key() == k {
                                        assert(cluster.controller_models.contains_key(id));
                                        assert(vsts_rely(id, cluster.installed_types)(s));
                                    }
                                    assert(post);
                                },
                                APIRequest::UpdateRequest(req) => {
                                    if s.resources().contains_key(k) {
                                        let resp = handle_update_request(cluster.installed_types, req, s.api_server).1;
                                        let old_obj = s.resources()[k];
                                        if req.key() == k && resp.res is Ok {
                                            if old_obj.metadata.owner_references is Some
                                                && old_obj.metadata.owner_references_contains(vsts.controller_owner_ref()) {
                                                assert(old_obj.metadata.owner_references->0.contains(vsts.controller_owner_ref()));
                                                assert(false);
                                            } else {
                                                if req.obj.metadata.owner_references is Some
                                                    && req.obj.metadata.owner_references->0.contains(vsts.controller_owner_ref()) {
                                                    assert(false);
                                                } else {
                                                    assert(obj.metadata.owner_references == req.obj.metadata.owner_references);
                                                    seq_filter_contains_implies_seq_contains(obj.metadata.owner_references->0, controller_owner_filter(), vsts.controller_owner_ref());
                                                    assert(false);
                                                }
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
    // PVC
    assert forall |k: ObjectRef| { // ==>
        let obj = s.resources()[k];
        &&& k.kind == Kind::PersistentVolumeClaimKind
        &&& #[trigger] s.resources().contains_key(k)
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& obj.metadata.owner_references is None
        &&& pvc_name_match(obj.metadata.name->0, vsts)
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
                            // so this proof is trivial, we only need to instantiate no_interfering_request_between_vsts
                            assert(cr_key != vsts.object_ref());
                            let other_vsts = VStatefulSetView {
                                metadata: ObjectMetaView {
                                    name: Some(cr_key.name),
                                    namespace: Some(cr_key.namespace),
                                    ..make_vsts().metadata
                                },
                                ..make_vsts()
                            };
                            assert(no_interfering_request_between_vsts(controller_id, other_vsts)(s));
                        } else {
                            assume(false);
                        }
                    },
                    _ => {},
                }
            }
        }
    }
}
    
}