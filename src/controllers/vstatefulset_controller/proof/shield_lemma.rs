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

// In addition to rely conditions, we also need to prove vsts controller's internal guarantee:
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
                    &&& exists |ord: nat| req.obj.metadata.name == Some(#[trigger] pod_name(vsts.object_ref().name, ord))
                }
                &&& req.obj.kind == Kind::PersistentVolumeClaimKind ==> {
                    &&& exists |i: (int, nat)| // PVC template index, ordinal
                        req.obj.metadata.name == Some(#[trigger] pvc_name(vsts.spec.volume_claim_templates->0[i.0].metadata.name->0, vsts.object_ref().name, i.1))
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
            },
            // VSTS controller will not issue DeleteRequest, UpdateRequest
            _ => false
        }
    }
}

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

// shield lemma
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
    forall |other_vsts| no_interfering_request_between_vsts(controller_id, other_vsts)(s),
    forall |other_id| vsts_rely(other_id, cluster.installed_types)(s),
    every_msg_from_vsts_controller_carries_vsts_key(controller_id)(s),
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
        &&& pvc_name_match(obj.metadata.name->0, vsts)
    } ==> {
        &&& s_prime.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    },
    forall |k: ObjectRef| { // <==
        let obj = s_prime.resources()[k];
        &&& k.kind == Kind::PersistentVolumeClaimKind
        &&& #[trigger] s_prime.resources().contains_key(k)
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& pvc_name_match(obj.metadata.name->0, vsts)
    } ==> {
        &&& s.resources().contains_key(k)
        &&& weakly_eq(s.resources()[k], s_prime.resources()[k])
    },
{
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
            if !{ // if request fails, trivial
                let resp_msg = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
                &&& resp_msg.content is APIResponse
                &&& is_ok_resp(resp_msg.content->APIResponse_0)
            } {
                assert(s_prime.resources() == s.resources());
                assert(post);
            }
            else { // if request succeeds
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
                            // so msg can only be list, create or get_then_update
                            assert(no_interfering_request_between_vsts(controller_id, other_vsts)(s));
                            // every_msg_from_vsts_controller_carries_vsts_key
                            if cr_key.namespace == vsts.metadata.namespace->0 && cr_key.name == vsts.metadata.name->0 {
                                assert(cr_key == vsts.object_ref());
                            }
                            match msg.content->APIRequest_0 {
                                APIRequest::DeleteRequest(req) => assert(false), // vsts controller doesn't send delete req
                                APIRequest::GetThenDeleteRequest(req) => admit(),
                                APIRequest::GetThenUpdateRequest(req) => {
                                    // controller_owner_ref does not carry namespace, while object_ref does
                                    // so object_ref != is not enough to prove controller_owner_ref !=
                                    if cr_key.namespace == vsts.metadata.namespace->0 {
                                        assert(!obj.metadata.owner_references_contains(req.owner_ref)) by {
                                            if obj.metadata.owner_references_contains(req.owner_ref) {
                                                assert(req.owner_ref != vsts.controller_owner_ref());
                                                assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                            }
                                        }
                                    } // or else, namespace is different, so should not be touched at all
                                },
                                _ => {},
                            }
                            assert(post);
                        } else {
                            let other_id = msg.src->Controller_0;
                            // by every_in_flight_req_msg_from_controller_has_valid_controller_id, used by vd_rely
                            assert(cluster.controller_models.contains_key(other_id));
                            assert(vsts_rely(other_id, cluster.installed_types)(s)); // trigger vd_rely_condition
                            VStatefulSetReconcileState::marshal_preserves_integrity();
                            match msg.content->APIRequest_0 {
                                APIRequest::DeleteRequest(..) | APIRequest::UpdateRequest(..) | APIRequest::CreateRequest(..) => {
                                    assert(post);
                                },
                                APIRequest::GetThenDeleteRequest(req) => {
                                    if req.key.kind == Kind::PodKind {
                                        if obj.metadata.owner_references_contains(req.owner_ref) {
                                            // then the singleton does not match
                                            assert(req.owner_ref != vsts.controller_owner_ref());
                                            assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                        }
                                    }
                                    assert(post);
                                },
                                APIRequest::GetThenUpdateRequest(req) => {
                                    if req.obj.kind == Kind::PodKind {
                                        // rely condition
                                        assert(req.owner_ref.kind != VStatefulSetView::kind());
                                        assert(!obj.metadata.owner_references_contains(req.owner_ref)) by {
                                            if obj.metadata.owner_references_contains(req.owner_ref) {
                                                assert(req.owner_ref != vsts.controller_owner_ref());
                                                assert(obj.metadata.owner_references->0.filter(controller_owner_filter()).contains(req.owner_ref));
                                            }
                                        }
                                    }
                                    assert(post);
                                },
                                APIRequest::UpdateStatusRequest(req) => {
                                    if req.obj.kind == Kind::PodKind {
                                        let new_obj = s_prime.resources()[req.key()];
                                        assert(weakly_eq(new_obj, obj));
                                    }
                                    assert(post);
                                },
                                _ => { // Read-only requests
                                    assert(post);
                                },
                            }
                            assert(post);
                        }
                    },
                    _ => {},
                }
            }
        }
    }
    admit();
}
    
}