use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
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
pub open spec fn no_interfering_request_between_vsts(controller_id: int, vsts_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let vsts = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[vsts_key].triggering_cr).unwrap();
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg) 
            &&& msg.content is APIRequest
            &&& msg.src == HostId::Controller(controller_id, vsts_key)
            &&& s.ongoing_reconciles(controller_id).contains_key(vsts_key)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => {
                &&& req.namespace == vsts_key.namespace
                &&& req.obj.kind == Kind::PodKind ==> {
                    &&& req.obj.metadata.owner_references == Some(Seq::empty().push(vsts.controller_owner_ref()))
                    &&& exists |ord: nat| req.obj.metadata.name == Some(#[trigger] pod_name(vsts_key.name, ord))
                }
                &&& req.obj.kind == Kind::PersistentVolumeClaimKind ==> {
                    &&& exists |i: (int, nat)| // PVC template index, ordinal
                        req.obj.metadata.name == Some(#[trigger] pvc_name(vsts.spec.volume_claim_templates->0[i.0].metadata.name->0, vsts_key.name, i.1))
                }
            },
            APIRequest::GetThenDeleteRequest(req) => {
                &&& req.key().namespace == vsts_key.namespace
                &&& req.key().kind == Kind::PodKind
                &&& exists |ord: nat| req.key().name == #[trigger] pod_name(vsts_key.name, ord)
                &&& req.owner_ref == vsts.controller_owner_ref()
            },
            APIRequest::GetThenUpdateRequest(req) => {
                &&& req.namespace == vsts_key.namespace
                &&& req.obj.kind == Kind::PodKind
                &&& exists |ord: nat| req.name == #[trigger] pod_name(vsts_key.name, ord)
                &&& req.owner_ref == vsts.controller_owner_ref()
            },
            // VSTS controller will not issue DeleteRequest, UpdateRequest
            _ => true
        }
    }
}

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
    forall |other_key| no_interfering_request_between_vsts(controller_id, other_key)(s),
    forall |other_id| vsts_rely(other_id)(s),
    msg.src != HostId::Controller(controller_id, vsts.object_ref()),
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
        // TODO: weaken to allow status update requests
        &&& s.resources()[k] == s_prime.resources()[k]
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
        // TODO: weaken to allow status update requests
        &&& s.resources()[k] == s_prime.resources()[k]
    },
    forall |k: ObjectRef| { // ==>
        let obj = s.resources()[k];
        &&& k.kind == Kind::PersistentVolumeClaimKind
        &&& #[trigger] s.resources().contains_key(k)
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& pvc_name_match(obj.metadata.name->0, vsts)
    } ==> {
        &&& s_prime.resources().contains_key(k)
        &&& s.resources()[k] == s_prime.resources()[k]
    },
    forall |k: ObjectRef| { // <==
        let obj = s_prime.resources()[k];
        &&& k.kind == Kind::PersistentVolumeClaimKind
        &&& #[trigger] s_prime.resources().contains_key(k)
        &&& obj.metadata.namespace == vsts.metadata.namespace
        &&& pvc_name_match(obj.metadata.name->0, vsts)
    } ==> {
        &&& s.resources().contains_key(k)
        &&& s.resources()[k] == s_prime.resources()[k]
    },
{
    admit();
}
    
}