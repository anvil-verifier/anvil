use crate::kubernetes_api_objects::spec::{prelude::*, persistent_volume_claim::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::kubernetes_cluster::spec::api_server::{state_machine::*, types::InstalledTypes};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::{
    trusted::spec_types::*,
    model::{reconciler::*, install::*},
    proof::predicate::*,
    proof::helper_lemmas::*
};
use crate::vstatefulset_controller::trusted::step::VStatefulSetReconcileStepView;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use crate::vstd_ext::seq_lib::*;

verus! {

// VSTS Guarantee Condition (for other controllers)

pub open spec fn vsts_guarantee(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
            APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
            APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
            // No Update, UpdateStatus and Delete requests submitted
            _ => true,
        }
    }
}

// VSTS controller only creates Pods owned by itself
// and only creates PVC matching its PVC templates
pub open spec fn vsts_guarantee_create_req(req: CreateRequest) -> bool {
    let owner_references = req.obj.metadata.owner_references->0;
    &&& req.obj.kind == PodView::kind() ==> {
        &&& req.obj.metadata.name is Some
        &&& has_vsts_prefix(req.obj.metadata.name->0)
        &&& req.obj.metadata.owner_references is Some
        &&& exists |vsts: VStatefulSetView| #[trigger]
            owner_references.contains(vsts.controller_owner_ref())
    }
    &&& req.obj.kind == PersistentVolumeClaimView::kind() ==> exists |vsts: VStatefulSetView|
        #[trigger] pvc_name_match(req.obj.metadata.name->0, vsts.metadata.name->0)
}

// VSTS controller Only updates Pod owned by itself and does not update PVC
pub open spec fn vsts_guarantee_get_then_update_req(req: GetThenUpdateRequest) -> bool {
    &&& req.obj.kind == PodView::kind()
    &&& has_vsts_prefix(req.obj.metadata.name->0)
    &&& exists |vsts: VStatefulSetView| {
        &&& req.owner_ref == #[trigger] vsts.controller_owner_ref()
        // do not change ownership
        &&& req.obj.metadata.owner_references_contains(vsts.controller_owner_ref())
    }
}

// VSTS controller Only deletes Pod owned by itself
pub open spec fn vsts_guarantee_get_then_delete_req(req: GetThenDeleteRequest) -> bool {
    &&& req.key.kind == PodView::kind()
    &&& exists |vsts: VStatefulSetView| req.owner_ref == #[trigger] vsts.controller_owner_ref()
}

// VSTS internal Rely-Guarantee condition (for itself and used in shield lemma)

pub open spec fn vsts_internal_guarantee_conditions(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |vsts: VStatefulSetView| #[trigger] no_interfering_request_between_vsts(controller_id, vsts)(s)
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

// all requests sent from one reconciliation do not interfere with other reconciliations on different CRs.
pub open spec fn no_interfering_request_between_vsts(controller_id: int, vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src == HostId::Controller(controller_id, vsts.object_ref())
        } ==> match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => vsts_internal_guarantee_create_req(req, vsts),
            APIRequest::GetThenDeleteRequest(req) => vsts_internal_guarantee_get_then_delete_req(req, vsts),
            APIRequest::GetThenUpdateRequest(req) => vsts_internal_guarantee_get_then_update_req(req, vsts),
            // VSTS controller will not issue DeleteRequest, UpdateRequest and UpdateStatusRequest
            _ => false
        }
    }
}

// VSTS controller only creates Pods and PVCs bound to the specific vsts instance
pub open spec fn vsts_internal_guarantee_create_req(req: CreateRequest, vsts: VStatefulSetView) -> bool {
    &&& req.namespace == vsts.object_ref().namespace
    &&& req.obj.metadata.name is Some
    &&& req.obj.metadata.finalizers is None
    &&& req.obj.kind == Kind::PodKind ==> {
        &&& exists |owner_reference: OwnerReferenceView| {
            &&& req.obj.metadata.owner_references == Some(Seq::empty().push(owner_reference))
            &&& #[trigger] owner_reference_eq_without_uid(owner_reference, vsts.controller_owner_ref())
        }
        &&& exists |ord: nat| req.key().name == #[trigger] pod_name(vsts.object_ref().name, ord)
    }
    &&& req.obj.kind == Kind::PersistentVolumeClaimKind ==> {
        &&& req.obj.metadata.owner_references is None
        &&& pvc_name_match(req.obj.metadata.name->0, vsts.metadata.name->0)
    }
}

// VSTS controller only deletes Pods bound to the specific vsts instance
pub open spec fn vsts_internal_guarantee_get_then_delete_req(req: GetThenDeleteRequest, vsts: VStatefulSetView) -> bool {
    &&& req.key().namespace == vsts.object_ref().namespace
    &&& req.key().kind == Kind::PodKind
    &&& exists |ord: nat| req.key().name == #[trigger] pod_name(vsts.object_ref().name, ord)
    &&& owner_reference_eq_without_uid(req.owner_ref, vsts.controller_owner_ref())
}

// VSTS controller only updates Pods bound to the specific vsts instance
pub open spec fn vsts_internal_guarantee_get_then_update_req(req: GetThenUpdateRequest, vsts: VStatefulSetView) -> bool {
    &&& req.namespace == vsts.object_ref().namespace
    &&& req.obj.kind == Kind::PodKind
    &&& exists |ord: nat| req.name == #[trigger] pod_name(vsts.object_ref().name, ord)
    &&& req.obj.metadata.owner_references is Some
    &&& req.obj.metadata.owner_references->0.filter(controller_owner_filter()) == Seq::empty().push(req.owner_ref)
    &&& owner_reference_eq_without_uid(req.owner_ref, vsts.controller_owner_ref())
    &&& req.obj.metadata.deletion_timestamp is None
    &&& req.obj.metadata.finalizers is None
}
// similar to local_pods_and_pvcs_are_bound_to_vsts
// helper invariant to prove both (external) guarantee conditions and internal guarantee conditions

// HINT: because we will prove it as an invariant, we need to pass key to local_pods_and_pvcs_are_bound_to_vsts_with_key
// before the reconciliation starts, !s.ongoing_reconciles(controller_id).contains_key(k) and this proof will be trivial
// during reconciliation, controller obtains vsts from s.ongoing_reconciles(controller_id)[k].triggering_cr
pub open spec fn local_pods_and_pvcs_are_bound_to_vsts(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |k: ObjectRef| #[trigger] s.ongoing_reconciles(controller_id).contains_key(k)
            ==> local_pods_and_pvcs_are_bound_to_vsts_with_key(controller_id, k, s)
    }
}

pub open spec fn local_pods_and_pvcs_are_bound_to_vsts_with_key_in_local_state(vsts: VStatefulSetView, local_state: VStatefulSetReconcileState) -> bool {
    let pvcs = local_state.pvcs;
    let needed_pods = local_state.needed;
    let condemned_pods = local_state.condemned;
    &&& vsts.metadata.well_formed_for_namespaced()
    &&& forall |i| #![trigger needed_pods[i]] 0 <= i < needed_pods.len() && needed_pods[i] is Some ==> {
        let pod = needed_pods[i]->0;
        &&& pod.metadata.name is Some
        &&& get_ordinal(vsts.metadata.name->0, pod.metadata.name->0) is Some
        &&& pod.metadata.namespace == Some(vsts.object_ref().namespace)
        &&& pod.metadata.owner_references is Some
        &&& pod.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()]
        &&& pod.metadata.deletion_timestamp is None
        &&& pod.metadata.finalizers is None
    }
    &&& forall |i| #![trigger condemned_pods[i]] 0 <= i < condemned_pods.len() ==> {
        let pod = condemned_pods[i];
        &&& pod.metadata.name is Some
        &&& get_ordinal(vsts.metadata.name->0, pod.metadata.name->0) is Some
        &&& pod.metadata.namespace == Some(vsts.object_ref().namespace)
        &&& pod.metadata.owner_references is Some
        &&& pod.metadata.owner_references->0.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()]
    }
    &&& forall |i| #![trigger pvcs[i]] 0 <= i < pvcs.len() ==> {
        let pvc = pvcs[i];
        &&& pvc.metadata.name is Some
        &&& pvc.metadata.namespace == Some(vsts.object_ref().namespace)
        &&& pvc_name_match(pvc.metadata.name->0, vsts.metadata.name->0)
        &&& pvc.metadata.owner_references is None
        &&& pvc.metadata.finalizers is None
    }
}

pub open spec fn local_pods_and_pvcs_are_bound_to_vsts_with_key(controller_id: int, key: ObjectRef, s: ClusterState) -> bool {
    let vsts = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr)->Ok_0;
    let local_state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state)->Ok_0;
    
    &&& vsts.object_ref() == key
    &&& local_pods_and_pvcs_are_bound_to_vsts_with_key_in_local_state(vsts, local_state)
    &&& local_state.reconcile_step == VStatefulSetReconcileStepView::AfterListPod ==> {
        let req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        &&& req_msg.dst is APIServer
        &&& req_msg.content.is_list_request()
        &&& req_msg.content.get_list_request() == ListRequest {
            kind: Kind::PodKind,
            namespace: vsts.metadata.namespace.unwrap(),
        }
        &&& forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src is APIServer
            &&& resp_msg_matches_req_msg(msg, req_msg)
            &&& is_ok_resp(msg.content->APIResponse_0)
        } ==> {
            let resp_objs = msg.content.get_list_response().res.unwrap();
            &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
            &&& forall |i| #![trigger resp_objs[i]] 0 <= i < resp_objs.len() ==> {
                let controller_owners = resp_objs[i].metadata.owner_references->0.filter(controller_owner_filter());
                &&& resp_objs[i].metadata.namespace is Some
                // list response should match the ns in request
                &&& resp_objs[i].metadata.namespace->0 == vsts.metadata.namespace->0
                // can pass objects_to_pods
                &&& resp_objs[i].kind == Kind::PodKind
                // Cluster::each_object_in_etcd_has_at_most_one_controller_owner
                &&& resp_objs[i].metadata.owner_references is Some ==> controller_owners.len() <= 1
            }
        }
    }
}

// TODO
#[verifier(external_body)]
pub proof fn lemma_local_pods_and_pvcs_are_bound_to_vsts_with_key_preserves_from_s_to_s_prime(
    cluster: Cluster, controller_id: int, key: ObjectRef, s: ClusterState, s_prime: ClusterState
)
requires
    cluster.next()(s, s_prime),
    Cluster::there_is_the_controller_state(controller_id)(s),
    Cluster::every_in_flight_msg_has_unique_id()(s),
    Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s),
    Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s),
    Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    cluster.each_builtin_object_in_etcd_is_well_formed()(s),
    cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s),
    cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
    Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
    Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id)(s),
    Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
    Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)(s),
    Cluster::etcd_is_finite()(s),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    local_pods_and_pvcs_are_bound_to_vsts_with_key(controller_id, key, s),
    s.ongoing_reconciles(controller_id).contains_key(key),
    s_prime.ongoing_reconciles(controller_id).contains_key(key),
ensures
    local_pods_and_pvcs_are_bound_to_vsts_with_key(controller_id, key, s_prime),
{}

pub proof fn lemma_always_local_pods_and_pvcs_are_bound_to_vsts(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures spec.entails(always(lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id)))),
{
    let invariant = local_pods_and_pvcs_are_bound_to_vsts(controller_id);

    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_builtin_object_in_etcd_is_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>(spec);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(spec, controller_id);
    cluster.lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(spec, controller_id);
    cluster.lemma_always_etcd_is_finite(spec);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id)(s)
        &&& Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)(s)
        &&& Cluster::etcd_is_finite()(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VStatefulSetView>(controller_id)),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)),
        lift_state(Cluster::etcd_is_finite())
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| {
            &&& invariant(s)
            &&& stronger_next(s, s_prime)
            &&& #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
        } implies local_pods_and_pvcs_are_bound_to_vsts_with_key(controller_id, key, s_prime) by {
            if s.ongoing_reconciles(controller_id).contains_key(key) {
                lemma_local_pods_and_pvcs_are_bound_to_vsts_with_key_preserves_from_s_to_s_prime(
                    cluster, controller_id, key, s, s_prime
                );
            } else { // RunScheduledReconcile
                VStatefulSetView::marshal_preserves_integrity();
                VStatefulSetReconcileState::marshal_preserves_integrity();
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}


pub proof fn lemma_guarantee_from_reconcile_state(
    msg: Message,
    state: VStatefulSetReconcileState,
    vsts: VStatefulSetView,
)
    requires
        msg.content is APIRequest,
        reconcile_core(vsts, None, state).1 is Some,
        reconcile_core(vsts, None, state).1->0 is KRequest,
        msg.content->APIRequest_0 == reconcile_core(vsts, None, state).1->0->KRequest_0,
        local_pods_and_pvcs_are_bound_to_vsts_with_key_in_local_state(vsts, state),
    ensures
        match msg.content->APIRequest_0 {
            APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
            APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
            APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
            _ => true,
        }
{
    match state.reconcile_step {
        VStatefulSetReconcileStepView::CreateNeeded => {
            assert(msg.content.is_create_request());
            let req = msg.content.get_create_request();
            let pod = make_pod(vsts, state.needed_index);
            assert(has_vsts_prefix(req.obj.metadata.name->0));
            let owner_references = req.obj.metadata.owner_references->0;
            assert(owner_references.contains(vsts.controller_owner_ref())) by {
                assert(owner_references == pod.metadata.owner_references->0);
                assert(pod.metadata.owner_references->0 == seq![vsts.controller_owner_ref()]);
                assert(owner_references[0] == vsts.controller_owner_ref());
            }
        },
        VStatefulSetReconcileStepView::UpdateNeeded => {
            assert(msg.content.is_get_then_update_request());
            let req = msg.content.get_get_then_update_request();
            let pod = state.needed[state.needed_index as int]->0;
            let owner_references = req.obj.metadata.owner_references->0;
            assert(owner_references.contains(vsts.controller_owner_ref())) by  {
                assert(owner_references == pod.metadata.owner_references->0);
                assert(owner_references.filter(controller_owner_filter()) == seq![vsts.controller_owner_ref()]);
                assert(owner_references.filter(controller_owner_filter()).contains(vsts.controller_owner_ref())) by {
                    assert(owner_references.filter(controller_owner_filter())[0] == vsts.controller_owner_ref());
                }
                seq_filter_contains_implies_seq_contains(owner_references, controller_owner_filter(), vsts.controller_owner_ref());
            }
        },
        _ => {
            // other cases are handled by Verus automatically
        }
    }
}

pub proof fn guarantee_condition_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action (without weak fairness).
        spec.entails(always(lift_action(cluster.next()))),
        // The vsts type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        // The vsts controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    ensures
        spec.entails(always(lift_state(vsts_guarantee(controller_id))))
{
    let invariant = vsts_guarantee(controller_id);

    cluster.lemma_always_cr_states_are_unmarshallable::<VStatefulSetReconciler, VStatefulSetReconcileState, VStatefulSetView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    lemma_always_local_pods_and_pvcs_are_bound_to_vsts(spec, cluster, controller_id);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);

    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& local_pods_and_pvcs_are_bound_to_vsts(controller_id)(s)
        &&& local_pods_and_pvcs_are_bound_to_vsts(controller_id)(s_prime)
        &&& Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    };

    always_to_always_later(spec, lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id)));

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id)),
        later(lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id))),
        lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        VStatefulSetView::marshal_preserves_integrity();
        VStatefulSetReconcileState::marshal_preserves_integrity();
        PodView::marshal_preserves_integrity();
        PersistentVolumeClaimView::marshal_preserves_integrity();

        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(req_msg_opt) => {
                let req_msg = req_msg_opt.unwrap();

                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content->APIRequest_0 {
                    APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
                    APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
                    APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
                    _ => true,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
            Step::ControllerStep((id, resp_msg_opt, cr_key_opt)) => {
                let cr_key = cr_key_opt->0;
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content->APIRequest_0 {
                    APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
                    APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
                    APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
                    _ => true,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.

                    if id == controller_id {
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());
                        if new_msgs.contains(msg) {
                            let state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            let vsts = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                            assert(reconcile_core(vsts, None, state).1 is Some);
                            assert(reconcile_core(vsts, None, state).1->0 is KRequest);
                            assert(msg.content->APIRequest_0 == reconcile_core(vsts, None, state).1->0->KRequest_0);
                            lemma_guarantee_from_reconcile_state(msg, state, vsts);
                        }
                    }
                }
            }
            _ => {
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content->APIRequest_0 {
                    APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
                    APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
                    APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
                    _ => true,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}

pub proof fn internal_guarantee_condition_holds(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, vsts: VStatefulSetView
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    ensures
        spec.entails(always(lift_state(no_interfering_request_between_vsts(controller_id, vsts))))
{
    let invariant = no_interfering_request_between_vsts(controller_id, vsts);

    cluster.lemma_always_cr_states_are_unmarshallable::<VStatefulSetReconciler, VStatefulSetReconcileState, VStatefulSetView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    lemma_always_local_pods_and_pvcs_are_bound_to_vsts(spec, cluster, controller_id);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>(spec);

    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& local_pods_and_pvcs_are_bound_to_vsts(controller_id)(s)
        &&& local_pods_and_pvcs_are_bound_to_vsts(controller_id)(s_prime)
        &&& Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()(s)
    };

    always_to_always_later(spec, lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id)));

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id)),
        later(lift_state(local_pods_and_pvcs_are_bound_to_vsts(controller_id))),
        lift_state(Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>())
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        VStatefulSetView::marshal_preserves_integrity();
        VStatefulSetReconcileState::marshal_preserves_integrity();
        PodView::marshal_preserves_integrity();
        PersistentVolumeClaimView::marshal_preserves_integrity();

        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(req_msg_opt) => {
                let req_msg = req_msg_opt.unwrap();

                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src == HostId::Controller(controller_id, vsts.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true,
                    APIRequest::CreateRequest(req) => vsts_internal_guarantee_create_req(req, vsts),
                    APIRequest::GetThenDeleteRequest(req) => vsts_internal_guarantee_get_then_delete_req(req, vsts),
                    APIRequest::GetThenUpdateRequest(req) => vsts_internal_guarantee_get_then_update_req(req, vsts),
                    _ => false,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
            Step::ControllerStep((id, resp_msg_opt, cr_key_opt)) => {
                let cr_key = cr_key_opt->0;
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src == HostId::Controller(controller_id, vsts.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true,
                    APIRequest::CreateRequest(req) => vsts_internal_guarantee_create_req(req, vsts),
                    APIRequest::GetThenDeleteRequest(req) => vsts_internal_guarantee_get_then_delete_req(req, vsts),
                    APIRequest::GetThenUpdateRequest(req) => vsts_internal_guarantee_get_then_update_req(req, vsts),
                    _ => false,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.

                    if id == controller_id && cr_key == vsts.object_ref() {
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());
                        if new_msgs.contains(msg) {
                            let triggering_vsts = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                            let state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            assert(reconcile_core(triggering_vsts, None, state).1 is Some);
                            assert(reconcile_core(triggering_vsts, None, state).1->0 is KRequest);
                            assert(msg.content->APIRequest_0 == reconcile_core(triggering_vsts, None, state).1->0->KRequest_0);

                            // Match on the reconcile step to handle each case
                            match state.reconcile_step {
                                VStatefulSetReconcileStepView::CreatePVC => {
                                    assert(msg.content.is_create_request());
                                    let req = msg.content.get_create_request();
                                    let pvc = state.pvcs[state.pvc_index as int];
                                    assert(req.obj.metadata == pvc.metadata);
                                    assert(pvc_name_match(req.obj.metadata.name->0, vsts.object_ref().name));
                                },
                                VStatefulSetReconcileStepView::CreateNeeded => {
                                    assert(msg.content.is_create_request());
                                    let req = msg.content.get_create_request();
                                    assert(req.key().name == pod_name(vsts.object_ref().name, state.needed_index));
                                    let owner_ref = req.obj.metadata.owner_references->0[0];
                                    assert(owner_reference_eq_without_uid(owner_ref, vsts.controller_owner_ref()));
                                },
                                VStatefulSetReconcileStepView::UpdateNeeded => {
                                    assert(msg.content.is_get_then_update_request());
                                    let req = msg.content.get_get_then_update_request();
                                    let pod = state.needed[state.needed_index as int]->0;
                                    assert(get_ordinal(vsts.object_ref().name, pod.metadata.name->0) is Some);
                                    let ord = get_ordinal(vsts.object_ref().name, pod.metadata.name->0)->0;
                                    assert(req.name == pod_name(vsts.object_ref().name, ord));
                                    let controller_owner_references = pod.metadata.owner_references->0.filter(controller_owner_filter());
                                    let owner_ref = controller_owner_references[0];
                                    assert(owner_reference_eq_without_uid(owner_ref, vsts.controller_owner_ref()));
                                },
                                VStatefulSetReconcileStepView::DeleteCondemned => {
                                    assert(msg.content.is_get_then_delete_request());
                                    let req = msg.content.get_get_then_delete_request();
                                    let condemned_pod = state.condemned[state.condemned_index as int];
                                    assert(get_ordinal(vsts.object_ref().name, condemned_pod.metadata.name->0) is Some);
                                    let ord = get_ordinal(vsts.object_ref().name, condemned_pod.metadata.name->0)->0;
                                    assert(req.key().name == pod_name(vsts.object_ref().name, ord));
                                },
                                VStatefulSetReconcileStepView::DeleteOutdated => {
                                    assert(msg.content.is_get_then_delete_request());
                                    let req = msg.content.get_get_then_delete_request();
                                    if let Some(pod) = get_largest_unmatched_pods(triggering_vsts, state.needed) {
                                        seq_filter_contains_implies_seq_contains(state.needed, outdated_pod_filter(triggering_vsts), Some(pod));
                                        // trigger for local_pods_and_pvcs_are_bound_to_vsts_with_key_in_local_state
                                        assert(exists |i: int| #[trigger] state.needed[i] == Some(pod));
                                        assert(get_ordinal(vsts.object_ref().name, pod.metadata.name->0) is Some);
                                        let ord = get_ordinal(vsts.object_ref().name, pod.metadata.name->0)->0;
                                        get_ordinal_eq_pod_name(vsts.object_ref().name, ord, pod.metadata.name->0);
                                        assert(req.key().name == pod.metadata.name->0);
                                    } else {
                                        assert(false); // should not has any new message
                                    }
                                },
                                _ => {
                                    // other cases are trivial
                                }
                            }
                        }
                    }
                }
            }
            _ => {
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src == HostId::Controller(controller_id, vsts.object_ref())
                } implies match msg.content->APIRequest_0 {
                    APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true,
                    APIRequest::CreateRequest(req) => vsts_internal_guarantee_create_req(req, vsts),
                    APIRequest::GetThenDeleteRequest(req) => vsts_internal_guarantee_get_then_delete_req(req, vsts),
                    APIRequest::GetThenUpdateRequest(req) => vsts_internal_guarantee_get_then_update_req(req, vsts),
                    _ => false,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}

pub proof fn internal_guarantee_condition_holds_on_all_vsts(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    ensures
        spec.entails(always(lift_state(vsts_internal_guarantee_conditions(controller_id))))
{
    let guarantee = lift_state(vsts_internal_guarantee_conditions(controller_id));
    let target = always(guarantee);
    let no_interfering_request = |vsts: VStatefulSetView| lift_state(no_interfering_request_between_vsts(controller_id, vsts));
    assert forall |ex: Execution<ClusterState>| spec.satisfied_by(ex) implies target.satisfied_by(ex) by {
        assert forall |vsts: VStatefulSetView| #![trigger no_interfering_request(vsts)] always(no_interfering_request(vsts)).satisfied_by(ex) by {
            internal_guarantee_condition_holds(spec, cluster, controller_id, vsts);
            assert(spec.entails(always(no_interfering_request(vsts))));
            assert(valid(spec.implies(always(no_interfering_request(vsts)))));
            assert(spec.implies(always(no_interfering_request(vsts))).satisfied_by(ex));
        }
        assert(forall |vsts: VStatefulSetView, i: nat| #[trigger] no_interfering_request(vsts).satisfied_by(ex.suffix(i)));
        assert forall |i: nat| #[trigger] guarantee.satisfied_by(ex.suffix(i)) by {
            assert forall |vsts: VStatefulSetView| #[trigger] no_interfering_request_between_vsts(controller_id, vsts)(ex.suffix(i).head()) by {
                assert(no_interfering_request(vsts).satisfied_by(ex.suffix(i)));
            }
        };
    }
}

}