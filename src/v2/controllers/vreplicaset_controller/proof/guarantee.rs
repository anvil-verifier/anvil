use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::reconciler::spec::io::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    proof::helper_invariants,
    trusted::{
        rely_guarantee::*,
        spec_types::*, 
    },
};
use crate::vstd_ext::seq_lib::*;
use vstd::prelude::*;

verus! {

// This invariant is a strengthened version of `vrs_guarantee_delete_req` that
// requires that any delete request sent by a VReplicaSet controller has a
// resource version precondition that is less than the resource version
// counter of the API server. Essentially, this prevents the delete request
// from interfering with newly created or updated objects.
spec fn stronger_vrs_guarantee_delete_req(req: DeleteRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key];
        &&& req.key.kind == Kind::PodKind
        &&& req.preconditions.is_Some()
        &&& req.preconditions.get_Some_0().resource_version.is_Some()
        // strengthened condition.
        &&& req.preconditions.get_Some_0().resource_version.get_Some_0() < 
            s.api_server.resource_version_counter
        &&& {
            &&& s.resources().contains_key(req.key)
            &&& etcd_obj.metadata.resource_version 
                == req.preconditions.get_Some_0().resource_version
        } ==> {
            let controller_owners = etcd_obj.metadata.owner_references
                .get_Some_0()
                .filter(|o: OwnerReferenceView| {
                    o.controller.is_Some() && o.controller.get_Some_0()
                });
            &&& etcd_obj.metadata.owner_references.is_Some()
            &&& exists |vrs: VReplicaSetView| 
                controller_owners == seq![#[trigger] vrs.controller_owner_ref()]
        }
    }
}

spec fn stronger_vrs_guarantee(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src == HostId::Controller(other_id)
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::ListRequest(_) => true,
            APIRequest::CreateRequest(req) => vrs_guarantee_create_req(req)(s),
            APIRequest::DeleteRequest(req) => stronger_vrs_guarantee_delete_req(req)(s),
            _ => false,
        }
    }
}

#[verifier(rlimit(100))]
pub proof fn guarantee_condition_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action (without weak fairness).
        spec.entails(always(lift_action(cluster.next()))),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
        // The vrs controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vrs_controller_model()),
    ensures
        spec.entails(always(lift_state(vrs_guarantee(controller_id))))
{
    let invariant = vrs_guarantee(controller_id);
    let stronger_invariant = stronger_vrs_guarantee(controller_id);

    cluster.lemma_always_cr_states_are_unmarshallable::<VReplicaSetReconciler, VReplicaSetReconcileState, VReplicaSetView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    helper_invariants::lemma_always_each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(spec, cluster, controller_id);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& helper_invariants::each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(helper_invariants::each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
    );

    assert forall |s, s_prime| stronger_invariant(s) && #[trigger] stronger_next(s, s_prime) implies stronger_invariant(s_prime) by {
        VReplicaSetView::marshal_preserves_integrity();
        VReplicaSetReconcileState::marshal_preserves_integrity();
        PodView::marshal_preserves_integrity();

        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(req_msg_opt) => {
                let req_msg = req_msg_opt.unwrap();

                assert forall |msg| {
                    &&& stronger_invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content.is_APIRequest()
                    &&& msg.src == HostId::Controller(controller_id)
                } implies match msg.content.get_APIRequest_0() {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_guarantee_create_req(req)(s_prime),
                    APIRequest::DeleteRequest(req) => stronger_vrs_guarantee_delete_req(req)(s_prime),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
            Step::ControllerStep((id, _, cr_key_opt)) => {
                let cr_key = cr_key_opt.get_Some_0();
                assert forall |msg| {
                    &&& stronger_invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content.is_APIRequest()
                    &&& msg.src == HostId::Controller(controller_id)
                } implies match msg.content.get_APIRequest_0() {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_guarantee_create_req(req)(s_prime),
                    APIRequest::DeleteRequest(req) => stronger_vrs_guarantee_delete_req(req)(s_prime),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.

                    if id == controller_id {
                        let new_msgs = s_prime.in_flight().sub(s.in_flight());
                        if new_msgs.contains(msg) && msg.content.is_delete_request() {
                            let req = msg.content.get_delete_request();
                            let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                            let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();

                            if state.reconcile_step.is_AfterListPods() {
                                let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                                let cr_msg = step.get_ControllerStep_0().1.get_Some_0();
                                let req_msg = s.ongoing_reconciles(controller_id)[cr_key].pending_req_msg.get_Some_0();
                                let objs = cr_msg.content.get_list_response().res.unwrap();
                                let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                                let pods_or_none = objects_to_pods(objs);
                                let pods = pods_or_none.unwrap();
                                let filtered_pods = filter_pods(pods, triggering_cr);

                                assert forall |i| #![auto] 
                                    0 <= i < filtered_pods.len()
                                    && stronger_invariant(s)
                                    && stronger_next(s, s_prime)
                                    implies
                                    (filtered_pods[i].object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                                    && ((s_prime.resources().contains_key(filtered_pods[i].object_ref())
                                        && s_prime.resources()[filtered_pods[i].object_ref()].metadata.resource_version
                                            == filtered_pods[i].metadata.resource_version) ==>
                                        (s_prime.resources()[filtered_pods[i].object_ref()].metadata.owner_references_contains(
                                            triggering_cr.controller_owner_ref()
                                            )
                                            ))
                                    && filtered_pods[i].metadata.resource_version.is_some()
                                    && filtered_pods[i].metadata.resource_version.unwrap()
                                        < s_prime.api_server.resource_version_counter) by {

                                    assert({
                                        let req_msg = s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.get_Some_0();
                                        &&& s.in_flight().contains(cr_msg)
                                        &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg.is_Some()
                                        &&& cr_msg.src.is_APIServer()
                                        &&& resp_msg_matches_req_msg(cr_msg, req_msg)});
                                    
                                    seq_filter_contains_implies_seq_contains(
                                        pods,
                                        |pod: PodView|
                                        pod.metadata.owner_references_contains(triggering_cr.controller_owner_ref())
                                        && triggering_cr.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
                                        && pod.metadata.deletion_timestamp.is_None(),
                                        filtered_pods[i]
                                    );

                                    // Show that pods[idx1] and filtered_pods[i] have the same metadata.
                                    let idx1 = choose |j| 0 <= j < pods.len() && pods[j] == filtered_pods[i];
                                    assert(pods[idx1].metadata == filtered_pods[i].metadata);

                                    assert(objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 );
                                    assert(objs.len() == pods.len());

                                    // Show that pods[idx1] and objs[idx1] have the same metadata.
                                    seq_pred_false_on_all_elements_is_equivalent_to_empty_filter(
                                        objs, |o: DynamicObjectView| PodView::unmarshal(o).is_err()
                                    );
                                    assert(objs.contains(objs[idx1]));
                                    assert(PodView::unmarshal(objs[idx1]).is_ok());

                                    let unwrap_obj = |o: DynamicObjectView| PodView::unmarshal(o).unwrap();
                                    assert(pods == objs.map_values(unwrap_obj));
                                    assert(objs.contains(objs[idx1]));
                                    assert(objs[idx1].metadata == pods[idx1].metadata);
                                }
                            }      
                            
                            if state.reconcile_step.is_AfterDeletePod() || state.reconcile_step.is_AfterListPods() {
                                let etcd_obj = s.resources()[req.key];
                                if s.resources().contains_key(req.key)
                                    && etcd_obj.metadata.resource_version
                                        == req.preconditions.get_Some_0().resource_version {
                                    let owners = etcd_obj.metadata.owner_references.get_Some_0();
                                    let controller_owners = owners.filter(
                                        |o: OwnerReferenceView| o.controller.is_Some() && o.controller.get_Some_0()
                                    );

                                    assert(controller_owners.len() <= 1);
                                    assert(etcd_obj.metadata.owner_references_contains(
                                        triggering_cr.controller_owner_ref()));
                                    assert(owners.contains(triggering_cr.controller_owner_ref()));
                                    assert(controller_owners.contains(triggering_cr.controller_owner_ref()));
                                    assert(controller_owners[0] == triggering_cr.controller_owner_ref());
                                    assert(controller_owners == seq![triggering_cr.controller_owner_ref()]);
                                }
                            }
                        }
                    }
                }
            }
            _ => {
                assert forall |msg| {
                    &&& stronger_invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content.is_APIRequest()
                    &&& msg.src == HostId::Controller(controller_id)
                } implies match msg.content.get_APIRequest_0() {
                    APIRequest::ListRequest(_) => true,
                    APIRequest::CreateRequest(req) => vrs_guarantee_create_req(req)(s_prime),
                    APIRequest::DeleteRequest(req) => stronger_vrs_guarantee_delete_req(req)(s_prime),
                    _ => false, 
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, stronger_invariant);
    always_weaken(spec, lift_state(stronger_invariant), lift_state(invariant));
}

}
