use crate::kubernetes_api_objects::spec::{prelude::*, persistent_volume_claim::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::kubernetes_cluster::spec::api_server::{state_machine::*, types::InstalledTypes};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::{
    trusted::{spec_types::*, liveness_theorem::*, rely_guarantee::*},
    model::{reconciler::*, install::*},
    proof::{predicate::*, helper_lemmas::*, internal_rely_guarantee::*},
};
use crate::vstatefulset_controller::trusted::step::VStatefulSetReconcileStepView;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::{prelude::*, map_lib::*};
use crate::vstd_ext::{string_view::*, seq_lib::*, set_lib::*, map_lib::*};

verus! {

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
        local_pods_and_pvcs_are_bound_to_vsts_with_key_in_local_state(vsts.object_ref(), state),
    ensures
        match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
            APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
            APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
            _ => false,
        }
{
    match state.reconcile_step {
        VStatefulSetReconcileStepView::CreateNeeded => {
            assert(msg.content.is_create_request());
            let req = msg.content.get_create_request();
            assert(has_vsts_prefix(req.obj.metadata.name->0));
            assert(req.obj.metadata.owner_references == Some(seq![vsts.controller_owner_ref()]));
            assert(has_vsts_prefix(req.obj.metadata.name->0));
        },
        VStatefulSetReconcileStepView::CreatePVC => {
            assert(msg.content.is_create_request());
            let req = msg.content.get_create_request();
            let pvc = state.pvcs[state.pvc_index as int];
            pvc_name_match_implies_has_vsts_prefix(pvc.metadata.name->0);
            assert(pvc.metadata.owner_references is None);
            assert(req.obj == pvc.marshal());
            assert(has_vsts_prefix(req.obj.metadata.name->0));
        },
        VStatefulSetReconcileStepView::UpdateNeeded => {
            assert(msg.content.is_get_then_update_request());
            let req = msg.content.get_get_then_update_request();
            let pod = state.needed[state.needed_index as int]->0;
            assert(req.name == pod.metadata.name->0);
            assert(has_vsts_prefix(req.name));
            assert(req.obj.metadata.owner_references == Some(seq![vsts.controller_owner_ref()]));
            assert(has_vsts_prefix(req.obj.metadata.name->0));
        },
        VStatefulSetReconcileStepView::DeleteCondemned => {
            assert(msg.content.is_get_then_delete_request());
            let req = msg.content.get_get_then_delete_request();
            let pod = state.condemned[state.condemned_index as int];
            assert(has_vsts_prefix(pod.metadata.name->0));
            assert(req.key.name == pod.metadata.name->0);
            assert(has_vsts_prefix(req.key.name));
            assert(req.owner_ref == vsts.controller_owner_ref());
        },
        VStatefulSetReconcileStepView::DeleteOutdated => {
            if let Some(pod) = get_largest_unmatched_pods(vsts, state.needed) {
                assert(msg.content.is_get_then_delete_request());
                let req = msg.content.get_get_then_delete_request();
                seq_filter_contains_implies_seq_contains(state.needed, outdated_pod_filter(vsts), Some(pod));
                assert(exists |i| 0 <= i < state.needed.len() && #[trigger] state.needed[i] == Some(pod));
                assert(has_vsts_prefix(pod.metadata.name->0));
                assert(req.key.name == pod.metadata.name->0);
                assert(has_vsts_prefix(req.key.name));
                assert(req.owner_ref == vsts.controller_owner_ref());
            }
        }
        VStatefulSetReconcileStepView::Init | VStatefulSetReconcileStepView::GetPVC => {},
        _ => {
            assert(reconcile_core(vsts, None, state).1 is None); // there is no message sent
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
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(spec, controller_id);

    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& local_pods_and_pvcs_are_bound_to_vsts(controller_id)(s)
        &&& local_pods_and_pvcs_are_bound_to_vsts(controller_id)(s_prime)
        &&& Cluster::cr_states_are_unmarshallable::<VStatefulSetReconcileState, VStatefulSetView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)(s)
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
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id))
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |msg| {
            &&& invariant(s)
            &&& stronger_next(s, s_prime)
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } implies match msg.content->APIRequest_0 {
            APIRequest::ListRequest(_) | APIRequest::GetRequest(_) => true, // read-only requests
            APIRequest::CreateRequest(req) => vsts_guarantee_create_req(req),
            APIRequest::GetThenUpdateRequest(req) => vsts_guarantee_get_then_update_req(req),
            APIRequest::GetThenDeleteRequest(req) => vsts_guarantee_get_then_delete_req(req),
            _ => false,
        } by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            let new_msgs = s_prime.in_flight().sub(s.in_flight());
            match step {
                Step::ControllerStep((id, _, cr_key_opt)) => {
                    let cr_key = cr_key_opt->0;
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                    if id == controller_id && new_msgs.contains(msg) {
                        let state = VStatefulSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                        let vsts = VStatefulSetView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                        assert(msg.content->APIRequest_0 == reconcile_core(vsts, None, state).1->0->KRequest_0);
                        lemma_guarantee_from_reconcile_state(msg, state, vsts);
                    }
                },
                _ => {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}

}