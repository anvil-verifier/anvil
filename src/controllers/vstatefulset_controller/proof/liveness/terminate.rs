use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    trusted::{spec_types::*, step::VStatefulSetReconcileStepView, step::VStatefulSetReconcileStepView::*},
    proof::predicate::*,
};
use vstd::prelude::*;

verus! {

pub proof fn reconcile_eventually_terminates_on_vsts_object(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
    spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
    spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
    spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
    spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
    spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
    spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()))),
    spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)))),
    spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref())))),
    // no sent request at certain steps
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(Init))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(GetPVC))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(CreatePVC))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(SkipPVC))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(CreateNeeded))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(UpdateNeeded))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(DeleteCondemned))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(DeleteOutdated))))),
    // there is always sent request/pending response at certain steps for vsts to transit to next state
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(AfterListPod))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(AfterGetPVC))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(AfterCreatePVC))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(AfterCreateNeeded))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(AfterUpdateNeeded))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(AfterDeleteCondemned))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(AfterDeleteOutdated))))),
ensures
    spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())))),
{
    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref());

    // First, prove that reconcile_done \/ reconcile_error \/ reconcile_idle ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, vsts.object_ref());
    cluster.lemma_reconcile_done_leads_to_reconcile_idle(spec, controller_id, vsts.object_ref());
    temp_pred_equality(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Done, None, None, None)), lift_state(cluster.reconciler_reconcile_done(controller_id, vsts.object_ref())));
    temp_pred_equality(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Error, None, None, None)), lift_state(cluster.reconciler_reconcile_error(controller_id, vsts.object_ref())));
    entails_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));

    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::GetPVC, None, None, None)).leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterGetPVC, None, None, None)).leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::CreatePVC, None, None, None)).leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterCreatePVC, None, None, None)).leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::SkipPVC, None, None, None)).leads_to(lift_state(reconcile_idle))));
    
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::CreateNeeded, None, None, None)).leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterCreateNeeded, None, None, None)).leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::UpdateNeeded, None, None, None)).leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterUpdateNeeded, None, None, None)).leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::DeleteCondemned, None, None, None)).leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterDeleteCondemned, None, None, None)).leads_to(lift_state(reconcile_idle))));
    
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::DeleteOutdated, None, None, None)).leads_to(lift_state(reconcile_idle))));
    // assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterDeleteOutdated, None, None, None)).leads_to(lift_state(reconcile_idle))));

    // Prove AfterListPod | Done ~> reconcile_idle
    assume(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterListPod, None, None, None)).leads_to(lift_state(reconcile_idle))));
    assert(spec.entails(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Done, None, None, None))
        .leads_to(lift_state(reconcile_idle))));
    or_leads_to_combine_n!(
        spec,
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterListPod, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Done, None, None, None));
        lift_state(reconcile_idle)
    );
    temp_pred_equality(lift_state(Cluster::at_expected_reconcile_states(controller_id, vsts.object_ref(),
        |rs: ReconcileLocalState| (lift_step(AfterListPod)(rs) || lift_step(Done)(rs)))),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterListPod, None, None, None)).or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Done, None, None, None)))
    );
    assert(spec.entails(lift_state(Cluster::at_expected_reconcile_states(controller_id, vsts.object_ref(),
        |rs: ReconcileLocalState| (lift_step(AfterListPod)(rs) || lift_step(Done)(rs))))
        .leads_to(lift_state(reconcile_idle))));

    // Need some extra statements to prove the lemma
    VStatefulSetReconcileState::marshal_preserves_integrity();

    // Prove that reconcile init state can reach AfterListPod | Done
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, controller_id, vsts.object_ref(),
        lift_step(Init),
        |rs: ReconcileLocalState| (lift_step(AfterListPod)(rs) || lift_step(Done)(rs))
    );

    assume(spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), lift_step(AfterDeleteOutdated))))));

    cluster.lemma_from_some_state_to_arbitrary_next_state(spec, controller_id, vsts.object_ref(), lift_step(AfterDeleteOutdated), |rs: ReconcileLocalState| (lift_step(Error)(rs) || lift_step(Done)(rs)));

    let error_or_done = Cluster::at_expected_reconcile_states(
        controller_id, vsts.object_ref(),
        |rs: ReconcileLocalState| (lift_step(Error)(rs) || lift_step(Done)(rs))
    );

    assert(spec.entails(lift_state(Cluster::at_expected_reconcile_states(controller_id, vsts.object_ref(), lift_step(AfterDeleteOutdated))).leads_to(lift_state(error_or_done))));
    assume(spec.entails(lift_state(error_or_done).leads_to(lift_state(reconcile_idle))));

    leads_to_trans_n!(
        spec, 
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vsts.object_ref(), lift_step(AfterDeleteOutdated))), 
        lift_state(error_or_done),
        lift_state(reconcile_idle)
    );

    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterDeleteOutdated, None, None, None)),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vsts.object_ref(), lift_step(AfterDeleteOutdated)))
    );

    // Needed to show Init ~> Done
    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Init, None, None, None)),
        lift_state(Cluster::at_expected_reconcile_states(controller_id, vsts.object_ref(), lift_step(Init)))
    );

    // Call the lemma to establish the equality
    lemma_true_equal_to_reconcile_idle_or_at_any_state(vsts, controller_id);

    // Use or_leads_to_combine_and_equality to combine all the individual leads_to proofs
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Init, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterListPod, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::GetPVC, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterGetPVC, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::CreatePVC, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterCreatePVC, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::SkipPVC, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::CreateNeeded, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterCreateNeeded, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::UpdateNeeded, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterUpdateNeeded, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::DeleteCondemned, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterDeleteCondemned, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::DeleteOutdated, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterDeleteOutdated, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Done, None, None, None)),
        lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Error, None, None, None));
        lift_state(reconcile_idle)
    );
}

pub open spec fn at_step_state_pred(controller_id: int, vsts: VStatefulSetView, step: VStatefulSetReconcileStepView, needed_index: Option<nat>, condemned_index: Option<nat>, pvc_index: Option<nat>) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(
        controller_id, vsts.object_ref(),
        at_step_closure(step, needed_index, condemned_index, pvc_index)
    )
}

pub open spec fn at_step_closure(step: VStatefulSetReconcileStepView, needed_index: Option<nat>, condemned_index: Option<nat>, pvc_index: Option<nat>) -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
            let unmarshalled_state = VStatefulSetReconcileState::unmarshal(s).unwrap();
            unmarshalled_state.reconcile_step == step &&
            (needed_index is None || needed_index->0 == unmarshalled_state.needed_index) &&
            (condemned_index is None || condemned_index->0 == unmarshalled_state.condemned_index) &&
            (pvc_index is None || pvc_index->0 == unmarshalled_state.pvc_index)
    }
}

#[verifier(external_body)]
proof fn lemma_true_equal_to_reconcile_idle_or_at_any_state(vsts: VStatefulSetView, controller_id: int)
    ensures true_pred::<ClusterState>()
                == lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()) })
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Init, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterListPod, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::GetPVC, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterGetPVC, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::CreatePVC, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterCreatePVC, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::SkipPVC, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::CreateNeeded, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterCreateNeeded, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::UpdateNeeded, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterUpdateNeeded, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::DeleteCondemned, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterDeleteCondemned, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::DeleteOutdated, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::AfterDeleteOutdated, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Done, None, None, None)))
                    .or(lift_state(at_step_state_pred(controller_id, vsts, VStatefulSetReconcileStepView::Error, None, None, None)))
{}

}