use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
    proof::predicate::*,
};
use vstd::prelude::*;

verus! {

pub proof fn reconcile_eventually_terminates_on_vd_object(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
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
    spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()))),
    spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)))),
    spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())))),
    // no request in init
    spec.entails(always(
        lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_closure(VDeploymentReconcileStepView::Init)
        )))),
    // there is always pending request for vd to proceed
    spec.entails(always(
        lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_closure(VDeploymentReconcileStepView::AfterCreateNewVRS)
        )))),
    spec.entails(always(
        lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_closure(VDeploymentReconcileStepView::AfterScaleNewVRS)
        )))),
    spec.entails(always(
        lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_closure(VDeploymentReconcileStepView::AfterScaleDownOldVRS)
        )))),
ensures
    // why it's true_pred here?
    spec.entails(true_pred().leads_to(
        lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()))
    )),
{
    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref());
    
    // 1, prove that reconcile_done \/ reconcile_error \/ reconcile_ide ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, vd.object_ref());
    cluster.lemma_reconcile_done_leads_to_reconcile_idle(spec, controller_id, vd.object_ref());
    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vd, VDeploymentReconcileStepView::Done)),
        lift_state(cluster.reconciler_reconcile_done(controller_id, vd.object_ref()))
    );
    temp_pred_equality(
        lift_state(at_step_state_pred(controller_id, vd, VDeploymentReconcileStepView::Error)),
        lift_state(cluster.reconciler_reconcile_error(controller_id, vd.object_ref()))
    );
    entails_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));

    // 2.1, AfterScaleDownOldVRS && state.old_vrs_list.len()==0 ~> to reconcile_idle.
    let state_at_done_or_error_step = |s: ReconcileLocalState| {
        let unmarshalled_s = VDeploymentReconcileState::unmarshal(s).unwrap();
        unmarshalled_s.reconcile_step == VDeploymentReconcileStepView::Done
        || unmarshalled_s.reconcile_step == VDeploymentReconcileStepView::Error
    };
    // Done ~> idle && Error ~> idle => Done \/ Error ~> idle
    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), state_at_done_or_error_step)),
        lift_state(cluster.reconciler_reconcile_done(controller_id, vd.object_ref())),
        lift_state(cluster.reconciler_reconcile_error(controller_id, vd.object_ref()));
        lift_state(reconcile_idle)
    );
    // AfterScaleDownOldVRS && state.old_vrs_list.len()==0 ~> Done \/ Error ~> idle
    let empty_old_vrs_list_pred = |s: VDeploymentReconcileState| s.old_vrs_list.len() == 0;
    lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
        spec, vd, controller_id, VDeploymentReconcileStepView::AfterScaleDownOldVRS, empty_old_vrs_list_pred);
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, vd.marshal(),
        at_step_and_closure(VDeploymentReconcileStepView::AfterScaleDownOldVRS, empty_old_vrs_list_pred), state_at_done_or_error_step);
    // 2.2, AfterScaleDownOldVRS && state.old_vrs_list.len()==n ==> idle
    assert forall |n: nat| spec.entails(#[trigger] lift_state(after_scale_down_old_vrs_rank(controller_id, vd, n as nat))
        .leads_to(lift_state(after_scale_down_old_vrs_rank(controller_id, vd, 0 as nat)))) by {
        // n | Error ~> n-1 | Error
        assert forall |n: nat| #![trigger after_scale_down_old_vrs_rank(controller_id, vd, n)]
            n > 0 implies spec.entails(lift_state(after_scale_down_old_vrs_rank(controller_id, vd, n as nat))
                .leads_to(lift_state(after_scale_down_old_vrs_rank(controller_id, vd, (n - 1) as nat)))) by {
            lemma_from_old_vrs_of_n_to_old_vrs_of_n_minus_1(spec, vd, cluster, controller_id, n);
        }
        // n ~> n-1 ~> 0
        leads_to_rank_step_one(spec, |n| lift_state(after_scale_down_old_vrs_rank(controller_id, vd, n as nat)));
        // n ~> n | Error
        always_implies_to_leads_to(
            spec, lift_state(at_step_and_state_pred(controller_id, vd, VDeploymentReconcileStepView::AfterScaleDownOldVRS,
                |vds: VDeploymentReconcileState| vds.old_vrs_list.len() == n as nat)),
            lift_state(after_scale_down_old_vrs_rank(controller_id, vd, n as nat)));
        // n | Error ~> 0 | Error
        assert(spec.entails((|n| lift_state(after_scale_down_old_vrs_rank(controller_id, vd, n as nat))
            .leads_to(lift_state(after_scale_down_old_vrs_rank(controller_id, vd, 0 as nat))))));
        // n | Error ~> 0 | Error ~> reconcile_idle
        leads_to_trans_n!(
            spec, lift_state(after_scale_down_old_vrs_rank(controller_id, vd, n as nat)),
            lift_state(after_scale_down_old_vrs_rank(controller_id, vd, 0 as nat)),
            lift_state(reconcile_idle));
    }
    
}

pub open spec fn at_step_state_pred(controller_id: int, vd: VDeploymentView, step: VDeploymentReconcileStepView) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), at_step_closure(step))
}

pub open spec fn at_step_and_state_pred(controller_id: int, vd: VDeploymentView,
    step: VDeploymentReconcileStepView, pred: spec_fn(VDeploymentReconcileState) -> bool
) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(controller_id, vd.object_ref(), at_step_and_closure(step, pred))
}

pub open spec fn after_scale_down_old_vrs_rank(controller_id: int, vd: VDeploymentView, n: nat) -> StatePred<ClusterState> {
    |s: ClusterState| {
        ||| at_step_and_state_pred(controller_id, vd, VDeploymentReconcileStepView::AfterScaleDownOldVRS,
                |vds: VDeploymentReconcileState| vds.old_vrs_list.len() == n)(s)
        ||| at_step_state_pred(controller_id, vd, VDeploymentReconcileStepView::Error)(s)
    }
}

// what is satisfied at step should also be satisfied at step and pred
pub proof fn lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
    spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int,
    step: VDeploymentReconcileStepView, pred: spec_fn(VDeploymentReconcileState) -> bool
)
requires
    spec.entails(always(
        lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_closure(step)
        )))),
ensures
    spec.entails(always(
        lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_and_closure(step, pred)
        )))),
{
    let pre = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id,
        vd.object_ref(),
        at_step_closure(step)
    ));
    let post = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id,
        vd.object_ref(),
        at_step_and_closure(step, pred)
    ));
    assert forall |ex| #![auto] spec.satisfied_by(ex) && spec.entails(always(pre)) implies always(post).satisfied_by(ex) by {
        assert(forall |ex| #[trigger] spec.implies(always(pre)).satisfied_by(ex));
        assert(forall |ex| spec.implies(always(pre)).satisfied_by(ex) <==> (spec.satisfied_by(ex) ==> #[trigger] always(pre).satisfied_by(ex)));
        assert(always(pre).satisfied_by(ex));

        assert forall |i: nat| #![auto] pre.satisfied_by(ex.suffix(i)) implies post.satisfied_by(ex.suffix(i)) by {
        }
    }
}

pub proof fn lemma_from_old_vrs_of_n_to_old_vrs_of_n_minus_1(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int, n: nat
)
requires
    n > 0,
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
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
    spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()))),
    spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VDeploymentView>(controller_id)))),
    spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vd.object_ref())))),
    spec.entails(always(
        lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_closure(VDeploymentReconcileStepView::AfterScaleDownOldVRS)
        )))),
ensures
    spec.entails(lift_state(after_scale_down_old_vrs_rank(controller_id, vd, n as nat))
        .leads_to(lift_state(after_scale_down_old_vrs_rank(controller_id, vd, (n - 1) as nat)))),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    VDeploymentView::marshal_preserves_integrity();
    // Error ~> **(n-1)`
    entails_implies_leads_to(spec,
        lift_state(at_step_state_pred(controller_id, vd, VDeploymentReconcileStepView::Error)),
        lift_state(after_scale_down_old_vrs_rank(controller_id, vd, (n - 1) as nat))
    );
    // n ~> **(n-1)
    let pred_n = |s: VDeploymentReconcileState| s.old_vrs_list.len() == n;
    lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
        spec, vd, controller_id, VDeploymentReconcileStepView::AfterScaleDownOldVRS,
        pred_n
    );
    let state_at_n_minus_1 = |s: ReconcileLocalState| {
        let unmarshalled_s = VDeploymentReconcileState::unmarshal(s).unwrap();
        ||| unmarshalled_s.reconcile_step == VDeploymentReconcileStepView::AfterScaleDownOldVRS
            && unmarshalled_s.old_vrs_list.len() == n - 1
        ||| unmarshalled_s.reconcile_step == VDeploymentReconcileStepView::Error
    };
    cluster.lemma_from_some_state_to_arbitrary_next_state(
        spec, controller_id, vd.marshal(),
        at_step_and_closure(VDeploymentReconcileStepView::AfterScaleDownOldVRS, pred_n),
        state_at_n_minus_1
    );
    assume(spec.entails(lift_state(at_step_and_state_pred(controller_id, vd, VDeploymentReconcileStepView::AfterScaleDownOldVRS, pred_n)).leads_to(
        lift_state(after_scale_down_old_vrs_rank(controller_id, vd, (n - 1) as nat))
    )));
    or_leads_to_combine_and_equality!(
        spec, lift_state(after_scale_down_old_vrs_rank(controller_id, vd, n as nat)),
        lift_state(at_step_state_pred(controller_id, vd, VDeploymentReconcileStepView::Error)),
        lift_state(at_step_and_state_pred(controller_id, vd, VDeploymentReconcileStepView::AfterScaleDownOldVRS, pred_n));
        lift_state(after_scale_down_old_vrs_rank(controller_id, vd, (n - 1) as nat))
    );
}
}