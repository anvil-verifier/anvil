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
// make encoding steps easier
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use vstd::prelude::*;

verus! {

pub open spec fn old_vrs_list_len(n: nat) -> spec_fn(VDeploymentReconcileState) -> bool {
    |vds: VDeploymentReconcileState| vds.old_vrs_list.len() == n
}

// these 2 spec exists because of the limitation on trigger:
// error: trigger must be a function call, a field access, or arithmetic operator
pub open spec fn after_old_vrs_rank(controller_id: int, vd: VDeploymentView, n: nat) -> TempPred<ClusterState> {
    temp_at_step!(controller_id, vd, (AfterScaleDownOldVRS, old_vrs_list_len(n)), Error)
}
pub open spec fn after_old_vrs(controller_id: int, vd: VDeploymentView) -> TempPred<ClusterState> {
    temp_at_step!(controller_id, vd, AfterScaleDownOldVRS, Error)
}

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
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vd.object_ref(), at_step!(Init))))),
    // there is always pending request for vd to proceed
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step!(AfterCreateNewVRS))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step!(AfterScaleNewVRS))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vd.object_ref(), at_step!(AfterScaleDownOldVRS))))),
    spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())))),
{
    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref());
    let reconcile_done = cluster.reconciler_reconcile_done(controller_id, vd.object_ref());
    let reconcile_error = cluster.reconciler_reconcile_error(controller_id, vd.object_ref());
    // 1, prove that reconcile_done \/ reconcile_error \/ reconcile_ide ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, vd.object_ref());
    cluster.lemma_reconcile_done_leads_to_reconcile_idle(spec, controller_id, vd.object_ref());
    // TODO: can we omit this?
    temp_pred_equality(
        temp_at_step!(controller_id, vd, Done),
        lift_state(reconcile_done)
    );
    temp_pred_equality(
        temp_at_step!(controller_id, vd, Error),
        lift_state(reconcile_error)
    );
    entails_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));
    // 2, AfterScaleDownOldVRS ~> reconcile_idle.
    // 2.1, AfterScaleDownOldVRS && state.old_vrs_list.len() == 0 ~> reconcile_idle.
    // Done ~> idle && Error ~> idle => Done \/ Error ~> idle
    or_leads_to_combine_and_equality!(
        spec, temp_at_step!(controller_id, vd, Done, Error),
        lift_state(reconcile_done),
        lift_state(reconcile_error);
        lift_state(reconcile_idle)
    );
    // AfterScaleDownOldVRS && state.old_vrs_list.len() == 0 ~> Done \/ Error ~> idle
    let empty_old_vrs_list_pred = |s: VDeploymentReconcileState| s.old_vrs_list.len() == 0;
    let current_state = at_step!((AfterScaleDownOldVRS, empty_old_vrs_list_pred));
    lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
        spec, vd, controller_id, AfterScaleDownOldVRS, empty_old_vrs_list_pred);
    // Next state leads to idle.
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, vd.marshal(), current_state, |s: ReconcileLocalState| (at_step!(Done, Error))(s));
    // 2.2, AfterScaleDownOldVRS && state.old_vrs_list.len() == n ~> idle
    assert forall |n: nat| #![trigger after_old_vrs_rank(controller_id, vd, n)]
        spec.entails(after_old_vrs_rank(controller_id, vd, n)
        .leads_to(after_old_vrs_rank(controller_id, vd, 0))) by {
        // n | Error ~> n-1 | Error
            assert forall |n: nat| #![trigger after_old_vrs_rank(controller_id, vd, n)]
                n > 0 implies
                spec.entails(after_old_vrs_rank(controller_id, vd, n) .leads_to(after_old_vrs_rank(controller_id, vd, (n - 1) as nat))) by {
            lemma_from_old_vrs_of_n_to_old_vrs_of_n_minus_1(spec, vd, cluster, controller_id, n);
        }
        // n ~> n-1 ~> 0
        leads_to_rank_step_one(spec, |n| after_old_vrs_rank(controller_id, vd, n));
        // n ~> n | Error
        always_implies_to_leads_to(
            spec,
            temp_at_step!(controller_id, vd, (AfterScaleDownOldVRS, old_vrs_list_len(n))),
            after_old_vrs_rank(controller_id, vd, n));
        // n | Error ~> 0 | Error
        // TODO: investigate why we need |n|f(n) instead of f, could be a bug in verus
        assert(spec.entails((|n| after_old_vrs_rank(controller_id, vd, n))(n)
                                .leads_to((|n| after_old_vrs_rank(controller_id, vd, n))(nat0!()))));
        // (n | Error() ~> (0 | Error) ~> reconcile_idle
        leads_to_trans_n!(spec, after_old_vrs_rank(controller_id, vd, n), after_old_vrs_rank(controller_id, vd, 0), lift_state(reconcile_idle));
    }
    // (AfterScaleDownOldVRS(n) | Error) == (AfterScaleDownOldVRS | Error)
    assert(after_old_vrs(controller_id, vd).entails(tla_exists(|n| after_old_vrs_rank(controller_id, vd, n)))) by {
        assert forall |ex: Execution<ClusterState>| #[trigger] after_old_vrs(controller_id, vd).satisfied_by(ex) implies exists |n: nat| after_old_vrs_rank(controller_id, vd, n).satisfied_by(ex) by {
            let n = choose |n: nat| after_old_vrs_rank(controller_id, vd, n).satisfied_by(ex);
        }
    }
    temp_pred_equality(tla_exists(|n| after_old_vrs_rank(controller_id, vd, n)), after_old_vrs(controller_id, vd));
    // (AfterScaleDownOldVRS | Error) ~> reconcile_idle
    leads_to_trans_n!(spec, after_old_vrs(controller_id, vd), after_old_vrs_rank(controller_id, vd, 0), lift_state(reconcile_idle));
    // 2.3, AfterScaleNewVRS ~> reconcile_idle.
    // AfterScaleNewVRS ~> AfterScaleDownOldVRS | Done | Error
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
            at_step_spec(step)
        )))),
ensures
    spec.entails(always(
        lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id,
            vd.object_ref(),
            at_step_pred_spec(step, pred)
        )))),
{
    let pre = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id,
        vd.object_ref(),
        at_step_spec(step)
    ));
    let post = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id,
        vd.object_ref(),
        at_step_pred_spec(step, pred)
    ));
    assert forall |ex| #![auto] spec.satisfied_by(ex) && spec.entails(always(pre)) implies always(post).satisfied_by(ex) by {
        assert(forall |ex| #[trigger] spec.implies(always(pre)).satisfied_by(ex));
        assert(forall |ex| spec.implies(always(pre)).satisfied_by(ex) <==> (spec.satisfied_by(ex) ==> #[trigger] always(pre).satisfied_by(ex)));
        assert(always(pre).satisfied_by(ex));

        assert forall |i: nat| #![auto] pre.satisfied_by(ex.suffix(i)) implies post.satisfied_by(ex.suffix(i)) by {
        }
    }
}

// what is satisfied at step should also be satisfied at step and pred
pub proof fn lemma_all_step_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
    spec: TempPred<ClusterState>, vd: VDeploymentView, controller_id: int
)
// tricky workaround for error: triggers cannot contain let/forall/exists/lambda/choose
ensures forall |step: VDeploymentReconcileStepView, pred: spec_fn(VDeploymentReconcileState) -> bool| #![trigger at_step_pred_spec(step, pred)]
    spec.entails(always(
        lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, vd.object_ref(), at_step_spec(step)
    ))))
    ==>
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, vd.object_ref(), at_step_pred_spec(step, pred)
    )))),
{
    assert forall |step: VDeploymentReconcileStepView, pred: spec_fn(VDeploymentReconcileState) -> bool| #![trigger at_step_pred_spec(step, pred)]
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id, vd.object_ref(), at_step_spec(step)
        ))))
        implies
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id, vd.object_ref(), at_step_pred_spec(step, pred)
        )))) by {
        let pre = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id, vd.object_ref(), at_step_spec(step)
        ));
        let post = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
            controller_id, vd.object_ref(), at_step_pred_spec(step, pred)
        ));
        assert forall |ex| #![auto] spec.satisfied_by(ex) && spec.entails(always(pre)) implies always(post).satisfied_by(ex) by {
            assert(forall |ex| #[trigger] spec.implies(always(pre)).satisfied_by(ex));
            assert(forall |ex| spec.implies(always(pre)).satisfied_by(ex) <==> (spec.satisfied_by(ex) ==> #[trigger] always(pre).satisfied_by(ex)));
            assert(always(pre).satisfied_by(ex));
            assert forall |i: nat| #![auto] pre.satisfied_by(ex.suffix(i)) implies post.satisfied_by(ex.suffix(i)) by {}
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
            at_step!(AfterScaleDownOldVRS)
        )))),
ensures
    spec.entails(after_old_vrs_rank(controller_id, vd, n)
        .leads_to(after_old_vrs_rank(controller_id, vd, (n - 1) as nat))),
{
    VDeploymentReconcileState::marshal_preserves_integrity();
    VDeploymentView::marshal_preserves_integrity();
    // Error ~> **(n-1)`
    entails_implies_leads_to(spec,
        temp_at_step!(controller_id, vd, Error),
        after_old_vrs_rank(controller_id, vd, (n - 1) as nat)
    );
    // n ~> **(n-1)
    lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
        spec, vd, controller_id, AfterScaleDownOldVRS,
        old_vrs_list_len(n)
    );
    cluster.lemma_from_some_state_to_arbitrary_next_state(
        spec, controller_id, vd.marshal(),
        at_step!((AfterScaleDownOldVRS, old_vrs_list_len(n))),
        at_step!((AfterScaleDownOldVRS, old_vrs_list_len(n - nat1!())), Error),
    );
    assume(spec.entails(temp_at_step!(controller_id, vd, (AfterScaleDownOldVRS, old_vrs_list_len(n))).leads_to(
        after_old_vrs_rank(controller_id, vd, (n - 1) as nat)
    )));
    or_leads_to_combine_and_equality!(
        spec,
        temp_at_step!(controller_id, vd, Error),
        after_old_vrs_rank(controller_id, vd, n),
        temp_at_step!(controller_id, vd, (AfterScaleDownOldVRS, old_vrs_list_len(n)));
        after_old_vrs_rank(controller_id, vd, (n - 1) as nat)
    );
}
}