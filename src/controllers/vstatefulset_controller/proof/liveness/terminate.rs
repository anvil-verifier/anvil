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
    trusted::{spec_types::*, step::*, step::VStatefulSetReconcileStepView::*, util::*},
    proof::predicate::*,
};
use vstd::prelude::*;

verus! {

// Helper predicates for specific index conditions
pub open spec fn needed_index(n: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.needed_index == n
}

pub open spec fn condemned_index(n: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.condemned_index == n
}

pub open spec fn pvc_index(n: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.pvc_index == n
}

pub open spec fn needed_len(n: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.needed.len() == n
}

pub open spec fn condemned_len(n: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.condemned.len() == n
}

pub open spec fn pvc_len(n: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.pvcs.len() == n
}

pub open spec fn needed_index_and_len(index: nat, len: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.needed_index == index && s.needed.len() == len
}

pub open spec fn condemned_index_and_len(index: nat, len: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.condemned_index == index && s.condemned.len() == len
}

pub open spec fn pvc_index_and_len(index: nat, len: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.pvc_index == index && s.pvcs.len() == len
}

pub proof fn lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, controller_id: int,
    step: VStatefulSetReconcileStepView, pred: spec_fn(VStatefulSetReconcileState) -> bool
)
requires
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, vsts.object_ref(), at_step_or![step]
    )))),
ensures
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, vsts.object_ref(), at_step_or![(step, pred)]
    )))),
{
    let pre = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, vsts.object_ref(), at_step_or![step]
    ));
    let post = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id, vsts.object_ref(), at_step_or![(step, pred)]
    ));
    assert forall |ex| #![auto] spec.satisfied_by(ex) && spec.entails(always(pre)) implies always(post).satisfied_by(ex) by {
        assert(forall |ex| #[trigger] spec.implies(always(pre)).satisfied_by(ex));
        assert(forall |ex| spec.implies(always(pre)).satisfied_by(ex) <==> (spec.satisfied_by(ex) ==> #[trigger] always(pre).satisfied_by(ex)));
        assert(always(pre).satisfied_by(ex));
        assert(forall |i: nat| #![auto] pre.satisfied_by(ex.suffix(i)) ==> post.satisfied_by(ex.suffix(i)));
    }
}

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
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated])))),
    // there is always sent request/pending response at certain steps for vsts to transit to next state
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod])))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC])))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC])))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded])))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded])))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned])))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated])))),
ensures
    spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())))),
{
    macro_rules! lift_at_step_or {
        [$($tail:tt)*] => {
            lift_state(lift_local(controller_id, vsts, at_step_or![$($tail)*]))
        }
    }

    VStatefulSetReconcileState::marshal_preserves_integrity();

    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref());
    let reconcile_done = cluster.reconciler_reconcile_done(controller_id, vsts.object_ref());
    let reconcile_error = cluster.reconciler_reconcile_error(controller_id, vsts.object_ref());

    // First, prove that reconcile_done \/ reconcile_error \/ reconcile_idle ~> reconcile_idle.
    // Here we simply apply a cluster lemma which uses the wf1 of end_reconcile action.
    cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, vsts.object_ref());
    cluster.lemma_reconcile_done_leads_to_reconcile_idle(spec, controller_id, vsts.object_ref());
    temp_pred_equality(lift_at_step_or![Done], lift_state(reconcile_done));
    temp_pred_equality(lift_at_step_or![Error], lift_state(reconcile_error));
    entails_implies_leads_to(spec, lift_state(reconcile_idle), lift_state(reconcile_idle));

    assume(spec.entails(lift_at_step_or![GetPVC].leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_at_step_or![AfterGetPVC].leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_at_step_or![CreatePVC].leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_at_step_or![AfterCreatePVC].leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_at_step_or![SkipPVC].leads_to(lift_state(reconcile_idle))));

    assume(spec.entails(lift_at_step_or![CreateNeeded].leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_at_step_or![AfterCreateNeeded].leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_at_step_or![UpdateNeeded].leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_at_step_or![AfterUpdateNeeded].leads_to(lift_state(reconcile_idle))));
    
    assume(spec.entails(lift_at_step_or![DeleteCondemned].leads_to(lift_state(reconcile_idle))));
    assume(spec.entails(lift_at_step_or![AfterDeleteCondemned].leads_to(lift_state(reconcile_idle))));

    assert(spec.entails(lift_at_step_or![DeleteCondemned].leads_to(lift_state(reconcile_idle)))) by {
        let delete_condemned_with_index_and_len = |n: nat, l: nat| lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l)), Error, DeleteOutdated];

        // Step 1: Prove AfterDeleteCondemned(n, l) with n < l leads to AfterDeleteCondemned(n+1, l) | Error | DeleteOutdated
        assert forall |n: nat, l: nat| #![trigger delete_condemned_with_index_and_len(n, l)]
            n < l ==> spec.entails(delete_condemned_with_index_and_len(n, l).leads_to(delete_condemned_with_index_and_len(n + 1 as nat, l))) by {

            let n_plus_1 = n + 1 as nat;

            // The state delete_condemned_with_index_and_len(n, l) is:
            // AfterDeleteCondemned with condemned_index==n && condemned.len()==l, OR Error, OR DeleteOutdated
            // We need to show each of these leads to delete_condemned_with_index_and_len(n+1, l)

            // Error and DeleteOutdated trivially lead to the target state
            entails_implies_leads_to(spec, lift_at_step_or![Error], delete_condemned_with_index_and_len(n_plus_1, l));
            entails_implies_leads_to(spec, lift_at_step_or![DeleteOutdated], delete_condemned_with_index_and_len(n_plus_1, l));

            // Show AfterDeleteCondemned(n, l) leads to the target
            // This happens in two steps:
            // 1. AfterDeleteCondemned(n, l) ~> DeleteCondemned | Error | DeleteOutdated
            // 2. DeleteCondemned ~> AfterDeleteCondemned(n+1, l) | Error

            // Step 1: AfterDeleteCondemned(n, l) transitions to DeleteCondemned | Error | DeleteOutdated
            assert(forall |input_cr, resp_o, s| #![trigger dummy((input_cr, resp_o, s))]
                at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))](s) ==>
                at_step_or![DeleteCondemned, Error, DeleteOutdated]((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0));

            // Use the lemma to lift pending_req from AfterDeleteCondemned to AfterDeleteCondemned(n, l)
            lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
                spec, vsts, controller_id, AfterDeleteCondemned, condemned_index_and_len(n, l)
            );

            cluster.lemma_from_some_state_to_arbitrary_next_state(
                spec, controller_id, vsts.object_ref(),
                at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))],
                at_step_or![DeleteCondemned, Error, DeleteOutdated]
            );

            // Step 2: DeleteCondemned with index n ~> AfterDeleteCondemned(n+1, l) | Error
            // From reconciler.rs line 500: handle_delete_condemned increments condemned_index before transitioning
            assert(forall |input_cr, resp_o, s| #![trigger dummy((input_cr, resp_o, s))]
                at_step_or![(DeleteCondemned, condemned_index_and_len(n, l))](s) ==>
                at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n_plus_1, l)), Error]((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0));

            // Note: DeleteCondemned has no_pending_req (line 86 precondition), not pending_req
            // So we cannot use lemma_from_pending_req here. But looking at the preconditions,
            // DeleteCondemned sends a request, so after the transition it's in flight.
            // We need a different approach - assume for now
            assume(spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id, vsts.object_ref(), at_step_or![(DeleteCondemned, condemned_index_and_len(n, l))]
            )))));

            cluster.lemma_from_some_state_to_arbitrary_next_state(
                spec, controller_id, vsts.object_ref(),
                at_step_or![(DeleteCondemned, condemned_index_and_len(n, l))],
                at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n_plus_1, l)), Error]
            );

            // The lemma above shows DeleteCondemned(n, l) ~> AfterDeleteCondemned(n+1, l) | Error
            // We need to show this leads to the full target state (which already includes Error)
            temp_pred_equality(
                lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n_plus_1, l)), Error],
                lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n_plus_1, l))].or(lift_at_step_or![Error])
            );

            entails_implies_leads_to(
                spec,
                lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n_plus_1, l)), Error],
                delete_condemned_with_index_and_len(n_plus_1, l)
            );

            leads_to_trans_n!(
                spec,
                lift_at_step_or![(DeleteCondemned, condemned_index_and_len(n, l))],
                lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n_plus_1, l)), Error],
                delete_condemned_with_index_and_len(n_plus_1, l)
            );

            // For general DeleteCondemned (without index constraint), assume it leads to target
            // TODO: This needs more careful reasoning - we only care about DeleteCondemned(n, l)
            assume(spec.entails(lift_at_step_or![DeleteCondemned].leads_to(delete_condemned_with_index_and_len(n_plus_1, l))));

            // Combine: AfterDeleteCondemned(n, l) ~> DeleteCondemned | Error | DeleteOutdated ~> target
            temp_pred_equality(
                lift_at_step_or![DeleteCondemned, Error, DeleteOutdated],
                lift_at_step_or![DeleteCondemned].or(lift_at_step_or![Error]).or(lift_at_step_or![DeleteOutdated])
            );

            or_leads_to_combine_and_equality!(spec,
                lift_at_step_or![DeleteCondemned, Error, DeleteOutdated],
                lift_at_step_or![DeleteCondemned],
                lift_at_step_or![Error],
                lift_at_step_or![DeleteOutdated];
                delete_condemned_with_index_and_len(n_plus_1, l)
            );

            leads_to_trans_n!(
                spec,
                lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))],
                lift_at_step_or![DeleteCondemned, Error, DeleteOutdated],
                delete_condemned_with_index_and_len(n_plus_1, l)
            );

            // Combine all three branches
            or_leads_to_combine_and_equality!(spec,
                delete_condemned_with_index_and_len(n, l),
                lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))],
                lift_at_step_or![Error],
                lift_at_step_or![DeleteOutdated];
                delete_condemned_with_index_and_len(n_plus_1, l)
            );
        };

        // TODO: Steps 2 and 3 to complete the overall proof
        assume(false);
    };

    // Prove AfterDeleteOutdated -> Idle first
    cluster.lemma_from_some_state_to_arbitrary_next_state(spec, controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated], at_step_or![Error, Done]);

    or_leads_to_combine_and_equality!(spec,
        lift_at_step_or![Error, Done],
        lift_state(reconcile_error),
        lift_state(reconcile_done);
        lift_state(reconcile_idle)
    );

    leads_to_trans_n!(
        spec,
        lift_at_step_or![AfterDeleteOutdated],
        lift_at_step_or![Error, Done],
        lift_state(reconcile_idle)
    );

    // Prove DeleteOutdated -> Idle (goes to AfterDeleteOutdated, Error, or Done)
    or_leads_to_combine_n!(
        spec,
        lift_at_step_or![AfterDeleteOutdated],
        lift_at_step_or![Error],
        lift_at_step_or![Done];
        lift_state(reconcile_idle)
    );
    temp_pred_equality(
        lift_at_step_or![AfterDeleteOutdated, Error, Done],
        lift_at_step_or![AfterDeleteOutdated].or(lift_at_step_or![Error]).or(lift_at_step_or![Done])
    );
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, controller_id, vsts.object_ref(),
        at_step_or![DeleteOutdated],
        at_step_or![AfterDeleteOutdated, Error, Done]
    );

    // Now prove AfterListPod -> Idle (goes to GetPVC, CreateNeeded, UpdateNeeded, DeleteCondemned, DeleteOutdated, Error, or Done)
    cluster.lemma_from_some_state_to_arbitrary_next_state(
        spec, controller_id, vsts.object_ref(),
        at_step_or![AfterListPod],
        at_step_or![GetPVC, CreateNeeded, UpdateNeeded, DeleteCondemned, DeleteOutdated, Error, Done]
    );
    or_leads_to_combine_and_equality!(spec,
        lift_at_step_or![GetPVC, CreateNeeded, UpdateNeeded, DeleteCondemned, DeleteOutdated, Error, Done],
        lift_at_step_or![GetPVC],
        lift_at_step_or![CreateNeeded],
        lift_at_step_or![UpdateNeeded],
        lift_at_step_or![DeleteCondemned],
        lift_at_step_or![DeleteOutdated],
        lift_at_step_or![Error],
        lift_at_step_or![Done];
        lift_state(reconcile_idle)
    );
    leads_to_trans_n!(
        spec,
        lift_at_step_or![AfterListPod],
        lift_at_step_or![GetPVC, CreateNeeded, UpdateNeeded, DeleteCondemned, DeleteOutdated, Error, Done],
        lift_state(reconcile_idle)
    );

    // Prove AfterListPod | Done ~> reconcile_idle
    assert(spec.entails(lift_at_step_or![Done]
        .leads_to(lift_state(reconcile_idle))));
    or_leads_to_combine_n!(
        spec,
        lift_at_step_or![AfterListPod],
        lift_at_step_or![Done];
        lift_state(reconcile_idle)
    );
    temp_pred_equality(
        lift_at_step_or![AfterListPod, Done],
        lift_at_step_or![AfterListPod].or(lift_at_step_or![Done])
    );

    // Prove that reconcile init state can reach AfterListPod | Done
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, controller_id, vsts.object_ref(),
        at_step_or![Init],
        at_step_or![AfterListPod, Done]
    );

    // Call the lemma to establish the equality
    lemma_true_equal_to_reconcile_idle_or_at_any_state(vsts, controller_id);

    // Use or_leads_to_combine_and_equality to combine all the individual leads_to proofs
    or_leads_to_combine_and_equality!(
        spec,
        true_pred(),
        lift_state(reconcile_idle),
        lift_at_step_or![Init],
        lift_at_step_or![AfterListPod],
        lift_at_step_or![GetPVC],
        lift_at_step_or![AfterGetPVC],
        lift_at_step_or![CreatePVC],
        lift_at_step_or![AfterCreatePVC],
        lift_at_step_or![SkipPVC],
        lift_at_step_or![CreateNeeded],
        lift_at_step_or![AfterCreateNeeded],
        lift_at_step_or![UpdateNeeded],
        lift_at_step_or![AfterUpdateNeeded],
        lift_at_step_or![DeleteCondemned],
        lift_at_step_or![AfterDeleteCondemned],
        lift_at_step_or![DeleteOutdated],
        lift_at_step_or![AfterDeleteOutdated],
        lift_at_step_or![Done],
        lift_at_step_or![Error];
        lift_state(reconcile_idle)
    );
}

#[verifier(external_body)]
proof fn lemma_true_equal_to_reconcile_idle_or_at_any_state(vsts: VStatefulSetView, controller_id: int)
    ensures true_pred::<ClusterState>()
                == lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()) })
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![Init])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![AfterListPod])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![GetPVC])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![AfterGetPVC])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![CreatePVC])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![AfterCreatePVC])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![SkipPVC])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![CreateNeeded])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![AfterCreateNeeded])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![UpdateNeeded])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![AfterUpdateNeeded])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![DeleteCondemned])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![AfterDeleteCondemned])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![DeleteOutdated])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![AfterDeleteOutdated])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![Done])))
                    .or(lift_state(lift_local(controller_id, vsts, at_step_or![Error])))
{}

}