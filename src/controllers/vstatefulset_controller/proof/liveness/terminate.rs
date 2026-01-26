use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
    esr::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    trusted::{spec_types::*, step::*, step::VStatefulSetReconcileStepView::*, rely::*},
    proof::{predicate::*, helper_invariants, guarantee, liveness::spec::*},
};
use vstd::prelude::*;

verus! {

pub open spec fn needed_index_and_len(index: nat, len: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.needed_index == index && s.needed.len() == len
}

pub open spec fn condemned_index_and_len(index: nat, len: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.condemned_index == index && s.condemned.len() == len
}

pub open spec fn pvc_and_needed_state(pvc_idx: nat, pvc_len: nat, needed_idx: nat, needed_len: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.pvc_index == pvc_idx && s.pvcs.len() == pvc_len && s.needed_index == needed_idx && s.needed.len() == needed_len
}

pub open spec fn get_pvc_with_needed(vsts: VStatefulSetView, controller_id: int, needed: nat, needed_l: nat) -> TempPred<ClusterState> {
    lift_state(lift_local(controller_id, vsts, at_step_or![(GetPVC, needed_index_and_len(needed, needed_l))]))
}

pub open spec fn create_or_update_or_error_with_needed(vsts: VStatefulSetView, controller_id: int, needed: nat, needed_l: nat) -> TempPred<ClusterState> {
    lift_state(lift_local(controller_id, vsts, at_step_or![(CreateNeeded, needed_index_and_len(needed, needed_l)), (UpdateNeeded, needed_index_and_len(needed, needed_l)), Error]))
}

pub open spec fn vsts_all_states(vsts: VStatefulSetView, controller_id: int) -> TempPred<ClusterState> {
    macro_rules! lift_at_step_or {
        [$($tail:tt)*] => {
            lift_state(lift_local(controller_id, vsts, at_step_or![$($tail)*]))
        }
    }
    lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()) })
    .or(lift_at_step_or![Init])
    .or(lift_at_step_or![AfterListPod])
    .or(lift_at_step_or![GetPVC])
    .or(lift_at_step_or![AfterGetPVC])
    .or(lift_at_step_or![CreatePVC])
    .or(lift_at_step_or![AfterCreatePVC])
    .or(lift_at_step_or![SkipPVC])
    .or(lift_at_step_or![CreateNeeded])
    .or(lift_at_step_or![AfterCreateNeeded])
    .or(lift_at_step_or![UpdateNeeded])
    .or(lift_at_step_or![AfterUpdateNeeded])
    .or(lift_at_step_or![DeleteCondemned])
    .or(lift_at_step_or![AfterDeleteCondemned])
    .or(lift_at_step_or![DeleteOutdated])
    .or(lift_at_step_or![AfterDeleteOutdated])
    .or(lift_at_step_or![Done])
    .or(lift_at_step_or![Error])
}

pub open spec fn vsts_terminate_invariants(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
) -> bool {
    &&& spec.entails(always(lift_action(cluster.next())))
    &&& cluster.type_is_installed_in_cluster::<VStatefulSetView>()
    &&& cluster.controller_models.contains_pair(controller_id, vsts_controller_model())
    &&& spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1))))
    &&& spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i)))
    &&& spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i)))
    &&& spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i))))
    &&& spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i))))
    &&& spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::crash_disabled(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::req_drop_disabled())))
    &&& spec.entails(always(lift_state(Cluster::pod_monkey_disabled())))
    &&& spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id())))
    &&& spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    &&& spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    &&& spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>())))
    &&& spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts.object_ref()))))
    // no sent request at certain steps
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![Init]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreateNeeded]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![UpdateNeeded]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned]))))
    &&& spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated]))))
    // there is always sent request/pending response at certain steps for vsts to transit to next state
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterListPod]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreateNeeded]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterUpdateNeeded]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned]))))
    &&& spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteOutdated]))))
}

pub proof fn reconcile_eventually_terminates_on_vsts_object(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    vsts_terminate_invariants(spec, vsts, cluster, controller_id)
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

    lemma_after_delete_condemned_leads_to_idle(spec, vsts, cluster, controller_id);

    or_leads_to_combine_n!(
        spec,
        lift_at_step_or![AfterDeleteCondemned],
        lift_at_step_or![Error];
        lift_state(reconcile_idle)
    );
    temp_pred_equality(
        lift_at_step_or![AfterDeleteCondemned, Error],
        lift_at_step_or![AfterDeleteCondemned].or(lift_at_step_or![Error])
    );

    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, controller_id, vsts.object_ref(),
        at_step_or![DeleteCondemned],
        at_step_or![AfterDeleteCondemned, Error]
    );

    lemma_get_pvc_leads_to_create_or_update_needed(spec, vsts, cluster, controller_id);

    lemma_after_create_and_update_needed_leads_to_idle(spec, vsts, cluster, controller_id);


    or_leads_to_combine_n!(
        spec,
        lift_at_step_or![AfterCreateNeeded],
        lift_at_step_or![Error];
        lift_state(reconcile_idle)
    );
    temp_pred_equality(
        lift_at_step_or![AfterCreateNeeded, Error],
        lift_at_step_or![AfterCreateNeeded].or(lift_at_step_or![Error])
    );
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, controller_id, vsts.object_ref(),
        at_step_or![CreateNeeded],
        at_step_or![AfterCreateNeeded, Error]
    );

    or_leads_to_combine_n!(
        spec,
        lift_at_step_or![AfterUpdateNeeded],
        lift_at_step_or![Error];
        lift_state(reconcile_idle)
    );
    temp_pred_equality(
        lift_at_step_or![AfterUpdateNeeded, Error],
        lift_at_step_or![AfterUpdateNeeded].or(lift_at_step_or![Error])
    );
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, controller_id, vsts.object_ref(),
        at_step_or![UpdateNeeded],
        at_step_or![AfterUpdateNeeded, Error]
    );

    assert forall |j: nat, jl: nat| #![trigger needed_index_and_len(j, jl)] spec.entails(
        lift_at_step_or![(GetPVC, needed_index_and_len(j, jl))].leads_to(lift_state(reconcile_idle))
    ) by {
        temp_pred_equality(
            get_pvc_with_needed(vsts, controller_id, j, jl),
            lift_at_step_or![(GetPVC, needed_index_and_len(j, jl))]
        );
        temp_pred_equality(
            create_or_update_or_error_with_needed(vsts, controller_id, j, jl),
            lift_at_step_or![(CreateNeeded, needed_index_and_len(j, jl)), (UpdateNeeded, needed_index_and_len(j, jl)), Error]
        );

        entails_implies_leads_to(spec, lift_at_step_or![(CreateNeeded, needed_index_and_len(j, jl))], lift_at_step_or![CreateNeeded]);
        entails_implies_leads_to(spec, lift_at_step_or![(UpdateNeeded, needed_index_and_len(j, jl))], lift_at_step_or![UpdateNeeded]);

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(CreateNeeded, needed_index_and_len(j, jl))],
            lift_at_step_or![CreateNeeded],
            lift_state(reconcile_idle)
        );

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(UpdateNeeded, needed_index_and_len(j, jl))],
            lift_at_step_or![UpdateNeeded],
            lift_state(reconcile_idle)
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(CreateNeeded, needed_index_and_len(j, jl))],
            lift_at_step_or![(UpdateNeeded, needed_index_and_len(j, jl))],
            lift_at_step_or![Error];
            lift_state(reconcile_idle)
        );
        temp_pred_equality(
            lift_at_step_or![(CreateNeeded, needed_index_and_len(j, jl)), (UpdateNeeded, needed_index_and_len(j, jl)), Error],
            lift_at_step_or![(CreateNeeded, needed_index_and_len(j, jl))].or(lift_at_step_or![(UpdateNeeded, needed_index_and_len(j, jl))]).or(lift_at_step_or![Error])
        );

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(GetPVC, needed_index_and_len(j, jl))],
            lift_at_step_or![(CreateNeeded, needed_index_and_len(j, jl)), (UpdateNeeded, needed_index_and_len(j, jl)), Error],
            lift_state(reconcile_idle)
        );
    };

    let get_pvc_with_indices = |j: nat, jl: nat| lift_state(lift_local(controller_id, vsts, at_step_or![(GetPVC, needed_index_and_len(j, jl))]));

    // Inline proof for dropping indices in GetPVC
    let target_idle = lift_state(reconcile_idle);
    let partial_pred_pvc = |i: (nat, nat)| get_pvc_with_indices(i.0, i.1);

    assert forall |i: (nat, nat)| #![trigger partial_pred_pvc(i)] spec.entails(partial_pred_pvc(i).leads_to(target_idle)) by {
        // proved earlier
    }

    leads_to_exists_intro(spec,
        partial_pred_pvc,
        target_idle
    );

    let p_get_pvc = lift_state(lift_local(controller_id, vsts, at_step_or![GetPVC]));
    assert forall |ex: Execution<ClusterState>| #![trigger p_get_pvc.satisfied_by(ex)] p_get_pvc.satisfied_by(ex) implies tla_exists(partial_pred_pvc).satisfied_by(ex) by {
        let vsts_state = VStatefulSetReconcileState::unmarshal(ex.head().ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
        let j_witness = vsts_state.needed_index;
        let jl_witness = vsts_state.needed.len();
        assert(partial_pred_pvc((j_witness, jl_witness)).satisfied_by(ex));
    }

    entails_implies_leads_to(spec, p_get_pvc, tla_exists(partial_pred_pvc));
    leads_to_trans_n!(
        spec,
        p_get_pvc,
        tla_exists(partial_pred_pvc),
        target_idle
    );

    or_leads_to_combine_and_equality!(spec,
        lift_at_step_or![GetPVC, CreateNeeded, UpdateNeeded, Error],
        lift_at_step_or![GetPVC],
        lift_at_step_or![CreateNeeded],
        lift_at_step_or![UpdateNeeded],
        lift_at_step_or![Error];
        lift_state(reconcile_idle)
    );
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, controller_id, vsts.object_ref(),
        at_step_or![SkipPVC],
        at_step_or![GetPVC, CreateNeeded, UpdateNeeded, Error]
    );
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, controller_id, vsts.object_ref(),
        at_step_or![AfterCreatePVC],
        at_step_or![GetPVC, CreateNeeded, UpdateNeeded, Error]
    );

    // Prove CreatePVC leads to idle
    // CreatePVC transitions to AfterCreatePVC | Error
    or_leads_to_combine_n!(
        spec,
        lift_at_step_or![AfterCreatePVC],
        lift_at_step_or![Error];
        lift_state(reconcile_idle)
    );
    temp_pred_equality(
        lift_at_step_or![AfterCreatePVC, Error],
        lift_at_step_or![AfterCreatePVC].or(lift_at_step_or![Error])
    );
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(
        spec, controller_id, vsts.object_ref(),
        at_step_or![CreatePVC],
        at_step_or![AfterCreatePVC, Error]
    );

    // Prove AfterGetPVC leads to idle
    // AfterGetPVC transitions to SkipPVC | CreatePVC | Error
    or_leads_to_combine_n!(
        spec,
        lift_at_step_or![SkipPVC],
        lift_at_step_or![CreatePVC],
        lift_at_step_or![Error];
        lift_state(reconcile_idle)
    );
    temp_pred_equality(
        lift_at_step_or![SkipPVC, CreatePVC, Error],
        lift_at_step_or![SkipPVC].or(lift_at_step_or![CreatePVC]).or(lift_at_step_or![Error])
    );
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(
        spec, controller_id, vsts.object_ref(),
        at_step_or![AfterGetPVC],
        at_step_or![SkipPVC, CreatePVC, Error]
    );

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

    lemma_true_equal_to_reconcile_idle_or_at_any_state(vsts, controller_id);
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

proof fn lemma_get_pvc_leads_to_create_or_update_needed(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    vsts_terminate_invariants(spec, vsts, cluster, controller_id),
ensures
    forall |j: nat, jl: nat| #[trigger] spec.entails(
        get_pvc_with_needed(vsts, controller_id, j, jl)
            .leads_to(create_or_update_or_error_with_needed(vsts, controller_id, j, jl))
    ),
{
    macro_rules! lift_at_step_or {
        [$($tail:tt)*] => {
            lift_state(lift_local(controller_id, vsts, at_step_or![$($tail)*]))
        }
    }

    VStatefulSetReconcileState::marshal_preserves_integrity();

    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref());

    let pvc_with_indices = |i: nat, l: nat, n: nat, ln: nat|
        lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln)), Error];

    assert forall |i: nat, l: nat, n: nat, ln: nat| #![trigger pvc_with_indices(i, l, n, ln)]
        i + 1 < l implies spec.entails(
            pvc_with_indices(i, l, n, ln).leads_to(pvc_with_indices(i + 1 as nat, l, n, ln))
        ) by {
        let i_plus_1 = (i + 1) as nat;

        entails_implies_leads_to(spec, lift_at_step_or![Error], pvc_with_indices(i_plus_1, l, n, ln));

        lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, AfterGetPVC, pvc_and_needed_state(i, l, n, ln)
        );
        cluster.lemma_from_some_state_to_arbitrary_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln))],
            at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln)), (SkipPVC, pvc_and_needed_state(i, l, n, ln)), Error]
        );

        lemma_from_no_pending_req_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, GetPVC, pvc_and_needed_state(i, l, n, ln)
        );
        cluster.lemma_from_no_pending_req_in_flight_at_some_state_to_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
            at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln)), Error]
        );

        entails_implies_leads_to(spec, lift_at_step_or![Error], lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln)), (SkipPVC, pvc_and_needed_state(i, l, n, ln)), Error]);
        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![Error];
            lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln)), (SkipPVC, pvc_and_needed_state(i, l, n, ln)), Error]
        );
        temp_pred_equality(
            lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln)), Error],
            lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
        );
        leads_to_trans_n!(
            spec,
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln)), Error],
            lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln)), (SkipPVC, pvc_and_needed_state(i, l, n, ln)), Error]
        );

        lemma_from_no_pending_req_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, SkipPVC, pvc_and_needed_state(i, l, n, ln)
        );
        cluster.lemma_from_no_pending_req_in_flight_at_some_state_to_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln))],
            at_step_or![(GetPVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]
        );

        lemma_from_no_pending_req_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, CreatePVC, pvc_and_needed_state(i, l, n, ln)
        );
        cluster.lemma_from_no_pending_req_in_flight_at_some_state_to_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln))],
            at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]
        );

        lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln)
        );

        cluster.lemma_from_some_state_to_arbitrary_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln))],
            at_step_or![(GetPVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]
        );

        entails_implies_leads_to(spec, lift_at_step_or![Error], lift_at_step_or![(GetPVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]);
        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln))],
            lift_at_step_or![Error];
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]
        );
        temp_pred_equality(
            lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error],
            lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln))].or(lift_at_step_or![Error])
        );
        leads_to_trans_n!(
            spec,
            lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error],
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln))];
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]
        );
        temp_pred_equality(
            lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln)), (CreatePVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln))])
        );

        entails_implies_leads_to(spec, lift_at_step_or![Error], lift_at_step_or![(GetPVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]);
        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln)), (CreatePVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![Error];
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]
        );
        temp_pred_equality(
            lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln)), (SkipPVC, pvc_and_needed_state(i, l, n, ln)), Error],
            lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln)), (CreatePVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
        );

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln)), (SkipPVC, pvc_and_needed_state(i, l, n, ln)), Error],
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]
        );

        temp_pred_equality(
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error],
            pvc_with_indices(i_plus_1, l, n, ln)
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![Error];
            pvc_with_indices(i_plus_1, l, n, ln)
        );
        temp_pred_equality(
            pvc_with_indices(i, l, n, ln),
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
        );
    };

    assert forall |i: nat, l: nat, n: nat, ln: nat| #![trigger pvc_with_indices(i, l, n, ln)]
        i + 1 == l implies spec.entails(
            pvc_with_indices(i, l, n, ln)
                .leads_to(lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error])
        ) by {
        let i_plus_1 = (i + 1) as nat;

        entails_implies_leads_to(spec, lift_at_step_or![Error], lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]);

        lemma_from_no_pending_req_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, GetPVC, pvc_and_needed_state(i, l, n, ln)
        );
        cluster.lemma_from_no_pending_req_in_flight_at_some_state_to_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
            at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln)), Error]
        );

        lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, AfterGetPVC, pvc_and_needed_state(i, l, n, ln)
        );
        cluster.lemma_from_some_state_to_arbitrary_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln))],
            at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln)), (SkipPVC, pvc_and_needed_state(i, l, n, ln)), Error]
        );

        lemma_from_no_pending_req_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, SkipPVC, pvc_and_needed_state(i, l, n, ln)
        );
        cluster.lemma_from_no_pending_req_in_flight_at_some_state_to_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln))],
            at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
        );

        lemma_from_no_pending_req_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, CreatePVC, pvc_and_needed_state(i, l, n, ln)
        );
        cluster.lemma_from_no_pending_req_in_flight_at_some_state_to_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln))],
            at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]
        );

        lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln)
        );
        cluster.lemma_from_some_state_to_arbitrary_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln))],
            at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
        );

        entails_implies_leads_to(spec, lift_at_step_or![Error], lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]);
        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln))],
            lift_at_step_or![Error];
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
        );
        temp_pred_equality(
            lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error],
            lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln))].or(lift_at_step_or![Error])
        );
        leads_to_trans_n!(
            spec,
            lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error],
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln))];
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
        );
        temp_pred_equality(
            lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln)), (CreatePVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln))])
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln)), (CreatePVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![Error];
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
        );
        temp_pred_equality(
            lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln)), (SkipPVC, pvc_and_needed_state(i, l, n, ln)), Error],
            lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln)), (CreatePVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
        );

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln)), (SkipPVC, pvc_and_needed_state(i, l, n, ln)), Error],
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![Error];
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
        );
        temp_pred_equality(
            lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln)), Error],
            lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
        );

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln)), Error],
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![Error];
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
        );
        temp_pred_equality(
            pvc_with_indices(i, l, n, ln),
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
        );
    };

    assert forall |i: nat, l: nat, n: nat, ln: nat| #![trigger pvc_with_indices(i, l, n, ln)]
        i >= l implies spec.entails(
            pvc_with_indices(i, l, n, ln).leads_to(lift_at_step_or![Error])
        ) by {
        lemma_from_no_pending_req_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, GetPVC, pvc_and_needed_state(i, l, n, ln)
        );
        cluster.lemma_from_no_pending_req_in_flight_at_some_state_to_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
            at_step_or![Error]
        );

        entails_implies_leads_to(spec, lift_at_step_or![Error], lift_at_step_or![Error]);

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![Error],
            lift_at_step_or![Error]
        );

        temp_pred_equality(
            pvc_with_indices(i, l, n, ln),
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
            lift_at_step_or![Error];
            lift_at_step_or![Error]
        );
    };

    assert forall |i: nat, l: nat, n: nat, ln: nat| #![trigger pvc_with_indices(i, l, n, ln)]
        spec.entails(
            pvc_with_indices(i, l, n, ln)
                .leads_to(lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error])
        ) by {
        if i >= l {
            entails_implies_leads_to(spec, lift_at_step_or![Error], lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]);
            leads_to_trans_n!(
                spec,
                pvc_with_indices(i, l, n, ln),
                lift_at_step_or![Error],
                lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
            );
        } else if i + 1 == l {
        } else {
            let target = (l - 1) as nat;
            let p_for_induction = |m: nat, t: nat| pvc_with_indices(m, t + 1 as nat, n, ln);

            assert forall |m: nat, t: nat| #![trigger p_for_induction(m, t)]
                m < t implies spec.entails(
                    p_for_induction(m, t).leads_to(p_for_induction(m + 1 as nat, t))
                ) by {
            };

            leads_to_greater_than_or_eq(spec, p_for_induction);

            temp_pred_equality(p_for_induction(i, target), pvc_with_indices(i, l, n, ln));
            temp_pred_equality(p_for_induction(target, target), pvc_with_indices((l - 1) as nat, l, n, ln));

            leads_to_trans_n!(
                spec,
                pvc_with_indices(i, l, n, ln),
                pvc_with_indices((l - 1) as nat, l, n, ln),
                lift_at_step_or![(CreateNeeded, needed_index_and_len(n, ln)), (UpdateNeeded, needed_index_and_len(n, ln)), Error]
            );
        }
    };

    assert forall |j: nat, jl: nat| #[trigger] spec.entails(
        get_pvc_with_needed(vsts, controller_id, j, jl)
            .leads_to(create_or_update_or_error_with_needed(vsts, controller_id, j, jl))
    ) by {
        let target = lift_at_step_or![(CreateNeeded, needed_index_and_len(j, jl)), (UpdateNeeded, needed_index_and_len(j, jl)), Error];
        let partial_pred = |i: (nat, nat)| pvc_with_indices(i.0, i.1, j, jl);
        assert forall |i: (nat, nat)| #![trigger partial_pred(i)] spec.entails(partial_pred(i).leads_to(target)) by {
            // proved earlier
        }
        leads_to_exists_intro(spec,
            partial_pred,
            target
        );

        let p = get_pvc_with_needed(vsts, controller_id, j, jl);
        assert forall |ex: Execution<ClusterState>| #![trigger p.satisfied_by(ex)] p.satisfied_by(ex) implies tla_exists(partial_pred).satisfied_by(ex) by {
           let vsts_state = VStatefulSetReconcileState::unmarshal(ex.head().ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
           let i_witness = vsts_state.pvc_index;
           let l_witness = vsts_state.pvcs.len();
           assert(partial_pred((i_witness, l_witness)).satisfied_by(ex)); 
        }
        entails_implies_leads_to(spec, p, tla_exists(partial_pred));
        leads_to_trans_n!(
            spec,
            p,
            tla_exists(partial_pred),
            target
        );
    };
}


pub proof fn lemma_after_create_and_update_needed_leads_to_idle(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    vsts_terminate_invariants(spec, vsts, cluster, controller_id),
    forall |j: nat, jl: nat| #![trigger get_pvc_with_needed(vsts, controller_id, j, jl)] spec.entails(
        get_pvc_with_needed(vsts, controller_id, j, jl)
            .leads_to(create_or_update_or_error_with_needed(vsts, controller_id, j, jl))
    ),
    spec.entails(lift_state(lift_local(controller_id, vsts, at_step_or![DeleteCondemned])).leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())))),
    spec.entails(lift_state(lift_local(controller_id, vsts, at_step_or![DeleteOutdated])).leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()))))
ensures
    spec.entails(lift_state(lift_local(controller_id, vsts, at_step_or![AfterCreateNeeded])).leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())))),
    spec.entails(lift_state(lift_local(controller_id, vsts, at_step_or![AfterUpdateNeeded])).leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())))),
{
    macro_rules! lift_at_step_or {
        [$($tail:tt)*] => {
            lift_state(lift_local(controller_id, vsts, at_step_or![$($tail)*]))
        }
    }

    VStatefulSetReconcileState::marshal_preserves_integrity();

    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref());
    let reconcile_error = cluster.reconciler_reconcile_error(controller_id, vsts.object_ref());

    cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, vsts.object_ref());
    temp_pred_equality(lift_at_step_or![Error], lift_state(reconcile_error));

    let after_create_or_update_with_index_and_len = |n: nat, l: nat|
        lift_at_step_or![(AfterCreateNeeded, needed_index_and_len(n, l)), (AfterUpdateNeeded, needed_index_and_len(n, l)), Error];

    assert forall |n: nat, l: nat| #![trigger after_create_or_update_with_index_and_len(n, l)]
        n < l implies spec.entails(after_create_or_update_with_index_and_len(n, l).leads_to(after_create_or_update_with_index_and_len(n + 1 as nat, l))) by {
        let n_plus_1 = n + 1 as nat;

        entails_implies_leads_to(spec, lift_at_step_or![Error], after_create_or_update_with_index_and_len(n_plus_1, l));

        lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, AfterCreateNeeded, needed_index_and_len(n, l)
        );
        cluster.lemma_from_some_state_to_arbitrary_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(AfterCreateNeeded, needed_index_and_len(n, l))],
            at_step_or![(GetPVC, needed_index_and_len(n, l)), (CreateNeeded, needed_index_and_len(n, l)), (UpdateNeeded, needed_index_and_len(n, l)), Error]
        );

        lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, AfterUpdateNeeded, needed_index_and_len(n, l)
        );
        cluster.lemma_from_some_state_to_arbitrary_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(AfterUpdateNeeded, needed_index_and_len(n, l))],
            at_step_or![(GetPVC, needed_index_and_len(n, l)), (CreateNeeded, needed_index_and_len(n, l)), (UpdateNeeded, needed_index_and_len(n, l)), Error]
        );

        assert(spec.entails(
            get_pvc_with_needed(vsts, controller_id, n, l)
                .leads_to(lift_at_step_or![(CreateNeeded, needed_index_and_len(n, l)), (UpdateNeeded, needed_index_and_len(n, l)), Error])
        ));

        lemma_from_no_pending_req_at_step_to_at_step_and_pred(spec, vsts, controller_id, CreateNeeded, needed_index_and_len(n, l));
        cluster.lemma_from_no_pending_req_in_flight_at_some_state_to_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(CreateNeeded, needed_index_and_len(n, l))],
            at_step_or![(AfterCreateNeeded, needed_index_and_len(n_plus_1, l)), Error]
        );

        lemma_from_no_pending_req_at_step_to_at_step_and_pred(spec, vsts, controller_id, UpdateNeeded, needed_index_and_len(n, l));
        cluster.lemma_from_no_pending_req_in_flight_at_some_state_to_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(UpdateNeeded, needed_index_and_len(n, l))],
            at_step_or![(AfterUpdateNeeded, needed_index_and_len(n_plus_1, l)), Error]
        );

        entails_implies_leads_to(spec, lift_at_step_or![(AfterCreateNeeded, needed_index_and_len(n_plus_1, l)), Error], after_create_or_update_with_index_and_len(n_plus_1, l));
        leads_to_trans_n!(
            spec,
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![(AfterCreateNeeded, needed_index_and_len(n_plus_1, l)), Error],
            after_create_or_update_with_index_and_len(n_plus_1, l)
        );

        entails_implies_leads_to(spec, lift_at_step_or![(AfterUpdateNeeded, needed_index_and_len(n_plus_1, l)), Error], after_create_or_update_with_index_and_len(n_plus_1, l));
        leads_to_trans_n!(
            spec,
            lift_at_step_or![(UpdateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![(AfterUpdateNeeded, needed_index_and_len(n_plus_1, l)), Error],
            after_create_or_update_with_index_and_len(n_plus_1, l)
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![(UpdateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![Error];
            after_create_or_update_with_index_and_len(n_plus_1, l)
        );
        temp_pred_equality(
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, l)), (UpdateNeeded, needed_index_and_len(n, l)), Error],
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, l))].or(lift_at_step_or![(UpdateNeeded, needed_index_and_len(n, l))]).or(lift_at_step_or![Error])
        );

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(GetPVC, needed_index_and_len(n, l))],
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, l)), (UpdateNeeded, needed_index_and_len(n, l)), Error],
            after_create_or_update_with_index_and_len(n_plus_1, l)
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(GetPVC, needed_index_and_len(n, l))],
            lift_at_step_or![(CreateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![(UpdateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![Error];
            after_create_or_update_with_index_and_len(n_plus_1, l)
        );
        temp_pred_equality(
            lift_at_step_or![(GetPVC, needed_index_and_len(n, l)), (CreateNeeded, needed_index_and_len(n, l)), (UpdateNeeded, needed_index_and_len(n, l)), Error],
            lift_at_step_or![(GetPVC, needed_index_and_len(n, l))].or(lift_at_step_or![(CreateNeeded, needed_index_and_len(n, l))]).or(lift_at_step_or![(UpdateNeeded, needed_index_and_len(n, l))]).or(lift_at_step_or![Error])
        );

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(AfterCreateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![(GetPVC, needed_index_and_len(n, l)), (CreateNeeded, needed_index_and_len(n, l)), (UpdateNeeded, needed_index_and_len(n, l)), Error],
            after_create_or_update_with_index_and_len(n_plus_1, l)
        );

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(AfterUpdateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![(GetPVC, needed_index_and_len(n, l)), (CreateNeeded, needed_index_and_len(n, l)), (UpdateNeeded, needed_index_and_len(n, l)), Error],
            after_create_or_update_with_index_and_len(n_plus_1, l)
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(AfterCreateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![(AfterUpdateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![Error];
            after_create_or_update_with_index_and_len(n_plus_1, l)
        );
        temp_pred_equality(
            after_create_or_update_with_index_and_len(n, l),
            lift_at_step_or![(AfterCreateNeeded, needed_index_and_len(n, l))].or(lift_at_step_or![(AfterUpdateNeeded, needed_index_and_len(n, l))]).or(lift_at_step_or![Error])
        );
    };

    assert forall |n: nat, l: nat| #![trigger after_create_or_update_with_index_and_len(n, l)]
        n >= l implies spec.entails(after_create_or_update_with_index_and_len(n, l).leads_to(lift_state(reconcile_idle))) by {

        lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, AfterCreateNeeded, needed_index_and_len(n, l)
        );
        cluster.lemma_from_some_state_to_arbitrary_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(AfterCreateNeeded, needed_index_and_len(n, l))],
            at_step_or![DeleteCondemned, DeleteOutdated, Error]
        );

        lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, AfterUpdateNeeded, needed_index_and_len(n, l)
        );
        cluster.lemma_from_some_state_to_arbitrary_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(AfterUpdateNeeded, needed_index_and_len(n, l))],
            at_step_or![DeleteCondemned, DeleteOutdated, Error]
        );

        temp_pred_equality(lift_at_step_or![Error], lift_state(reconcile_error));
        cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, vsts.object_ref());

        or_leads_to_combine_and_equality!(
            spec,
            lift_at_step_or![DeleteCondemned, DeleteOutdated, Error],
            lift_at_step_or![DeleteCondemned],
            lift_at_step_or![DeleteOutdated],
            lift_state(reconcile_error);
            lift_state(reconcile_idle)
        );

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(AfterCreateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![DeleteCondemned, DeleteOutdated, Error],
            lift_state(reconcile_idle)
        );

        leads_to_trans_n!(
            spec,
            lift_at_step_or![(AfterUpdateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![DeleteCondemned, DeleteOutdated, Error],
            lift_state(reconcile_idle)
        );

        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(AfterCreateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![(AfterUpdateNeeded, needed_index_and_len(n, l))],
            lift_at_step_or![Error];
            lift_state(reconcile_idle)
        );
        temp_pred_equality(
            after_create_or_update_with_index_and_len(n, l),
            lift_at_step_or![(AfterCreateNeeded, needed_index_and_len(n, l))].or(lift_at_step_or![(AfterUpdateNeeded, needed_index_and_len(n, l))]).or(lift_at_step_or![Error])
        );
    };

    leads_to_greater_than_or_eq(spec, after_create_or_update_with_index_and_len);

    assert forall |n: nat, l: nat| #![trigger after_create_or_update_with_index_and_len(n, l)]
        spec.entails(after_create_or_update_with_index_and_len(n, l).leads_to(lift_state(reconcile_idle))) by {
        if n >= l {
        } else {
            leads_to_trans_n!(
                spec,
                after_create_or_update_with_index_and_len(n, l),
                after_create_or_update_with_index_and_len(l, l),
                lift_state(reconcile_idle)
            );
        }
    };

    let target = lift_state(reconcile_idle);
    let partial_pred = |i: (nat, nat)| after_create_or_update_with_index_and_len(i.0, i.1);

    assert forall |i: (nat, nat)| #![trigger partial_pred(i)] spec.entails(partial_pred(i).leads_to(target)) by {
        // proved earlier
    }

    leads_to_exists_intro(spec,
        partial_pred,
        target
    );

    let p_create = lift_at_step_or![AfterCreateNeeded];
    assert forall |ex: Execution<ClusterState>| #![trigger p_create.satisfied_by(ex)] p_create.satisfied_by(ex) implies tla_exists(partial_pred).satisfied_by(ex) by {
        let vsts_state = VStatefulSetReconcileState::unmarshal(ex.head().ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
        let n_witness = vsts_state.needed_index;
        let l_witness = vsts_state.needed.len();
        assert(partial_pred((n_witness, l_witness)).satisfied_by(ex));
    }

    entails_implies_leads_to(spec, p_create, tla_exists(partial_pred));
    leads_to_trans_n!(
        spec,
        p_create,
        tla_exists(partial_pred),
        target
    );

    let p_update = lift_at_step_or![AfterUpdateNeeded];
    assert forall |ex: Execution<ClusterState>| #![trigger p_update.satisfied_by(ex)] p_update.satisfied_by(ex) implies tla_exists(partial_pred).satisfied_by(ex) by {
        let vsts_state = VStatefulSetReconcileState::unmarshal(ex.head().ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
        let n_witness = vsts_state.needed_index;
        let l_witness = vsts_state.needed.len();
        assert(partial_pred((n_witness, l_witness)).satisfied_by(ex));
    }

    entails_implies_leads_to(spec, p_update, tla_exists(partial_pred));
    leads_to_trans_n!(
        spec,
        p_update,
        tla_exists(partial_pred),
        target
    );
}

pub proof fn lemma_after_delete_condemned_leads_to_idle(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    vsts_terminate_invariants(spec, vsts, cluster, controller_id),
    spec.entails(lift_state(lift_local(controller_id, vsts, at_step_or![DeleteOutdated])).leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()))))
ensures
    spec.entails(lift_state(lift_local(controller_id, vsts, at_step_or![AfterDeleteCondemned])).leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())))),
{
    macro_rules! lift_at_step_or {
        [$($tail:tt)*] => {
            lift_state(lift_local(controller_id, vsts, at_step_or![$($tail)*]))
        }
    }
    VStatefulSetReconcileState::marshal_preserves_integrity();

    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref());
    let reconcile_error = cluster.reconciler_reconcile_error(controller_id, vsts.object_ref());

    let delete_condemned_with_index_and_len = |n: nat, l: nat| lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l)), Error, DeleteOutdated];

    assert forall |n: nat, l: nat| #![trigger delete_condemned_with_index_and_len(n, l)]
        n < l implies spec.entails(delete_condemned_with_index_and_len(n, l).leads_to(delete_condemned_with_index_and_len(n + 1 as nat, l))) by {
        let n_plus_1 = n + 1 as nat;
        entails_implies_leads_to(spec, lift_at_step_or![Error], delete_condemned_with_index_and_len(n_plus_1, l));
        entails_implies_leads_to(spec, lift_at_step_or![DeleteOutdated], delete_condemned_with_index_and_len(n_plus_1, l));

        lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, AfterDeleteCondemned, condemned_index_and_len(n, l)
        );
        cluster.lemma_from_some_state_to_arbitrary_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))],
            at_step_or![(DeleteCondemned, condemned_index_and_len(n, l)), Error, DeleteOutdated]
        );

        lemma_from_no_pending_req_at_step_to_at_step_and_pred(spec, vsts, controller_id, DeleteCondemned, condemned_index_and_len(n, l));
        cluster.lemma_from_no_pending_req_in_flight_at_some_state_to_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(DeleteCondemned, condemned_index_and_len(n, l))],
            at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n_plus_1, l)), Error]
        );
        entails_implies_leads_to(spec, lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n_plus_1, l)), Error], delete_condemned_with_index_and_len(n_plus_1, l));
        leads_to_trans_n!(
            spec,
            lift_at_step_or![(DeleteCondemned, condemned_index_and_len(n, l))],
            lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n_plus_1, l)), Error],
            delete_condemned_with_index_and_len(n_plus_1, l)
        );
        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(DeleteCondemned, condemned_index_and_len(n, l))],
            lift_at_step_or![Error],
            lift_at_step_or![DeleteOutdated];
            delete_condemned_with_index_and_len(n_plus_1, l)
        );
        temp_pred_equality(
            lift_at_step_or![(DeleteCondemned, condemned_index_and_len(n, l)), Error, DeleteOutdated],
            lift_at_step_or![(DeleteCondemned, condemned_index_and_len(n, l))].or(lift_at_step_or![Error]).or(lift_at_step_or![DeleteOutdated])
        );
        leads_to_trans_n!(
            spec,
            lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))],
            lift_at_step_or![(DeleteCondemned, condemned_index_and_len(n, l)), Error, DeleteOutdated],
            delete_condemned_with_index_and_len(n_plus_1, l)
        );
        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))],
            lift_at_step_or![Error],
            lift_at_step_or![DeleteOutdated];
            delete_condemned_with_index_and_len(n_plus_1, l)
        );
        temp_pred_equality(
            delete_condemned_with_index_and_len(n, l),
            lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))].or(lift_at_step_or![Error]).or(lift_at_step_or![DeleteOutdated])
        );
    };

    assert forall |n: nat, l: nat| #![trigger delete_condemned_with_index_and_len(n, l)]
        n >= l implies spec.entails(delete_condemned_with_index_and_len(n, l).leads_to(lift_state(reconcile_idle))) by {
        lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, AfterDeleteCondemned, condemned_index_and_len(n, l)
        );
        cluster.lemma_from_some_state_to_arbitrary_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))],
            at_step_or![Error, DeleteOutdated]
        );
        temp_pred_equality(lift_at_step_or![Error], lift_state(reconcile_error));

        cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, vsts.object_ref());

        or_leads_to_combine_and_equality!(
            spec,
            lift_at_step_or![Error, DeleteOutdated],
            lift_state(reconcile_error),
            lift_at_step_or![DeleteOutdated];
            lift_state(reconcile_idle)
        );
        leads_to_trans_n!(
            spec,
            lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))],
            lift_at_step_or![Error, DeleteOutdated],
            lift_state(reconcile_idle)
        );
        or_leads_to_combine_n!(
            spec,
            lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))],
            lift_at_step_or![Error],
            lift_at_step_or![DeleteOutdated];
            lift_state(reconcile_idle)
        );
        temp_pred_equality(
            delete_condemned_with_index_and_len(n, l),
            lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))].or(lift_at_step_or![Error]).or(lift_at_step_or![DeleteOutdated])
        );
    };

    leads_to_greater_than_or_eq(spec, delete_condemned_with_index_and_len);

    assert forall |n: nat, l: nat| #![trigger delete_condemned_with_index_and_len(n, l)]
        spec.entails(delete_condemned_with_index_and_len(n, l).leads_to(lift_state(reconcile_idle))) by {
        if n >= l {
        } else {
            leads_to_trans_n!(
                spec,
                delete_condemned_with_index_and_len(n, l),
                delete_condemned_with_index_and_len(l, l),
                lift_state(reconcile_idle)
            );
        }
    };

    let target = lift_state(reconcile_idle);
    let partial_pred = |i: (nat, nat)| delete_condemned_with_index_and_len(i.0, i.1);

    assert forall |i: (nat, nat)| #![trigger partial_pred(i)] spec.entails(partial_pred(i).leads_to(target)) by {
        // proved earlier
    }

    leads_to_exists_intro(spec,
        partial_pred,
        target
    );

    let p = lift_at_step_or![AfterDeleteCondemned];
    assert forall |ex: Execution<ClusterState>| #![trigger p.satisfied_by(ex)] p.satisfied_by(ex) implies tla_exists(partial_pred).satisfied_by(ex) by {
        let vsts_state = VStatefulSetReconcileState::unmarshal(ex.head().ongoing_reconciles(controller_id)[vsts.object_ref()].local_state).unwrap();
        let n_witness = vsts_state.condemned_index;
        let l_witness = vsts_state.condemned.len();
        assert(partial_pred((n_witness, l_witness)).satisfied_by(ex));
    }

    entails_implies_leads_to(spec, p, tla_exists(partial_pred));
    leads_to_trans_n!(
        spec,
        p,
        tla_exists(partial_pred),
        target
    );
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
    entails_preserved_by_always(pre, post);
    entails_trans(spec, always(pre), always(post));
}

pub proof fn lemma_from_no_pending_req_at_step_to_at_step_and_pred(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, controller_id: int,
    step: VStatefulSetReconcileStepView, pred: spec_fn(VStatefulSetReconcileState) -> bool
)
requires
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, vsts.object_ref(), at_step_or![step]
    )))),
ensures
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, vsts.object_ref(), at_step_or![(step, pred)]
    )))),
{
    let pre = lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, vsts.object_ref(), at_step_or![step]
    ));
    let post = lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id, vsts.object_ref(), at_step_or![(step, pred)]
    ));
    entails_preserved_by_always(pre, post);
    entails_trans(spec, always(pre), always(post));
}

proof fn lemma_true_equal_to_reconcile_idle_or_at_any_state(vsts: VStatefulSetView, controller_id: int)
    ensures true_pred::<ClusterState>() == vsts_all_states(vsts, controller_id)

{
    assert(forall |ex| #[trigger] true_pred::<ClusterState>().satisfied_by(ex) ==> vsts_all_states(vsts, controller_id).satisfied_by(ex));
    temp_pred_equality(true_pred::<ClusterState>(), vsts_all_states(vsts, controller_id));
}

}