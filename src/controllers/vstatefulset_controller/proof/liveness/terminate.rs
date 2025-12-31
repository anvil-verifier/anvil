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

pub open spec fn pvc_index_len_and_needed(index: nat, len: nat, needed: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.pvc_index == index && s.pvcs.len() == len && s.needed_index == needed
}

pub open spec fn pvc_and_needed_state(pvc_idx: nat, pvc_len: nat, needed_idx: nat, needed_len: nat) -> spec_fn(VStatefulSetReconcileState) -> bool {
    |s: VStatefulSetReconcileState| s.pvc_index == pvc_idx && s.pvcs.len() == pvc_len && s.needed_index == needed_idx && s.needed.len() == needed_len
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
    assert forall |ex| #![auto] spec.satisfied_by(ex) && spec.entails(always(pre)) implies always(post).satisfied_by(ex) by {
        assert(forall |ex| #[trigger] spec.implies(always(pre)).satisfied_by(ex));
        assert(forall |ex| spec.implies(always(pre)).satisfied_by(ex) <==> (spec.satisfied_by(ex) ==> #[trigger] always(pre).satisfied_by(ex)));
        assert(always(pre).satisfied_by(ex));
        assert(forall |i: nat| #![auto] pre.satisfied_by(ex.suffix(i)) ==> post.satisfied_by(ex.suffix(i)));
    }
}

pub open spec fn get_pvc_with_needed(vsts: VStatefulSetView, controller_id: int, needed: nat) -> TempPred<ClusterState> {
    lift_state(lift_local(controller_id, vsts, at_step_or![(GetPVC, needed_index(needed))]))
}

pub open spec fn create_or_update_or_error_with_needed(vsts: VStatefulSetView, controller_id: int, needed: nat) -> TempPred<ClusterState> {
    lift_state(lift_local(controller_id, vsts, at_step_or![(CreateNeeded, needed_index(needed)), (UpdateNeeded, needed_index(needed)), Error]))
}

proof fn lemma_get_pvc_leads_to_create_or_update_needed(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![GetPVC])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![CreatePVC])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![SkipPVC])))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterGetPVC])))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterCreatePVC])))),
ensures
    forall |j: nat| #[trigger] spec.entails(
        get_pvc_with_needed(vsts, controller_id, j)
            .leads_to(create_or_update_or_error_with_needed(vsts, controller_id, j))
    ),
{
    macro_rules! lift_at_step_or {
        [$($tail:tt)*] => {
            lift_state(lift_local(controller_id, vsts, at_step_or![$($tail)*]))
        }
    }

    let get_pvc_with_needed = |j: nat| lift_at_step_or![(GetPVC, needed_index(j))];

    assert forall |j: nat| #![trigger get_pvc_with_needed(j)] spec.entails(
        get_pvc_with_needed(j)
            .leads_to(lift_at_step_or![(CreateNeeded, needed_index(j)), (UpdateNeeded, needed_index(j)), Error])
    ) by {
        let pvc_pred = |i: nat, l: nat, n: nat, ln: nat|
            lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln)), Error];

        assert forall |i: nat, l: nat, n: nat, ln: nat| #![trigger pvc_pred(i, l, n, ln)]
            i + 1 < l implies spec.entails(
                pvc_pred(i, l, n, ln).leads_to(pvc_pred(i + 1 as nat, l, n, ln))
            ) by {
            let i_plus_1 = (i + 1) as nat;

            entails_implies_leads_to(spec, lift_at_step_or![Error], pvc_pred(i_plus_1, l, n, ln));
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
            cluster.lemma_from_some_state_to_next_state_no_req(
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
            cluster.lemma_from_some_state_to_next_state_no_req(
                spec, controller_id, vsts.object_ref(),
                at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln))],
                at_step_or![(GetPVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error]
            );

            lemma_from_no_pending_req_at_step_to_at_step_and_pred(
                spec, vsts, controller_id, CreatePVC, pvc_and_needed_state(i, l, n, ln)
            );
            cluster.lemma_from_some_state_to_next_state_no_req(
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
                pvc_pred(i_plus_1, l, n, ln)
            );

            or_leads_to_combine_n!(
                spec,
                lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
                lift_at_step_or![Error];
                pvc_pred(i_plus_1, l, n, ln)
            );
            temp_pred_equality(
                pvc_pred(i, l, n, ln),
                lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
            );
        };

        assert forall |i: nat, l: nat, n: nat, ln: nat| #![trigger pvc_pred(i, l, n, ln)]
            i + 1 == l implies spec.entails(
                pvc_pred(i, l, n, ln)
                    .leads_to(lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error])
            ) by {
            let i_plus_1 = (i + 1) as nat;

            entails_implies_leads_to(spec, lift_at_step_or![Error], lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]);

            lemma_from_no_pending_req_at_step_to_at_step_and_pred(
                spec, vsts, controller_id, GetPVC, pvc_and_needed_state(i, l, n, ln)
            );
            cluster.lemma_from_some_state_to_next_state_no_req(
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
            cluster.lemma_from_some_state_to_next_state_no_req(
                spec, controller_id, vsts.object_ref(),
                at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln))],
                at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
            );

            lemma_from_no_pending_req_at_step_to_at_step_and_pred(
                spec, vsts, controller_id, CreatePVC, pvc_and_needed_state(i, l, n, ln)
            );
            cluster.lemma_from_some_state_to_next_state_no_req(
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
                at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
            );

            entails_implies_leads_to(spec, lift_at_step_or![Error], lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]);
            or_leads_to_combine_n!(
                spec,
                lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln))],
                lift_at_step_or![Error];
                lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
            );
            temp_pred_equality(
                lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error],
                lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln))].or(lift_at_step_or![Error])
            );
            leads_to_trans_n!(
                spec,
                lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln))],
                lift_at_step_or![(AfterCreatePVC, pvc_and_needed_state(i_plus_1, l, n, ln)), Error],
                lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
            );

            or_leads_to_combine_n!(
                spec,
                lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln))],
                lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln))];
                lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
            );
            temp_pred_equality(
                lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln)), (CreatePVC, pvc_and_needed_state(i, l, n, ln))],
                lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln))])
            );

            or_leads_to_combine_n!(
                spec,
                lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln)), (CreatePVC, pvc_and_needed_state(i, l, n, ln))],
                lift_at_step_or![Error];
                lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
            );
            temp_pred_equality(
                lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln)), (SkipPVC, pvc_and_needed_state(i, l, n, ln)), Error],
                lift_at_step_or![(SkipPVC, pvc_and_needed_state(i, l, n, ln)), (CreatePVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
            );

            leads_to_trans_n!(
                spec,
                lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln))],
                lift_at_step_or![(CreatePVC, pvc_and_needed_state(i, l, n, ln)), (SkipPVC, pvc_and_needed_state(i, l, n, ln)), Error],
                lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
            );

            or_leads_to_combine_n!(
                spec,
                lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln))],
                lift_at_step_or![Error];
                lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
            );
            temp_pred_equality(
                lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln)), Error],
                lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
            );

            leads_to_trans_n!(
                spec,
                lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
                lift_at_step_or![(AfterGetPVC, pvc_and_needed_state(i, l, n, ln)), Error],
                lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
            );

            or_leads_to_combine_n!(
                spec,
                lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
                lift_at_step_or![Error];
                lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
            );
            temp_pred_equality(
                pvc_pred(i, l, n, ln),
                lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
            );
        };

        assert forall |i: nat, l: nat, n: nat, ln: nat| #![trigger pvc_pred(i, l, n, ln)]
            i >= l implies spec.entails(
                pvc_pred(i, l, n, ln).leads_to(lift_at_step_or![Error])
            ) by {
            lemma_from_no_pending_req_at_step_to_at_step_and_pred(
                spec, vsts, controller_id, GetPVC, pvc_and_needed_state(i, l, n, ln)
            );

            cluster.lemma_from_some_state_to_next_state_no_req(
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
                pvc_pred(i, l, n, ln),
                lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))].or(lift_at_step_or![Error])
            );

            or_leads_to_combine_n!(
                spec,
                lift_at_step_or![(GetPVC, pvc_and_needed_state(i, l, n, ln))],
                lift_at_step_or![Error];
                lift_at_step_or![Error]
            );
        };

        assert forall |i: nat, l: nat, n: nat, ln: nat| #![trigger pvc_pred(i, l, n, ln)]
            spec.entails(
                pvc_pred(i, l, n, ln)
                    .leads_to(lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error])
            ) by {
            if i >= l {
                entails_implies_leads_to(spec, lift_at_step_or![Error], lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]);
                leads_to_trans_n!(
                    spec,
                    pvc_pred(i, l, n, ln),
                    lift_at_step_or![Error],
                    lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
                );
            } else if i + 1 == l {
            } else {
                let target = (l - 1) as nat;
                let p_for_induction = |m: nat, t: nat| pvc_pred(m, t + 1 as nat, n, ln);

                assert forall |m: nat, t: nat| #![trigger p_for_induction(m, t)]
                    m < t implies spec.entails(
                        p_for_induction(m, t).leads_to(p_for_induction(m + 1 as nat, t))
                    ) by {
                };

                leads_to_greater_than_or_eq(spec, p_for_induction);

                temp_pred_equality(p_for_induction(i, target), pvc_pred(i, l, n, ln));
                temp_pred_equality(p_for_induction(target, target), pvc_pred((l - 1) as nat, l, n, ln));

                leads_to_trans_n!(
                    spec,
                    pvc_pred(i, l, n, ln),
                    pvc_pred((l - 1) as nat, l, n, ln),
                    lift_at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error]
                );
            }
        };

        lemma_get_pvc_union_equiv(spec, vsts, controller_id, pvc_pred, j);
    };
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

pub proof fn lemma_after_delete_condemned_leads_to_idle(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![AfterDeleteCondemned])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteCondemned])))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts.object_ref(), at_step_or![DeleteOutdated])))),
    spec.entails(lift_state(lift_local(controller_id, vsts, at_step_or![DeleteOutdated])).leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()))))
ensures
    spec.entails(lift_state(lift_local(controller_id, vsts, at_step_or![AfterDeleteCondemned])).leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref())))),
{
    macro_rules! lift_at_step_or {
        [$($tail:tt)*] => {
            lift_state(lift_local(controller_id, vsts, at_step_or![$($tail)*]))
        }
    }

    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref());
    let reconcile_error = cluster.reconciler_reconcile_error(controller_id, vsts.object_ref());

    let delete_condemned_with_index_and_len = |n: nat, l: nat| lift_at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l)), Error, DeleteOutdated];

    assert forall |n: nat, l: nat| #![trigger delete_condemned_with_index_and_len(n, l)]
        n < l implies spec.entails(delete_condemned_with_index_and_len(n, l).leads_to(delete_condemned_with_index_and_len(n + 1 as nat, l))) by {
        let n_plus_1 = n + 1 as nat;
        entails_implies_leads_to(spec, lift_at_step_or![Error], delete_condemned_with_index_and_len(n_plus_1, l));
        entails_implies_leads_to(spec, lift_at_step_or![DeleteOutdated], delete_condemned_with_index_and_len(n_plus_1, l));
        assert(forall |input_cr, resp_o, s| #![trigger dummy((input_cr, resp_o, s))]
            at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))](s) ==>
            at_step_or![(DeleteCondemned, condemned_index_and_len(n, l)), Error, DeleteOutdated]((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0));
        lemma_from_pending_req_in_flight_or_resp_in_flight_at_step_to_at_step_and_pred(
            spec, vsts, controller_id, AfterDeleteCondemned, condemned_index_and_len(n, l)
        );
        cluster.lemma_from_some_state_to_arbitrary_next_state(
            spec, controller_id, vsts.object_ref(),
            at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))],
            at_step_or![(DeleteCondemned, condemned_index_and_len(n, l)), Error, DeleteOutdated]
        );
        assert(forall |input_cr, resp_o, s| #![trigger dummy((input_cr, resp_o, s))]
            at_step_or![(DeleteCondemned, condemned_index_and_len(n, l))](s) ==>
            at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n_plus_1, l)), Error]((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0));
        lemma_from_no_pending_req_at_step_to_at_step_and_pred(spec, vsts, controller_id, DeleteCondemned, condemned_index_and_len(n, l));
        cluster.lemma_from_some_state_to_next_state_no_req(
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
        assert(forall |input_cr, resp_o, s| #![trigger dummy((input_cr, resp_o, s))]
            at_step_or![(AfterDeleteCondemned, condemned_index_and_len(n, l))](s) ==>
            at_step_or![Error, DeleteOutdated]((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0));
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

    lemma_delete_condemned_union_equiv(spec, vsts, controller_id, delete_condemned_with_index_and_len);
}

#[verifier(external_body)]
proof fn lemma_delete_condemned_union_equiv(
    spec: TempPred<ClusterState>,
    vsts: VStatefulSetView,
    controller_id: int,
    delete_condemned_with_index_and_len: spec_fn(nat, nat) -> TempPred<ClusterState>
)
    requires
        forall |n: nat, l: nat| #![trigger delete_condemned_with_index_and_len(n, l)]
            spec.entails(delete_condemned_with_index_and_len(n, l).leads_to(lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()) }))),
    ensures
        spec.entails(lift_state(lift_local(controller_id, vsts, at_step_or![AfterDeleteCondemned])).leads_to(lift_state(|s: ClusterState| { !s.ongoing_reconciles(controller_id).contains_key(vsts.object_ref()) })))
{
}

#[verifier(external_body)]
proof fn lemma_get_pvc_union_equiv(
    spec: TempPred<ClusterState>,
    vsts: VStatefulSetView,
    controller_id: int,
    pvc_pred: spec_fn(nat, nat, nat, nat) -> TempPred<ClusterState>,
    needed_idx: nat
)
    requires
        forall |i: nat, l: nat, n: nat, ln: nat| #![trigger pvc_pred(i, l, n, ln)]
            spec.entails(
                pvc_pred(i, l, n, ln)
                    .leads_to(lift_state(lift_local(controller_id, vsts, at_step_or![(CreateNeeded, needed_index(n)), (UpdateNeeded, needed_index(n)), Error])))
            ),
    ensures
        spec.entails(
            lift_state(lift_local(controller_id, vsts, at_step_or![(GetPVC, needed_index(needed_idx))]))
                .leads_to(lift_state(lift_local(controller_id, vsts, at_step_or![(CreateNeeded, needed_index(needed_idx)), (UpdateNeeded, needed_index(needed_idx)), Error])))
        )
{
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