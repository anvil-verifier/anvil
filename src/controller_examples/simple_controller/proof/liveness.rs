// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_examples::simple_controller::proof::safety::*;
use crate::controller_examples::simple_controller::proof::shared::*;
use crate::controller_examples::simple_controller::spec::{
    custom_resource::*,
    reconciler,
    reconciler::{simple_reconciler, SimpleReconcileState},
};
use crate::kubernetes_api_objects::{api_method::*, common::*, resource::*};
use crate::kubernetes_cluster::{
    proof::{
        cluster::*, controller_runtime_liveness::*, controller_runtime_safety::*,
        kubernetes_api_liveness, kubernetes_api_safety,
    },
    spec::{
        controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
        controller::controller_runtime::{
            continue_reconcile, end_reconcile, run_scheduled_reconcile,
        },
        controller::state_machine::controller,
        distributed_system::*,
        kubernetes_api::state_machine::handle_request,
        message::*,
    },
};
use crate::temporal_logic::{defs::*, rules::*};
use builtin::*;
use builtin_macros::*;
use vstd::*;
use vstd::{option::*, result::*};

verus! {

spec fn cr_exists(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    lift_state(|s: State<SimpleReconcileState>| s.resource_obj_exists(cr.to_dynamic_object()) && cr.metadata.name.is_Some() && cr.metadata.namespace.is_Some())
}

spec fn cr_matched(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    lift_state(|s: State<SimpleReconcileState>|
        s.resource_key_exists(reconciler::subresource_configmap(cr).object_ref()))
}

/// Proof strategy:
///     (1) For case_1, case_2, ..., case_n, we prove partial_spec /\ [] crash_disabled /\ all_invariants /\ []cr_exists |= case_i ~> cm_exists. The disjunction of case_1, case_2, ..., case_n should be true.
///     (2) Combining the n cases, we have partial_spec /\ [] crash_disabled /\ all_invariants /\ []cr_exists |= true ~> cm_exists. Unpacking []crash_disabled /\ []cr_exists to the right side, we have spec /\ all_invariants |= []cr_exists ~> cm_exists.
///     (3) To unpack []cr_exists, we have to prove the stability of partial_spec /\ all_invariants.
///     (4) By proving all the invariants can be inferred from spec, here comes to spec |= []cr_exists /\ []crash_disabled ~> cm_exists.
///     (5) Next, with the help of lemma_p_leads_to_cm_always_exists, we have spec |= []cr_exists /\ []crash_disabled ~> []cm_exists.
///     (6) By the weak fairness of the action disable_crash, we have spec |= []cr_exists ~> []cr_exists /\ []crash_disabled.
///     (7) By the transitivity of leads_to relation, we have spec |= []cr_exists ~> []cr_matched.

/// To prove the liveness property, we need some invariants (these invariants have already contained "always" constraint).
spec fn all_invariants(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr)))
    .and(tla_forall(|msg| always(lift_state(resp_matches_at_most_one_pending_req(msg, cr.object_ref())))))
    .and(tla_forall(|resp_msg: Message| always(lift_state(at_most_one_resp_matches_req(resp_msg, cr.object_ref())))))
    .and(always(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr))))
    .and(always(lift_state(reconciler_at_init_pc(cr))
        .implies(lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref())))))
    .and(always(lift_state(every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>())))
    .and(always(lift_state(every_in_flight_req_has_unique_id::<SimpleReconcileState>())))
}

spec fn partial_spec_with_invariants_and_assumptions(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    sm_partial_spec(simple_reconciler())
    .and(always(lift_state(crash_disabled::<SimpleReconcileState>())))
    .and(all_invariants(cr))
    .and(always(cr_exists(cr)))
}

spec fn liveness(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    always(cr_exists(cr)).leads_to(always(cr_matched(cr)))
}

proof fn liveness_proof_forall_cr()
    ensures
        forall |cr: CustomResourceView| #[trigger] sm_spec(simple_reconciler()).entails(liveness(cr)),
{
    assert forall |cr: CustomResourceView| #[trigger] sm_spec(simple_reconciler()).entails(liveness(cr)) by {
        liveness_proof(cr);
    };
}

proof fn liveness_proof(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            always(cr_exists(cr)).leads_to(always(cr_matched(cr)))
        ),
{
    // Step (6)
    lemma_any_pred_leads_to_crash_always_disabled(sm_spec(simple_reconciler()), simple_reconciler(), always(cr_exists(cr)));
    leads_to_self_temp::<State<SimpleReconcileState>>(always(cr_exists(cr)));
    leads_to_always_combine_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), always(cr_exists(cr)),
        cr_exists(cr), lift_state(crash_disabled::<SimpleReconcileState>()));
    always_and_equality::<State<SimpleReconcileState>>(cr_exists(cr), lift_state(crash_disabled::<SimpleReconcileState>()));
    lemma_sm_spec_entails_cr_always_exists_and_crash_always_disabled_leads_to_cm_always_exists(cr);
    // Step (7)
    leads_to_trans_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), always(cr_exists(cr)),
        always(cr_exists(cr)).and(always(lift_state(crash_disabled::<SimpleReconcileState>()))), always(cr_matched(cr)));
}

proof fn lemma_sm_spec_entails_cr_always_exists_and_crash_always_disabled_leads_to_cm_always_exists(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            always(cr_exists(cr)).and(always(lift_state(crash_disabled::<SimpleReconcileState>())))
                .leads_to(always(cr_matched(cr)))),
{
    lemma_true_leads_to_cm_exists(cr);
    temp_pred_equality::<State<SimpleReconcileState>>(
        sm_partial_spec(simple_reconciler()).and(all_invariants(cr))
        .and(always(cr_exists(cr)).and(always(lift_state(crash_disabled::<SimpleReconcileState>())))),
        partial_spec_with_invariants_and_assumptions(cr));
    lemma_valid_stable_sm_partial_spec_and_invariants(cr);
    // Step (2)
    unpack_assumption_from_spec::<State<SimpleReconcileState>>(lift_state(init(simple_reconciler())),
        sm_partial_spec(simple_reconciler()).and(all_invariants(cr)),
        always(cr_exists(cr)).and(always(lift_state(crash_disabled::<SimpleReconcileState>()))),
        lift_state(cm_exists(cr)));
    temp_pred_equality::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()).and(all_invariants(cr)),
        lift_state(init(simple_reconciler())).and(sm_partial_spec(simple_reconciler()).and(all_invariants(cr))));
    lemma_sm_spec_entails_all_invariants(cr);
    simplify_predicate::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), all_invariants(cr));
    // Step (5)
    lemma_p_leads_to_cm_always_exists(cr,
        always(cr_exists(cr)).and(always(lift_state(crash_disabled::<SimpleReconcileState>()))));
}

// Step (2)
proof fn lemma_true_leads_to_cm_exists(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            true_pred::<State<SimpleReconcileState>>().leads_to(lift_state(cm_exists(cr)))
        ),
{
    lemma_reconcile_idle_leads_to_cm_exists(cr);
    lemma_reconcile_ongoing_leads_to_cm_exists(cr);

    temp_pred_equality::<State<SimpleReconcileState>>(
        true_pred::<State<SimpleReconcileState>>(),
        lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.object_ref()))
            .or(lift_state(|s: State<SimpleReconcileState>| !s.reconcile_state_contains(cr.object_ref()))));

    or_leads_to_combine_temp(partial_spec_with_invariants_and_assumptions(cr),
        lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.object_ref())),
        lift_state(|s: State<SimpleReconcileState>| !s.reconcile_state_contains(cr.object_ref())),
        lift_state(cm_exists(cr)));
}

// Step (3), prove the stability of partial_spec /\ all_invariants.
proof fn lemma_valid_stable_sm_partial_spec_and_invariants(cr: CustomResourceView)
    ensures
        valid(stable(sm_partial_spec(simple_reconciler()).and(all_invariants(cr)))),
{
    valid_stable_sm_partial_spec(simple_reconciler());

    always_p_stable::<State<SimpleReconcileState>>(
        lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr)));
    always_p_stable::<State<SimpleReconcileState>>(
        lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr)));
    always_p_stable::<State<SimpleReconcileState>>(
        tla_forall(|msg| lift_state(resp_matches_at_most_one_pending_req(msg, cr.object_ref()))));
    always_p_stable::<State<SimpleReconcileState>>(
        tla_forall(|resp_msg: Message| lift_state(at_most_one_resp_matches_req(resp_msg, cr.object_ref()))));
    always_p_stable::<State<SimpleReconcileState>>(
        lift_state(reconciler_at_init_pc(cr))
            .implies(lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref()))));
    always_p_stable::<State<SimpleReconcileState>>(
        lift_state(every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>()));
    always_p_stable::<State<SimpleReconcileState>>(
        lift_state(every_in_flight_req_has_unique_id::<SimpleReconcileState>()));

    let a_to_p = |msg| lift_state(resp_matches_at_most_one_pending_req::<SimpleReconcileState>(msg, cr.object_ref()));
    let a_to_always = |msg| always(lift_state(
        resp_matches_at_most_one_pending_req::<SimpleReconcileState>(msg, cr.object_ref())));
    tla_forall_always_equality_variant::<State<SimpleReconcileState>, Message>(a_to_always, a_to_p);

    let a_to_p_1 = |resp_msg: Message| lift_state(at_most_one_resp_matches_req(resp_msg, cr.object_ref()));
    let a_to_always_1 = |resp_msg: Message| always(lift_state(at_most_one_resp_matches_req(resp_msg, cr.object_ref())));
    tla_forall_always_equality_variant::<State<SimpleReconcileState>, Message>(a_to_always_1, a_to_p_1);

    stable_and_n!(
        always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr))),
        tla_forall(|msg| always(lift_state(resp_matches_at_most_one_pending_req(msg, cr.object_ref())))),
        tla_forall(|msg| always(lift_state(at_most_one_resp_matches_req(msg, cr.object_ref())))),
        always(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr))),
        always(lift_state(reconciler_at_init_pc(cr))
            .implies(lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref())))),
        always(lift_state(every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>())),
        always(lift_state(every_in_flight_req_has_unique_id::<SimpleReconcileState>())));

    stable_and_temp::<State<SimpleReconcileState>>(sm_partial_spec(simple_reconciler()), all_invariants(cr));
}

// Step (4)
// This proof is straightforward: Use the lemmas which prove spec |= invariant_i for i = 1, 2, 3, 4 respectively.
proof fn lemma_sm_spec_entails_all_invariants(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(all_invariants(cr)),
{
    lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr);
    lemma_forall_resp_always_matches_at_most_one_pending_req(simple_reconciler(), cr.object_ref());
    lemma_forall_always_at_most_one_resp_matches_req(simple_reconciler(), cr.object_ref());
    lemma_always_reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr);
    lemma_always_reconcile_init_pc_and_no_pending_req(cr);
    lemma_always_every_in_flight_msg_has_lower_id_than_chan_manager(simple_reconciler());
    lemma_always_every_in_flight_req_has_unique_id(simple_reconciler());

    entails_and_n!(sm_spec(simple_reconciler()),
        always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr))),
        tla_forall(|msg| always(lift_state(resp_matches_at_most_one_pending_req(msg, cr.object_ref())))),
        tla_forall(|resp_msg: Message| always(lift_state(at_most_one_resp_matches_req(resp_msg, cr.object_ref())))),
        always(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr))),
        always(lift_state(reconciler_at_init_pc(cr))
            .implies(lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref())))),
        always(lift_state(every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>())),
        always(lift_state(every_in_flight_req_has_unique_id::<SimpleReconcileState>())));
}

proof fn lemma_p_leads_to_cm_always_exists(cr: CustomResourceView, p: TempPred<State<SimpleReconcileState>>)
    requires
        sm_spec(simple_reconciler()).entails(
            p.leads_to(lift_state(cm_exists(cr)))
        ),
    ensures
        sm_spec(simple_reconciler()).entails(
            p.leads_to(always(lift_state(cm_exists(cr))))
        ),
{
    let next_and_invariant = |s: State<SimpleReconcileState>, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& delete_cm_req_msg_not_in_flight(cr)(s)
    };

    lemma_delete_cm_req_msg_never_in_flight(cr);

    strengthen_next::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()),
        delete_cm_req_msg_not_in_flight(cr), next_and_invariant);
    leads_to_stable_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_action(next_and_invariant),
        p, lift_state(cm_exists(cr)));
}

proof fn lemma_reconcile_idle_leads_to_cm_exists(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
        lift_state(|s: State<SimpleReconcileState>| !s.reconcile_state_contains(cr.object_ref()))
            .leads_to(lift_state(cm_exists(cr)))
        ),
{
    lemma_cr_always_exists_entails_reconcile_idle_leads_to_reconcile_init_and_no_pending_req(simple_reconciler(),
        cr.object_ref());

    implies_preserved_by_always_temp::<State<SimpleReconcileState>>(cr_exists(cr),
        lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref())));

    entails_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr), always(cr_exists(cr)),
        always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref()))));
    entails_and_n!(partial_spec_with_invariants_and_assumptions(cr),
        sm_partial_spec(simple_reconciler()),
        always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref()))),
        always(lift_state(crash_disabled::<SimpleReconcileState>())));

    entails_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr),
        sm_partial_spec(simple_reconciler())
            .and(always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref()))))
            .and(always(lift_state(crash_disabled::<SimpleReconcileState>()))),
        lift_state(|s: State<SimpleReconcileState>| !s.reconcile_state_contains(cr.object_ref()))
            .leads_to(lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref()))));

    lemma_init_pc_and_no_pending_req_leads_to_cm_exists(cr);
    leads_to_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr),
        |s: State<SimpleReconcileState>| !s.reconcile_state_contains(cr.object_ref()),
        reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref()), cm_exists(cr));
}

proof fn lemma_reconcile_ongoing_leads_to_cm_exists(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
        lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.object_ref()))
            .leads_to(lift_state(cm_exists(cr)))
        ),
{
    temp_pred_equality::<State<SimpleReconcileState>>(
        lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.object_ref())),
        lift_state(reconciler_reconcile_error(cr))
            .or(lift_state(reconciler_at_init_pc(cr)))
            .or(lift_state(reconciler_at_after_get_cr_pc(cr)))
            .or(lift_state(reconciler_at_after_create_cm_pc(cr))));
    lemma_error_pc_leads_to_cm_exists(cr);
    lemma_init_pc_leads_to_cm_exists(cr);
    lemma_after_get_cr_pc_leads_to_cm_exists(cr);
    lemma_after_create_cm_pc_leads_to_cm_exists(cr);
    or_leads_to_combine_n!(partial_spec_with_invariants_and_assumptions(cr),
        lift_state(reconciler_reconcile_error(cr)),
        lift_state(reconciler_at_init_pc(cr)),
        lift_state(reconciler_at_after_get_cr_pc(cr)),
        lift_state(reconciler_at_after_create_cm_pc(cr));
        lift_state(cm_exists(cr)));
}

proof fn lemma_init_pc_and_no_pending_req_leads_to_cm_exists(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref()))
                .leads_to(lift_state(cm_exists(cr)))
        ),
{
    lemma_init_pc_and_no_pending_req_leads_to_after_create_cm_pc(cr);
    lemma_after_create_cm_pc_leads_to_cm_exists(cr);
    leads_to_trans_auto::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr));
}

proof fn lemma_error_pc_leads_to_cm_exists(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
        lift_state(reconciler_reconcile_error(cr))
            .leads_to(lift_state(cm_exists(cr)))
        ),
{
    lemma_cr_always_exists_entails_reconcile_error_leads_to_reconcile_init_and_no_pending_req(
        partial_spec_with_always_cr_key_exists_and_crash_disabled(simple_reconciler(), cr.object_ref()),
        simple_reconciler(), cr.object_ref());

    implies_preserved_by_always_temp::<State<SimpleReconcileState>>(cr_exists(cr),
        lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref())));

    entails_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr), always(cr_exists(cr)),
        always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref()))));
    entails_and_n!(partial_spec_with_invariants_and_assumptions(cr),
        sm_partial_spec(simple_reconciler()),
        always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref()))),
        always(lift_state(crash_disabled::<SimpleReconcileState>())));

    entails_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr),
        partial_spec_with_always_cr_key_exists_and_crash_disabled(simple_reconciler(), cr.object_ref()),
        lift_state(reconciler_reconcile_error(cr))
            .leads_to(lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref()))));

    lemma_init_pc_and_no_pending_req_leads_to_cm_exists(cr);
    leads_to_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr),
        reconciler_reconcile_error(cr),
        reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref()), cm_exists(cr));
}

proof fn lemma_init_pc_leads_to_cm_exists(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(reconciler_at_init_pc(cr))
                .leads_to(lift_state(cm_exists(cr)))
        ),
{
    implies_to_leads_to::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr),
        lift_state(reconciler_at_init_pc(cr)),
        lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref())));
    lemma_init_pc_and_no_pending_req_leads_to_cm_exists(cr);
    leads_to_trans_auto::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr));
}

proof fn lemma_after_get_cr_pc_leads_to_cm_exists(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(reconciler_at_after_get_cr_pc(cr))
                .leads_to(lift_state(cm_exists(cr)))
        ),
{
    assert forall |ex| partial_spec_with_invariants_and_assumptions(cr).satisfied_by(ex) implies
    #[trigger] lift_state(reconciler_at_after_get_cr_pc(cr))
        .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr))).satisfied_by(ex) by {
        assert forall |i| #[trigger] lift_state(reconciler_at_after_get_cr_pc(cr)).satisfied_by(ex.suffix(i)) implies
        eventually(lift_state(reconciler_at_after_create_cm_pc(cr))).satisfied_by(ex.suffix(i)) by {
            assert(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr))
                .satisfied_by(ex.suffix(i)));
            let s = ex.suffix(i).head();
            let req_msg = choose |req_msg: Message| {
                #[trigger] is_controller_get_cr_request_msg(req_msg, cr)
                && s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg)
                && (s.message_in_flight(req_msg)
                    || exists |resp_msg: Message| {
                        #[trigger] s.message_in_flight(resp_msg)
                        && resp_msg_matches_req_msg(resp_msg, req_msg)
                    })
            };
            if (s.message_in_flight(req_msg)) {
                lemma_req_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg, cr);
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i,
                    partial_spec_with_invariants_and_assumptions(cr),
                    lift_state(reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr)),
                    lift_state(reconciler_at_after_create_cm_pc(cr)));
            } else {
                lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg, cr);
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i,
                    partial_spec_with_invariants_and_assumptions(cr),
                    lift_state(|s: State<SimpleReconcileState>| {
                        exists |m: Message| {
                            &&& #[trigger] s.message_in_flight(m)
                            &&& resp_msg_matches_req_msg(m, req_msg)
                        }
                    }).and(lift_state(reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr))),
                    lift_state(reconciler_at_after_create_cm_pc(cr)));
            }
        }
    }
    lemma_after_create_cm_pc_leads_to_cm_exists(cr);
    leads_to_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr),
        reconciler_at_after_get_cr_pc(cr), reconciler_at_after_create_cm_pc(cr), cm_exists(cr));
}

proof fn lemma_after_create_cm_pc_leads_to_cm_exists(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(reconciler_at_after_create_cm_pc(cr))
                .leads_to(lift_state(cm_exists(cr)))
        ),
{
    assert forall |ex| #[trigger] partial_spec_with_invariants_and_assumptions(cr).satisfied_by(ex) implies
    lift_state(reconciler_at_after_create_cm_pc(cr)).leads_to(lift_state(cm_exists(cr))).satisfied_by(ex) by {
        assert forall |i| #[trigger] lift_state(reconciler_at_after_create_cm_pc(cr)).satisfied_by(ex.suffix(i))
        implies eventually(lift_state(cm_exists(cr))).satisfied_by(ex.suffix(i)) by {
            assert(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr))
                .satisfied_by(ex.suffix(i)));
            let s = ex.suffix(i).head();
            let req_msg = choose |m: Message| {
                (#[trigger] is_controller_create_cm_request_msg(m, cr)
                && s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(m)
                && s.message_in_flight(m))
                || s.resource_key_exists(reconciler::subresource_configmap(cr).object_ref())
            };
            if (s.resource_key_exists(reconciler::subresource_configmap(cr).object_ref())) {
                assert(lift_state(cm_exists(cr)).satisfied_by(ex.suffix(i).suffix(0)));
            } else {
                let cm = reconciler::subresource_configmap(cr).to_dynamic_object();
                let pre = |s: State<SimpleReconcileState>| {
                    &&& s.message_in_flight(req_msg)
                    &&& req_msg.dst == HostId::KubernetesAPI
                    &&& req_msg.content.is_create_request()
                    &&& req_msg.content.get_create_request().obj == cm
                };
                kubernetes_api_liveness::lemma_create_req_leads_to_res_exists(sm_partial_spec(simple_reconciler()),
                    simple_reconciler(), req_msg, cm);
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i, sm_partial_spec(simple_reconciler()),
                    lift_state(pre), lift_state(cm_exists(cr)));
            }
        };
    };
}

proof fn lemma_init_pc_and_no_pending_req_leads_to_after_create_cm_pc(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref()))
                .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    lemma_init_pc_and_no_pending_req_leads_to_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr);

    // To make the spec and proof simpler, we first choose the pending req_msg.
    // In this case, we have to use the `assert forall` to continue the proof in the view of a specific execution.
    assert forall |ex| #[trigger] partial_spec_with_invariants_and_assumptions(cr).satisfied_by(ex) implies
        lift_state(reconciler_at_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr))
            .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr))).satisfied_by(ex) by {
        assert forall |i| #[trigger] lift_state(reconciler_at_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr)).satisfied_by(ex.suffix(i)) implies
        eventually(lift_state(reconciler_at_after_create_cm_pc(cr))).satisfied_by(ex.suffix(i)) by {
            let s = ex.suffix(i).head();
            let req_msg = choose |msg| {
                &&& #[trigger] is_controller_get_cr_request_msg(msg, cr)
                &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(msg)
                &&& ! exists |resp_msg: Message| {
                    &&& #[trigger] s.message_in_flight(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                }
            };
            lemma_after_get_cr_pc_and_pending_req_in_flight_and_no_resp_in_flight_leads_to_ok_resp_received(req_msg, cr);
            lemma_after_get_cr_pc_and_ok_resp_received_leads_to_after_create_cm_pc(req_msg, cr);
            leads_to_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr),
                reconciler_at_after_get_cr_pc_and_pending_req_in_flight_and_no_resp_in_flight(req_msg, cr),
                reconciler_at_after_get_cr_pc_and_ok_resp_with_name_and_namespace_in_flight(req_msg, cr), reconciler_at_after_create_cm_pc(cr));

            instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i,
                partial_spec_with_invariants_and_assumptions(cr),
                lift_state(reconciler_at_after_get_cr_pc_and_pending_req_in_flight_and_no_resp_in_flight(req_msg, cr)),
                lift_state(reconciler_at_after_create_cm_pc(cr)));
        };
    };

    leads_to_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr),
        reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref()),
        reconciler_at_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr),
        reconciler_at_after_create_cm_pc(cr));
}

proof fn lemma_req_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg: Message, cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr))
                .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    let pre = reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr);
    let get_cr_resp_msg_sent = |s: State<SimpleReconcileState>| {
        exists |resp_msg: Message| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        }
    };
    let spec = partial_spec_with_invariants_and_assumptions(cr);
    leads_to_weaken_auto::<State<SimpleReconcileState>>(spec);

    leads_to_self::<State<SimpleReconcileState>>(pre);

    kubernetes_api_liveness::lemma_get_req_leads_to_some_resp(spec, simple_reconciler(), req_msg, cr.object_ref());

    let get_req = |s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(req_msg)
        &&& req_msg.dst == HostId::KubernetesAPI
        &&& req_msg.content.is_get_request()
        &&& req_msg.content.get_get_request().key == cr.object_ref()
    };

    // Now we have:
    //  spec |= pre ~> reconciler_at_after_get_cr_pc_and_pending_req /\ get_cr_req_in_flight
    //  spec |= get_cr_req_in_flight ~> get_cr_resp_msg_sent
    // By applying leads_to_partial_confluence,
    // we will get spec |= pre ~> reconciler_at_after_get_cr_pc_and_pending_req /\ get_cr_resp_msg_sent
    let stronger_next = |s, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& !s.crash_enabled
    };
    strengthen_next::<State<SimpleReconcileState>>(spec, next(simple_reconciler()),
        crash_disabled::<SimpleReconcileState>(), stronger_next);
    leads_to_partial_confluence::<State<SimpleReconcileState>>(spec, stronger_next, pre,
        reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr), get_req, get_cr_resp_msg_sent);
    // Now we have all the premise to fire the leads-to formula from
    // lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc
    lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg, cr);
    leads_to_trans::<State<SimpleReconcileState>>(spec,
        pre,
        |s| {
            &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
            &&& get_cr_resp_msg_sent(s)
        },
        reconciler_at_after_create_cm_pc(cr)
    );
}

proof fn lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg: Message, cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                exists |m: Message| {
                    &&& #[trigger] s.message_in_flight(m)
                    &&& resp_msg_matches_req_msg(m, req_msg)
                }
            }).and(lift_state(reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)))
            .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    let m_to_pre1 = |m: Message| lift_state(|s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(m)
        &&& resp_msg_matches_req_msg(m, req_msg)
    });
    let pre2 = lift_state(reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr));
    let post = lift_state(reconciler_at_after_create_cm_pc(cr));
    let spec = partial_spec_with_invariants_and_assumptions(cr);
    assert forall |msg: Message| spec.entails(#[trigger] m_to_pre1(msg).and(pre2).leads_to(post)) by {
        lemma_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(msg, req_msg, cr);
        let pre = lift_state(|s: State<SimpleReconcileState>| {
            &&& s.message_in_flight(msg)
            &&& resp_msg_matches_req_msg(msg, req_msg)
            &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
        });
        temp_pred_equality::<State<SimpleReconcileState>>(pre, m_to_pre1(msg).and(pre2));
    };
    leads_to_exists_intro::<State<SimpleReconcileState>, Message>(spec, |m| m_to_pre1(m).and(pre2), post);
    tla_exists_and_equality::<State<SimpleReconcileState>, Message>(m_to_pre1, pre2);

    // This is very tedious proof to show exists_m_to_pre1 == tla_exists(m_to_pre1)
    // I hope we can encapsulate this as a lemma
    let exists_m_to_pre1 = lift_state(|s: State<SimpleReconcileState>| {
        exists |m: Message| {
            &&& #[trigger] s.message_in_flight(m)
            &&& resp_msg_matches_req_msg(m, req_msg)
        }
    });
    assert forall |ex| #[trigger] exists_m_to_pre1.satisfied_by(ex) implies tla_exists(m_to_pre1).satisfied_by(ex) by {
        let m = choose |m: Message| {
            &&& #[trigger] ex.head().message_in_flight(m)
            &&& resp_msg_matches_req_msg(m, req_msg)
        };
        assert(m_to_pre1(m).satisfied_by(ex));
    };
    temp_pred_equality::<State<SimpleReconcileState>>(exists_m_to_pre1, tla_exists(m_to_pre1));
}

proof fn lemma_init_pc_and_no_pending_req_leads_to_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref()))
                .leads_to(lift_state(reconciler_at_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr)))
        ),
{
    let pre = reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref());
    let post = reconciler_at_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr);
    let input = (Option::None, Option::Some(cr.object_ref()));
    let stronger_next = |s, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& !s.crash_enabled
        &&& every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>()(s)
    };
    entails_always_and_n!(partial_spec_with_invariants_and_assumptions(cr),
        lift_action(next(simple_reconciler())), lift_state(crash_disabled::<SimpleReconcileState>()),
        lift_state(every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>()));
    temp_pred_equality(lift_action(stronger_next),
        lift_action(next(simple_reconciler()))
        .and(lift_state(crash_disabled::<SimpleReconcileState>()))
        .and(lift_state(every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>())));
    assert forall |s, s_prime| reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref())(s) && #[trigger] stronger_next(s, s_prime) implies
    reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref())(s_prime)
    || reconciler_at_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr)(s_prime) by {
        next_and_not_crash_preserves_init_pc_or_reconciler_at_after_get_cr_pc_and_pending_req_in_flight_and_no_resp_in_flight(cr, s, s_prime);
    }

    lemma_pre_leads_to_post_by_controller(partial_spec_with_invariants_and_assumptions(cr), simple_reconciler(), input, stronger_next, continue_reconcile(simple_reconciler()), pre, post);
}

proof fn lemma_after_get_cr_pc_and_pending_req_in_flight_and_no_resp_in_flight_leads_to_ok_resp_received(req_msg: Message, cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(reconciler_at_after_get_cr_pc_and_pending_req_in_flight_and_no_resp_in_flight(req_msg, cr))
                .leads_to(lift_state(reconciler_at_after_get_cr_pc_and_ok_resp_with_name_and_namespace_in_flight(req_msg, cr)))
        ),
{
    let pre = reconciler_at_after_get_cr_pc_and_pending_req_in_flight_and_no_resp_in_flight(req_msg, cr);
    let post = reconciler_at_after_get_cr_pc_and_ok_resp_with_name_and_namespace_in_flight(req_msg, cr);
    let stronger_next = |s, s_prime: State<SimpleReconcileState>| {
        next(simple_reconciler())(s, s_prime)
        && !s.crash_enabled
        && s.resource_obj_exists(cr.to_dynamic_object()) && cr.metadata.name.is_Some() && cr.metadata.namespace.is_Some()
        && every_in_flight_req_has_unique_id::<SimpleReconcileState>()(s)
    };
    implies_preserved_by_always_temp(cr_exists(cr), lift_state(|s: State<SimpleReconcileState>| s.resource_obj_exists(cr.to_dynamic_object())));
    entails_trans(partial_spec_with_invariants_and_assumptions(cr), always(cr_exists(cr)), always(lift_state(|s: State<SimpleReconcileState>| s.resource_obj_exists(cr.to_dynamic_object()))));
    entails_always_and_n!(partial_spec_with_invariants_and_assumptions(cr),
        lift_action(next(simple_reconciler())), lift_state(crash_disabled::<SimpleReconcileState>()),
        cr_exists(cr),
        lift_state(every_in_flight_req_has_unique_id::<SimpleReconcileState>()));
    temp_pred_equality(lift_action(stronger_next),
        lift_action(next(simple_reconciler())).and(lift_state(crash_disabled::<SimpleReconcileState>()))
        .and(cr_exists(cr))
        .and(lift_state(every_in_flight_req_has_unique_id::<SimpleReconcileState>())));
    kubernetes_api_liveness::lemma_pre_leads_to_post_by_kubernetes_api(partial_spec_with_invariants_and_assumptions(cr),
        simple_reconciler(), Option::Some(req_msg), stronger_next, handle_request(), pre, post);
}

// This lemma proves:
// ideal_spec |= get_cr_pc /\ pending_req /\ ok_resp_in_flight ~> create_cm_pc
proof fn lemma_after_get_cr_pc_and_ok_resp_received_leads_to_after_create_cm_pc(req_msg: Message, cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(reconciler_at_after_get_cr_pc_and_ok_resp_with_name_and_namespace_in_flight(req_msg, cr))
                .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    let pre = reconciler_at_after_get_cr_pc_and_ok_resp_with_name_and_namespace_in_flight(req_msg, cr);
    let resp_msg = form_get_resp_msg(req_msg, Result::Ok(cr.to_dynamic_object()));
    let clearer_pre = lift_state(|s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
        &&& resp_is_ok_and_named_and_namespaced(resp_msg)
    });
    lemma_ok_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(resp_msg, req_msg, cr);
    leads_to_weaken_temp::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_assumptions(cr), clearer_pre,
        lift_state(reconciler_at_after_create_cm_pc(cr)), lift_state(pre), lift_state(reconciler_at_after_create_cm_pc(cr)));
}

spec fn strengthen_next_with_rep_resp_injectivity(resp_msg: Message, req_msg: Message, cr: CustomResourceView) -> ActionPred<State<SimpleReconcileState>> {
    |s, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& at_most_one_resp_matches_req(resp_msg, cr.object_ref())(s)
        &&& resp_matches_at_most_one_pending_req(resp_msg, cr.object_ref())(s)
        &&& !s.crash_enabled
    }
}

spec fn resp_is_ok_and_named_and_namespaced(resp_msg: Message) -> bool {
    let res = resp_msg.content.get_APIResponse_0().get_GetResponse_0().res;

    resp_msg.content.is_APIResponse()
    && resp_msg.content.get_APIResponse_0().is_GetResponse()
    && res.is_Ok()
    && res.get_Ok_0().metadata.name.is_Some()
    && res.get_Ok_0().metadata.namespace.is_Some()
}

proof fn lemma_ok_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(resp_msg: Message, req_msg: Message, cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                &&& s.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
                &&& resp_is_ok_and_named_and_namespaced(resp_msg)
            }).leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    let pre = |s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
        &&& resp_is_ok_and_named_and_namespaced(resp_msg)
    };
    let input = (Option::Some(resp_msg), Option::Some(cr.object_ref()));
    let spec = partial_spec_with_invariants_and_assumptions(cr);
    spec_entails_strengthen_next_with_rep_resp_injectivity(resp_msg, req_msg, cr);
    let post = reconciler_at_after_create_cm_pc(cr);
    lemma_pre_leads_to_post_by_controller(spec, simple_reconciler(), input,
        strengthen_next_with_rep_resp_injectivity(resp_msg, req_msg, cr), continue_reconcile(simple_reconciler()),
        pre, post);
}

proof fn lemma_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(resp_msg: Message, req_msg: Message, cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                &&& s.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
            }).leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    let pre = |s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
    };
    let pre_with_name_and_namespace = lift_state(|s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
        &&& resp_is_ok_and_named_and_namespaced(resp_msg)
    });
    let input = (Option::Some(resp_msg), Option::Some(cr.object_ref()));
    let spec = partial_spec_with_invariants_and_assumptions(cr);
    spec_entails_strengthen_next_with_rep_resp_injectivity(resp_msg, req_msg, cr);

    if (resp_is_ok_and_named_and_namespaced(resp_msg)) {
        lemma_ok_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(resp_msg, req_msg, cr);
        leads_to_weaken_temp::<State<SimpleReconcileState>>(spec, pre_with_name_and_namespace, lift_state(reconciler_at_after_create_cm_pc(cr)), lift_state(pre), lift_state(reconciler_at_after_create_cm_pc(cr)));
    } else {
        let post = reconciler_reconcile_error(cr);
        lemma_pre_leads_to_post_by_controller(spec, simple_reconciler(), input,
            strengthen_next_with_rep_resp_injectivity(resp_msg, req_msg, cr), continue_reconcile(simple_reconciler()),
            pre, post);

        // To show that ideal_spec |= error_pc ~> init_pc /\ no_pending_req
        // First, show that always(cr_exists) |= always(cr_key_exists) to get spec |= always(cr_key_exists) using entails_trans.
        // Then we can use lemma_cr_always_exists_entails_reconcile_error_leads_to_reconcile_init_and_no_pending_req.
        implies_preserved_by_always_temp::<State<SimpleReconcileState>>(cr_exists(cr),
            lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref())));
        entails_trans::<State<SimpleReconcileState>>(spec, always(cr_exists(cr)),
            always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref()))));
        lemma_cr_always_exists_entails_reconcile_error_leads_to_reconcile_init_and_no_pending_req(spec,
            simple_reconciler(), cr.object_ref());
        lemma_init_pc_and_no_pending_req_leads_to_after_create_cm_pc(cr);

        // Finally, using leads_to transitivity.
        // 1. spec |= after_get_cr_pc /\ pending_req /\ err_resp_in_flight ~> error_pc ~> init_pc /\ no_pending_req
        // 2. spec |= after_get_cr_pc /\ pending_req /\ err_resp_in_flight ~> init_pc /\ no_pending_req ~> after_create_cm_pc
        leads_to_trans::<State<SimpleReconcileState>>(spec, pre, post,
            reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref()));
        leads_to_trans::<State<SimpleReconcileState>>(spec, pre,
            reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref()),
            reconciler_at_after_create_cm_pc(cr));
    }
}

proof fn spec_entails_strengthen_next_with_rep_resp_injectivity(resp_msg: Message, req_msg: Message, cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_assumptions(cr).entails(
            always(lift_action(strengthen_next_with_rep_resp_injectivity(resp_msg, req_msg, cr)))
        ),
{
    let next_and_invariant = strengthen_next_with_rep_resp_injectivity(resp_msg, req_msg, cr);
    let spec = partial_spec_with_invariants_and_assumptions(cr);
    // First, show spec |= always(inv1)
    let a_to_p_1 = |resp_msg: Message| always(lift_state(at_most_one_resp_matches_req(resp_msg, cr.object_ref())));
    let tla_forall_pred_1 = tla_forall(a_to_p_1);
    assert(spec.entails(tla_forall_pred_1));
    tla_forall_apply::<State<SimpleReconcileState>, Message>(a_to_p_1, resp_msg);
    entails_trans::<State<SimpleReconcileState>>(spec, tla_forall_pred_1,
        always(lift_state(at_most_one_resp_matches_req(resp_msg, cr.object_ref()))));

    // Next, show spec |= always(inv2)
    let a_to_p_2 = |msg| always(lift_state(resp_matches_at_most_one_pending_req(msg, cr.object_ref())));
    let tla_forall_pred_2 = tla_forall(a_to_p_2);
    assert(spec.entails(tla_forall_pred_2));
    tla_forall_apply::<State<SimpleReconcileState>, Message>(a_to_p_2, resp_msg);
    entails_trans::<State<SimpleReconcileState>>(spec, tla_forall_pred_2,
        always(lift_state(resp_matches_at_most_one_pending_req(resp_msg, cr.object_ref()))));

    entails_always_and_n!(spec, lift_action(next(simple_reconciler())),
        lift_state(at_most_one_resp_matches_req(resp_msg, cr.object_ref())),
        lift_state(resp_matches_at_most_one_pending_req(resp_msg, cr.object_ref())),
        lift_state(crash_disabled::<SimpleReconcileState>()));
    temp_pred_equality(lift_action(next_and_invariant),
        lift_action(next(simple_reconciler())).and(lift_state(at_most_one_resp_matches_req(resp_msg, cr.object_ref())))
        .and(lift_state(resp_matches_at_most_one_pending_req(resp_msg, cr.object_ref())))
        .and(lift_state(crash_disabled::<SimpleReconcileState>())));
}

pub proof fn next_and_not_crash_preserves_init_pc_or_reconciler_at_after_get_cr_pc_and_pending_req_in_flight_and_no_resp_in_flight(cr: CustomResourceView, s: State<SimpleReconcileState>, s_prime: State<SimpleReconcileState>)
    requires
        next(simple_reconciler())(s, s_prime), !s.crash_enabled, every_in_flight_msg_has_lower_id_than_chan_manager::<SimpleReconcileState>()(s),
        reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref())(s),
    ensures
        reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref())(s_prime) || reconciler_at_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr)(s_prime),
{
    let pre = reconciler_init_and_no_pending_req(simple_reconciler(), cr.object_ref());
    let post = reconciler_at_after_get_cr_pc_and_exists_pending_req_and_req_in_flight_and_no_resp_in_flight(cr);
    if (!pre(s_prime)) {
        let next_step = choose |step: Step<CustomResourceView>| next_step(simple_reconciler(), s, s_prime, step);
        let input = next_step.get_ControllerStep_0();
        let req_msg = controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr.object_ref()}), s.chan_manager.allocate().1);
        assert(is_controller_get_cr_request_msg(req_msg, cr));
        assert(req_msg.content.get_req_id() == s.chan_manager.cur_chan_id);
        if (exists |resp_msg: Message| {
            &&& #[trigger] s_prime.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        }) {
            let resp_msg = choose |resp_msg: Message| {
                &&& #[trigger] s_prime.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
            };
            assert(s.message_in_flight(resp_msg));
            assert(false);
        }
    }

}

}
