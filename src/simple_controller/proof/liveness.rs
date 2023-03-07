// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::{
    proof::{
        controller_runtime_liveness, controller_runtime_safety, kubernetes_api_liveness,
        kubernetes_api_safety,
    },
    spec::{
        common::*,
        controller::common::{controller_req_msg, ControllerActionInput},
        controller::controller_runtime::{continue_reconcile, end_reconcile, trigger_reconcile},
        controller::state_machine::controller,
        distributed_system::*,
    },
};
use crate::pervasive::*;
use crate::pervasive::{option::*, result::*};
use crate::simple_controller::proof::safety;
use crate::simple_controller::proof::shared::*;
use crate::simple_controller::spec::{
    simple_reconciler,
    simple_reconciler::{simple_reconciler, SimpleReconcileState},
};
use crate::temporal_logic::{defs::*, rules::*};
use builtin::*;
use builtin_macros::*;

verus! {

spec fn match_cr(cr: ResourceObj) -> TempPred<State<SimpleReconcileState>>
    recommends
        cr.key.kind.is_CustomResourceKind(),
{
    lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))
}

spec fn liveness(cr: ResourceObj) -> TempPred<State<SimpleReconcileState>>
    recommends
        cr.key.kind.is_CustomResourceKind(),
{
    lift_state(|s: State<SimpleReconcileState>| s.resource_obj_exists(cr)).leads_to(always(match_cr(cr)))
}

proof fn liveness_proof_forall_cr()
    ensures
        forall |cr: ResourceObj| cr.key.kind.is_CustomResourceKind() ==> #[trigger] sm_spec(simple_reconciler()).entails(liveness(cr)),
{
    assert forall |cr: ResourceObj| cr.key.kind.is_CustomResourceKind() implies #[trigger] sm_spec(simple_reconciler()).entails(liveness(cr)) by {
        liveness_proof(cr);
    };
}

proof fn liveness_proof(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| s.resource_obj_exists(cr))
                .leads_to(always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));
    kubernetes_api_safety::always_res_exists_implies_added_in_flight_or_reconcile_ongoing_or_reconcile_scheduled::<SimpleReconcileState>(simple_reconciler(), cr);

    // Now we have [](cr_exists => cr_added_event_msg_sent \/ reconcile_ongoing \/ reconcile_scheduled)
    // and we need to prove each conclusion leads to []cm_exists
    lemma_cr_added_event_msg_sent_leads_to_cm_always_exists(cr);
    lemma_reconcile_ongoing_leads_to_cm_always_exists(cr);
    lemma_reconcile_idle_and_scheduled_leads_to_cm_always_exists(cr);

    let added_event_in_flight = |s: State<SimpleReconcileState>| s.message_in_flight(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg_content(cr)));
    let reconcile_ongoing = |s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.key);
    let reconcile_idle_and_scheduled = |s: State<SimpleReconcileState>| {
        &&& !s.reconcile_state_contains(cr.key)
        &&& s.reconcile_scheduled_for(cr.key)
    };
    let reconcile_ongoing_or_scheduled = |s: State<SimpleReconcileState>| {
        ||| s.reconcile_state_contains(cr.key)
        ||| s.reconcile_scheduled_for(cr.key)
    };

    // Use or_leads_to_combine_temp to combine the three leads-to formulas
    or_leads_to_combine_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(reconcile_ongoing), lift_state(reconcile_idle_and_scheduled), always(lift_state(cm_exists(cr.key))));
    or_leads_to_combine_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(reconcile_ongoing_or_scheduled), lift_state(added_event_in_flight), always(lift_state(cm_exists(cr.key))));

    // This assertion triggers leads_to_weaken_auto
    assert(sm_spec(simple_reconciler()).entails(
        lift_state(|s: State<SimpleReconcileState>| {
            ||| s.message_in_flight(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg_content(cr)))
            ||| s.reconcile_state_contains(cr.key)
            ||| s.reconcile_scheduled_for(cr.key)
        }).leads_to(always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
    ));
}

proof fn lemma_cr_added_event_msg_sent_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| s.message_in_flight(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg_content(cr))))
                .leads_to(always(lift_state(cm_exists(cr.key))))
        ),
{
    let cr_added_event_msg_sent = |s: State<SimpleReconcileState>| s.message_in_flight(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg_content(cr)));
    let reconcile_ongoing = |s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.key);

    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    lemma_cr_added_event_msg_sent_leads_to_reconcile_ongoing(cr);
    lemma_reconcile_ongoing_leads_to_cm_always_exists(cr);

    leads_to_trans_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(cr_added_event_msg_sent), lift_state(reconcile_ongoing), always(lift_state(cm_exists(cr.key))));

}

proof fn lemma_cr_added_event_msg_sent_leads_to_reconcile_ongoing(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| s.message_in_flight(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg_content(cr))))
                .leads_to(lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.key)))
        ),
{
    let cm = simple_reconciler::subresource_configmap(cr.key);
    let cr_added_event_msg = form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg_content(cr));

    let cr_added_event_msg_sent_and_controller_not_in_reconcile = |s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(cr_added_event_msg)
        &&& !s.reconcile_state_contains(cr.key)
    };
    let cr_added_event_msg_sent_and_reconcile_ongoing = |s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(cr_added_event_msg)
        &&& s.reconcile_state_contains(cr.key)
    };
    let reconcile_ongoing = |s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.key);

    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    // It calls wf1 to get cr_added_event_msg_sent_and_controller_not_in_reconcile ~> reconcile_at_init_pc
    // which also gives us cr_added_event_msg_sent_and_controller_not_in_reconcile ~> reconcile_ongoing by weakening
    lemma_relevant_event_sent_leads_to_init_pc(cr_added_event_msg, cr.key);

    // This lemma gives reconcile_ongoing ~> reconcile_ongoing
    // and also cr_added_event_msg_sent_and_reconcile_ongoing ~> reconcile_ongoing by weakening
    leads_to_self::<State<SimpleReconcileState>>(reconcile_ongoing);

    // Combine the two leads-to above and we will get the postcondition
    or_leads_to_combine::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), cr_added_event_msg_sent_and_controller_not_in_reconcile, cr_added_event_msg_sent_and_reconcile_ongoing, reconcile_ongoing);
}

proof fn lemma_reconcile_ongoing_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.key))
                .leads_to(always(lift_state(cm_exists(cr.key))))
        ),
{
    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    // This proof is also straightforward once we have proved the four following lemmas
    // The four lemmas cover all the possible values of reconcile_pc
    lemma_init_pc_leads_to_cm_always_exists(cr); // reconcile_at_init_pc ~> []cm_exists
    lemma_after_get_cr_pc_leads_to_cm_always_exists(cr); // reconciler_at_after_get_cr_pc ~> []cm_exists
    lemma_after_create_cm_pc_leads_to_cm_always_exists(cr); // reconciler_at_after_create_cm_pc ~> []cm_exists
    lemma_reconcile_done_leads_to_cm_always_exists(cr); // reconciler_reconcile_done ~> []cm_exists
    lemma_reconcile_error_leads_to_cm_always_exists(cr); // reconciler_reconcile_done ~> []cm_exists

    // Now we combine the four cases together
    // and we will get s.reconcile_state_contains(cr.key) ~> []cm_exists
    or_leads_to_combine_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(reconciler_at_init_pc(cr.key)), lift_state(reconciler_at_after_get_cr_pc(cr.key)), always(lift_state(cm_exists(cr.key))));
    or_leads_to_combine_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(reconciler_at_after_create_cm_pc(cr.key)), lift_state(reconciler_reconcile_done(cr.key)), always(lift_state(cm_exists(cr.key))));
    or_leads_to_combine_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()),
        lift_state(|s: State<SimpleReconcileState>| {
            ||| reconciler_at_init_pc(cr.key)(s)
            ||| reconciler_at_after_get_cr_pc(cr.key)(s)
        }),
        lift_state(|s: State<SimpleReconcileState>| {
            ||| reconciler_at_after_create_cm_pc(cr.key)(s)
            ||| reconciler_reconcile_done(cr.key)(s)
        }),
        always(lift_state(cm_exists(cr.key)))
    );
    or_leads_to_combine_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()),
        lift_state(|s: State<SimpleReconcileState>| {
            ||| reconciler_at_init_pc(cr.key)(s)
            ||| reconciler_at_after_get_cr_pc(cr.key)(s)
            ||| reconciler_at_after_create_cm_pc(cr.key)(s)
            ||| reconciler_reconcile_done(cr.key)(s)
        }),
        lift_state(reconciler_reconcile_error(cr.key)),
        always(lift_state(cm_exists(cr.key)))
    );
}

proof fn lemma_init_pc_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_at_init_pc(cr.key))
            .leads_to(always(lift_state(cm_exists(cr.key))))
        ),
{
    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    leads_to_self::<State<SimpleReconcileState>>(reconciler_at_init_pc(cr.key));
    safety::lemma_always_reconcile_init_implies_no_pending_req(cr.key);
    // We get the following asserted leads-to formula by auto weakening the one from leads_to_self
    // with the always-implies formula from lemma_always_reconcile_init_implies_no_pending_req
    // We have to write down this assertion to further trigger leads_to_weaken_auto
    assert(sm_spec(simple_reconciler()).entails(lift_state(reconciler_at_init_pc(cr.key)).leads_to(lift_state(reconciler_at_init_pc_and_no_pending_req(cr.key)))));
    // Get the leads-to formula from lemma_init_pc_leads_to_after_get_cr_pc and connect it with the above asserted one
    lemma_init_pc_leads_to_after_get_cr_pc(cr.key);
    leads_to_trans::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), reconciler_at_init_pc(cr.key), reconciler_at_init_pc_and_no_pending_req(cr.key), reconciler_at_after_get_cr_pc(cr.key));
    // Since we have prove that spec |= reconciler_at_after_get_cr_pc ~> []cm_exists, we will just take a shortcut here
    lemma_after_get_cr_pc_leads_to_cm_always_exists(cr);
    leads_to_trans_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(reconciler_at_init_pc(cr.key)), lift_state(reconciler_at_after_get_cr_pc(cr.key)), always(lift_state(cm_exists(cr.key))));
}

proof fn lemma_after_get_cr_pc_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_at_after_get_cr_pc(cr.key))
                .leads_to(always(lift_state(cm_exists(cr.key))))
        ),
{
    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));
    always_implies_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    safety::lemma_always_reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr.key);

    // TODO: there should be a way to avoid unfolding here using some lemma. Will investigate later
    assert forall |ex| #[trigger] sm_spec(simple_reconciler()).satisfied_by(ex) implies lift_state(reconciler_at_after_get_cr_pc(cr.key)).leads_to(lift_state(reconciler_at_after_create_cm_pc(cr.key))).satisfied_by(ex) by {
        assert forall |i| #[trigger] lift_state(reconciler_at_after_get_cr_pc(cr.key)).satisfied_by(ex.suffix(i)) implies eventually(lift_state(reconciler_at_after_create_cm_pc(cr.key))).satisfied_by(ex.suffix(i)) by {
            instantiate_entailed_always::<State<SimpleReconcileState>>(ex, i, sm_spec(simple_reconciler()), lift_state(safety::reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr.key)));

            let get_cr_req_msg = choose |req_msg: Message| {
                &&& is_controller_get_cr_request_msg(req_msg, cr.key)
                &&& ex.suffix(i).head().reconcile_state_of(cr.key).pending_req_msg == Option::Some(req_msg)
                &&& {
                    ||| #[trigger] ex.suffix(i).head().message_in_flight(req_msg)
                    ||| exists |resp_msg: Message| {
                        &&& #[trigger] ex.suffix(i).head().message_in_flight(resp_msg)
                        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                    }
                }
            };

            if ex.suffix(i).head().message_in_flight(get_cr_req_msg) {
                let pre = |req_msg: Message| reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr.key);
                assert(lift_state(pre(get_cr_req_msg)).satisfied_by(ex.suffix(i)));
                lemma_req_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(get_cr_req_msg, cr.key);
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i, sm_spec(simple_reconciler()), lift_state(pre(get_cr_req_msg)), lift_state(reconciler_at_after_create_cm_pc(cr.key)));
            } else {
                let pre = |req_msg: Message| reconciler_at_after_get_cr_pc_and_pending_req_and_resp_in_flight(req_msg, cr.key);
                assert(lift_state(pre(get_cr_req_msg)).satisfied_by(ex.suffix(i)));
                lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(get_cr_req_msg, cr.key);
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i, sm_spec(simple_reconciler()), lift_state(pre(get_cr_req_msg)), lift_state(reconciler_at_after_create_cm_pc(cr.key)));
            }
        };
    };

    // Since we have prove that spec |= reconciler_at_after_create_cm_pc ~> []cm_exists, we will just take a shortcut here
    lemma_after_create_cm_pc_leads_to_cm_always_exists(cr);
    leads_to_trans_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(reconciler_at_after_get_cr_pc(cr.key)), lift_state(reconciler_at_after_create_cm_pc(cr.key)), always(lift_state(cm_exists(cr.key))));
}

proof fn lemma_after_create_cm_pc_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_at_after_create_cm_pc(cr.key))
                .leads_to(always(lift_state(cm_exists(cr.key))))
        ),
{
    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));
    always_implies_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    safety::lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr.key);

    assert forall |ex| #[trigger] sm_spec(simple_reconciler()).satisfied_by(ex) implies lift_state(reconciler_at_after_create_cm_pc(cr.key)).leads_to(lift_state(cm_exists(cr.key))).satisfied_by(ex) by {
        assert forall |i| #[trigger] lift_state(reconciler_at_after_create_cm_pc(cr.key)).satisfied_by(ex.suffix(i)) implies eventually(lift_state(cm_exists(cr.key))).satisfied_by(ex.suffix(i)) by {
            instantiate_entailed_always::<State<SimpleReconcileState>>(ex, i, sm_spec(simple_reconciler()), lift_state(safety::reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr.key)));

            let create_cm_req_msg = choose |m: Message| {
                #[trigger] is_controller_create_cm_request_msg(m, cr.key)
                && ex.suffix(i).head().reconcile_state_of(cr.key).pending_req_msg == Option::Some(m)
                && (ex.suffix(i).head().message_in_flight(m) || ex.suffix(i).head().resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))
            };

            if ex.suffix(i).head().message_in_flight(create_cm_req_msg) {
                let pre = |msg: Message| reconciler_at_after_create_cm_pc_and_pending_req_and_req_in_flight(msg, cr.key);
                assert(lift_state(pre(create_cm_req_msg)).satisfied_by(ex.suffix(i)));
                let cm = simple_reconciler::subresource_configmap(cr.key);
                kubernetes_api_liveness::lemma_create_req_leads_to_res_exists::<SimpleReconcileState>(simple_reconciler(), create_cm_req_msg, cm);
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i, sm_spec(simple_reconciler()), lift_state(pre(create_cm_req_msg)), lift_state(cm_exists(cr.key)));
            } else {
                leads_to_self(cm_exists(cr.key));
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i, sm_spec(simple_reconciler()), lift_state(cm_exists(cr.key)), lift_state(cm_exists(cr.key)));
            }
        };
    };

    // finally prove stability: spec |= reconciler_at_after_create_cm_pc ~> []cm_exists
    lemma_p_leads_to_cm_always_exists(cr, lift_state(reconciler_at_after_create_cm_pc(cr.key)));
}

proof fn lemma_reconcile_done_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_reconcile_done(cr.key))
            .leads_to(always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    // The key of this proof is that ending step label (Done or Error) will make the reconcile rescheduled
    // (yeah it is not super realistic but it is a good practice to always requeue your reconcile
    // and is one compromise I did in the spec to make it easier to start),
    // and the rescheduled reconcile leads to the init reconcile state,
    // which we have proved leads to cm_exists
    controller_runtime_liveness::lemma_reconcile_done_leads_to_reconcile_init::<SimpleReconcileState>(simple_reconciler(), cr.key);
    lemma_init_pc_leads_to_cm_always_exists(cr);
    leads_to_trans_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(reconciler_reconcile_done(cr.key)), lift_state(reconciler_at_init_pc(cr.key)), always(lift_state(cm_exists(cr.key))));
}

proof fn lemma_reconcile_error_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_reconcile_error(cr.key))
            .leads_to(always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    controller_runtime_liveness::lemma_reconcile_error_leads_to_reconcile_init::<SimpleReconcileState>(simple_reconciler(), cr.key);
    lemma_init_pc_leads_to_cm_always_exists(cr);
    leads_to_trans_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(reconciler_reconcile_error(cr.key)), lift_state(reconciler_at_init_pc(cr.key)), always(lift_state(cm_exists(cr.key))));
}

proof fn lemma_reconcile_idle_and_scheduled_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                &&& !s.reconcile_state_contains(cr.key)
                &&& s.reconcile_scheduled_for(cr.key)
            }).leads_to(always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    let reconcile_idle_and_scheduled = |s: State<SimpleReconcileState>| {
        &&& !s.reconcile_state_contains(cr.key)
        &&& s.reconcile_scheduled_for(cr.key)
    };

    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    controller_runtime_liveness::lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init::<SimpleReconcileState>(simple_reconciler(), cr.key);
    lemma_init_pc_leads_to_cm_always_exists(cr);
    leads_to_trans_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(reconcile_idle_and_scheduled), lift_state(reconciler_at_init_pc(cr.key)), always(lift_state(cm_exists(cr.key))));
}

proof fn lemma_p_leads_to_cm_always_exists(cr: ResourceObj, p: TempPred<State<SimpleReconcileState>>)
    requires
        cr.key.kind.is_CustomResourceKind(),
        sm_spec(simple_reconciler()).entails(
            p.leads_to(lift_state(cm_exists(cr.key)))
        ),
    ensures
        sm_spec(simple_reconciler()).entails(
            p.leads_to(always(lift_state(cm_exists(cr.key))))
        ),
{
    let next_and_invariant = |s: State<SimpleReconcileState>, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& safety::delete_cm_req_msg_not_in_flight(cr.key)(s)
    };

    safety::lemma_delete_cm_req_msg_never_in_flight(cr.key);

    strengthen_next::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()), safety::delete_cm_req_msg_not_in_flight(cr.key), next_and_invariant);
    leads_to_stable_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_action(next_and_invariant), p, lift_state(cm_exists(cr.key)));
}

proof fn lemma_relevant_event_sent_leads_to_init_pc(msg: Message, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                &&& s.message_in_flight(msg)
                &&& msg.dst == HostId::CustomController
                &&& msg.content.is_WatchEvent()
                &&& simple_reconciler::reconcile_trigger(msg) == Option::Some(cr_key)
                &&& !s.reconcile_state_contains(cr_key)
            })
                .leads_to(lift_state(reconciler_at_init_pc_and_no_pending_req(cr_key)))
        ),
{
    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));
    controller_runtime_liveness::lemma_relevant_event_sent_leads_to_reconcile_triggered::<SimpleReconcileState>(simple_reconciler(), msg, cr_key);
}

proof fn lemma_init_pc_leads_to_after_get_cr_pc(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_at_init_pc_and_no_pending_req(cr_key)).leads_to(lift_state(reconciler_at_after_get_cr_pc(cr_key)))
        ),
{
    let pre = reconciler_at_init_pc_and_no_pending_req(cr_key);
    let post = reconciler_at_after_get_cr_pc(cr_key);
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr_key),
    };
    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<SimpleReconcileState>(simple_reconciler(), input, next(simple_reconciler()), continue_reconcile(simple_reconciler()), pre, post);
}

proof fn lemma_req_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg: Message, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr_key))
                .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr_key)))
        ),
{
    let pre = reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr_key);
    let get_cr_resp_msg_sent = |s: State<SimpleReconcileState>| {
        exists |resp_msg: Message| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        }
    };
    let reconciler_at_after_create_cm_pc = reconciler_at_after_create_cm_pc(cr_key);

    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    leads_to_self::<State<SimpleReconcileState>>(pre);

    kubernetes_api_liveness::lemma_get_req_leads_to_some_resp::<SimpleReconcileState>(simple_reconciler(), req_msg, cr_key);

    // Now we have:
    //  spec |= pre ~> reconciler_at_after_get_cr_pc_and_pending_req /\ get_cr_req_in_flight
    //  spec |= get_cr_req_in_flight ~> get_cr_resp_msg_sent
    // By applying leads_to_partial_confluence, we will get spec |= pre ~> reconciler_at_after_get_cr_pc_and_pending_req /\ get_cr_resp_msg_sent
    leads_to_partial_confluence::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()), pre, reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr_key), get_cr_req_in_flight(req_msg, cr_key), get_cr_resp_msg_sent);
    // Now we have all the premise to fire the leads-to formula from lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc
    lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg, cr_key);
    leads_to_trans::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()),
        pre,
        |s| {
            &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr_key)(s)
            &&& get_cr_resp_msg_sent(s)
        },
        reconciler_at_after_create_cm_pc
    );
}

proof fn lemma_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(resp_msg: Message, req_msg: Message, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                &&& s.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr_key)(s)
            }).leads_to(lift_state(reconciler_at_after_create_cm_pc(cr_key)))
        ),
{
    let pre = |s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr_key)(s)
    };
    let post = reconciler_at_after_create_cm_pc(cr_key);
    let input = ControllerActionInput {
        recv: Option::Some(resp_msg),
        scheduled_cr_key: Option::Some(cr_key),
    };

    let next_and_invariant = |s, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& controller_runtime_safety::resp_matches_at_most_one_pending_req(resp_msg, cr_key)(s)
    };

    controller_runtime_safety::lemma_always_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(simple_reconciler(), resp_msg, cr_key);

    strengthen_next::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()), controller_runtime_safety::resp_matches_at_most_one_pending_req(resp_msg, cr_key), next_and_invariant);
    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<SimpleReconcileState>(simple_reconciler(), input, next_and_invariant, continue_reconcile(simple_reconciler()), pre, post);
}

proof fn lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg: Message, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                exists |m: Message| {
                    &&& #[trigger] s.message_in_flight(m)
                    &&& resp_msg_matches_req_msg(m, req_msg)
                }
            }).and(lift_state(reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr_key)))
            .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr_key)))
        ),
{
    let m_to_pre1 = |m: Message| lift_state(|s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(m)
        &&& resp_msg_matches_req_msg(m, req_msg)
    });
    let pre2 = lift_state(reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr_key));
    let post = lift_state(reconciler_at_after_create_cm_pc(cr_key));
    assert forall |msg: Message| #[trigger] sm_spec(simple_reconciler()).entails(m_to_pre1(msg).and(pre2).leads_to(post)) by {
        lemma_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(msg, req_msg, cr_key);
        let pre = lift_state(|s: State<SimpleReconcileState>| {
            &&& s.message_in_flight(msg)
            &&& resp_msg_matches_req_msg(msg, req_msg)
            &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr_key)(s)
        });
        temp_pred_equality::<State<SimpleReconcileState>>(pre, m_to_pre1(msg).and(pre2));
    };
    leads_to_exists_intro::<State<SimpleReconcileState>, Message>(sm_spec(simple_reconciler()), |m| m_to_pre1(m).and(pre2), post);
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

}
