// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, custom_resource::*, object::*};
use crate::kubernetes_cluster::{
    proof::{
        controller_runtime_liveness, controller_runtime_safety, kubernetes_api_liveness,
        kubernetes_api_safety,
    },
    spec::{
        controller::common::{controller_req_msg, ControllerActionInput},
        controller::controller_runtime::{continue_reconcile, end_reconcile},
        controller::state_machine::controller,
        distributed_system::*,
        message::*,
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

spec fn cr_exists(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    lift_state(|s: State<SimpleReconcileState>| s.resource_obj_exists(KubernetesObject::CustomResource(cr)))
}

spec fn cr_matched(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref()))
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
    lemma_cr_always_exists_leads_to_reconcile_scheduled(cr);
    lemma_reconcile_scheduled_leads_to_cm_always_exists(cr);
    leads_to_trans_temp(sm_spec(simple_reconciler()), always(cr_exists(cr)), lift_state(|s: State<SimpleReconcileState>| s.reconcile_scheduled_for(cr.object_ref())), always(cr_matched(cr)));
}

proof fn lemma_cr_always_exists_leads_to_reconcile_scheduled(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            always(cr_exists(cr)).leads_to(lift_state(|s: State<SimpleReconcileState>| s.reconcile_scheduled_for(cr.object_ref())))
        ),
{
    let scheduled = lift_state(|s: State<SimpleReconcileState>| s.reconcile_scheduled_for(cr.object_ref()));
    let cr_key_exists = lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref()));
    valid_stable_sm_partial_spec::<SimpleReconcileState>(simple_reconciler());
    controller_runtime_liveness::lemma_true_leads_to_reconcile_scheduled_by_assumption::<SimpleReconcileState>(simple_reconciler(), cr.object_ref());
    unpack_assumption_from_spec::<State<SimpleReconcileState>>(lift_state(init(simple_reconciler())), sm_partial_spec(simple_reconciler()), always(cr_key_exists), scheduled);
    implies_preserved_by_always_temp::<State<SimpleReconcileState>>(cr_exists(cr), cr_key_exists);
    valid_implies_implies_leads_to::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), always(cr_exists(cr)), always(cr_key_exists));
    leads_to_trans_auto(sm_spec(simple_reconciler()));
}

proof fn lemma_reconcile_scheduled_leads_to_cm_always_exists(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| s.reconcile_scheduled_for(cr.object_ref())).leads_to(always(lift_state(cm_exists(cr))))
        ),
{
    lemma_reconcile_idle_and_scheduled_leads_to_cm_always_exists(cr);
    let reconcile_idle_and_scheduled = lift_state(|s: State<SimpleReconcileState>| {
        &&& !s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_scheduled_for(cr.object_ref())
    });
    let reconcile_ongoing_and_scheduled = lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_scheduled_for(cr.object_ref())
    });
    valid_implies_implies_leads_to(sm_spec(simple_reconciler()), reconcile_ongoing_and_scheduled, lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.object_ref())));
    lemma_reconcile_ongoing_leads_to_cm_always_exists(cr);
    leads_to_trans_temp(sm_spec(simple_reconciler()), reconcile_ongoing_and_scheduled, lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.object_ref())), always(lift_state(cm_exists(cr))));
    temp_pred_equality(reconcile_idle_and_scheduled.or(reconcile_ongoing_and_scheduled), lift_state(|s: State<SimpleReconcileState>| s.reconcile_scheduled_for(cr.object_ref())));
    or_leads_to_combine_temp(sm_spec(simple_reconciler()), reconcile_idle_and_scheduled, reconcile_ongoing_and_scheduled, always(lift_state(cm_exists(cr))));
}

#[verifier(external_body)]
proof fn lemma_reconcile_not_ongoing_leads_to_cm_always_exists(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| !s.reconcile_state_contains(cr.object_ref()))
                .leads_to(always(lift_state(cm_exists(cr))))
        ),
{}

#[verifier(external_body)]
proof fn lemma_reconcile_ongoing_leads_to_cm_always_exists(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.object_ref()))
                .leads_to(always(lift_state(cm_exists(cr))))
        ),
{
    lemma_init_pc_leads_to_cm_always_exists(cr);
    lemma_after_get_cr_pc_leads_to_cm_always_exists(cr);
    lemma_after_create_cm_pc_leads_to_cm_always_exists(cr);
}

proof fn lemma_init_pc_leads_to_cm_always_exists(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_at_init_pc(cr))
            .leads_to(always(lift_state(cm_exists(cr))))
        ),
{
    safety::lemma_always_reconcile_init_implies_no_pending_req(cr);
    lemma_init_pc_leads_to_after_get_cr_pc(cr);
    lemma_after_get_cr_pc_leads_to_cm_always_exists(cr);
    leads_to_trans_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));
    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));
}

proof fn lemma_after_get_cr_pc_leads_to_cm_always_exists(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_at_after_get_cr_pc(cr))
                .leads_to(always(lift_state(cm_exists(cr))))
        ),
{
    assert forall |ex| #[trigger] sm_spec(simple_reconciler()).satisfied_by(ex) implies lift_state(reconciler_at_after_get_cr_pc(cr)).leads_to(lift_state(reconciler_at_after_create_cm_pc(cr))).satisfied_by(ex) by {
        safety::lemma_always_reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr);
        assert forall |i| #[trigger] lift_state(reconciler_at_after_get_cr_pc(cr)).satisfied_by(ex.suffix(i)) implies eventually(lift_state(reconciler_at_after_create_cm_pc(cr))).satisfied_by(ex.suffix(i)) by {
            instantiate_entailed_always::<State<SimpleReconcileState>>(ex, i, sm_spec(simple_reconciler()), lift_state(safety::reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr)));
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
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i, sm_spec(simple_reconciler()), lift_state(reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr)), lift_state(reconciler_at_after_create_cm_pc(cr)));
            } else {
                lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg, cr);
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i, sm_spec(simple_reconciler()), lift_state(|s: State<SimpleReconcileState>| {
                    exists |m: Message| {
                        &&& #[trigger] s.message_in_flight(m)
                        &&& resp_msg_matches_req_msg(m, req_msg)
                    }
                }).and(lift_state(reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr))), lift_state(reconciler_at_after_create_cm_pc(cr)));
            }
        }
    }
    lemma_after_create_cm_pc_leads_to_cm_always_exists(cr);
    leads_to_trans_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(reconciler_at_after_get_cr_pc(cr)), lift_state(reconciler_at_after_create_cm_pc(cr)), always(lift_state(cm_exists(cr))));
}

proof fn lemma_after_create_cm_pc_leads_to_cm_always_exists(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_at_after_create_cm_pc(cr))
                .leads_to(always(lift_state(cm_exists(cr))))
        ),
{
    assert forall |ex| #[trigger] sm_spec(simple_reconciler()).satisfied_by(ex) implies
    lift_state(reconciler_at_after_create_cm_pc(cr)).leads_to(lift_state(cm_exists(cr))).satisfied_by(ex) by {
        safety::lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr);
        assert forall |i| #[trigger] lift_state(reconciler_at_after_create_cm_pc(cr)).satisfied_by(ex.suffix(i))
        implies eventually(lift_state(cm_exists(cr))).satisfied_by(ex.suffix(i)) by {
            instantiate_entailed_always::<State<SimpleReconcileState>>(ex, i, sm_spec(simple_reconciler()), lift_state(safety::reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr)));
            let s = ex.suffix(i).head();
            let req_msg = choose |m: Message| {
                (#[trigger] is_controller_create_cm_request_msg(m, cr)
                && s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(m)
                && s.message_in_flight(m))
                || s.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref())
            };
            if (s.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref())) {
                assert(lift_state(cm_exists(cr)).satisfied_by(ex.suffix(i).suffix(0)));
            } else {
                let cm = KubernetesObject::ConfigMap(simple_reconciler::subresource_configmap(cr.object_ref()));
                let pre = |s: State<SimpleReconcileState>| {
                    &&& s.message_in_flight(req_msg) &&& req_msg.dst == HostId::KubernetesAPI &&& req_msg.content.is_create_request() 
                    &&& req_msg.content.get_create_request().obj == cm
                };
                kubernetes_api_liveness::lemma_create_req_leads_to_res_exists::<SimpleReconcileState>(simple_reconciler(), req_msg, cm);
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i, sm_spec(simple_reconciler()), lift_state(pre), lift_state(cm_exists(cr)));
            }
        };
    };
    // finally prove stability: spec |= reconciler_at_after_create_cm_pc ~> []cm_exists
    lemma_p_leads_to_cm_always_exists(cr, lift_state(reconciler_at_after_create_cm_pc(cr)));
}

proof fn lemma_reconcile_idle_and_scheduled_leads_to_cm_always_exists(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                &&& !s.reconcile_state_contains(cr.object_ref())
                &&& s.reconcile_scheduled_for(cr.object_ref())
            }).leads_to(always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref()))))
        ),
{
    let reconcile_idle_and_scheduled = |s: State<SimpleReconcileState>| {
        &&& !s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_scheduled_for(cr.object_ref())
    };

    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    controller_runtime_liveness::lemma_reconcile_idle_and_scheduled_leads_to_reconcile_init::<SimpleReconcileState>(simple_reconciler(), cr.object_ref());
    lemma_init_pc_leads_to_cm_always_exists(cr);
    leads_to_trans_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_state(reconcile_idle_and_scheduled), lift_state(reconciler_at_init_pc(cr)), always(lift_state(cm_exists(cr))));
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
        &&& safety::delete_cm_req_msg_not_in_flight(cr)(s)
    };

    safety::lemma_delete_cm_req_msg_never_in_flight(cr);

    strengthen_next::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()), safety::delete_cm_req_msg_not_in_flight(cr), next_and_invariant);
    leads_to_stable_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_action(next_and_invariant), p, lift_state(cm_exists(cr)));
}

proof fn lemma_init_pc_leads_to_after_get_cr_pc(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_at_init_pc_and_no_pending_req(cr)).leads_to(lift_state(reconciler_at_after_get_cr_pc(cr)))
        ),
{
    let pre = reconciler_at_init_pc_and_no_pending_req(cr);
    let post = reconciler_at_after_get_cr_pc(cr);
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr.object_ref()),
    };
    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<SimpleReconcileState>(simple_reconciler(), input, next(simple_reconciler()), continue_reconcile(simple_reconciler()), pre, post);
}

proof fn lemma_req_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg: Message, cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
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
    let reconciler_at_after_create_cm_pc = reconciler_at_after_create_cm_pc(cr);

    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    leads_to_self::<State<SimpleReconcileState>>(pre);

    kubernetes_api_liveness::lemma_get_req_leads_to_some_resp::<SimpleReconcileState>(simple_reconciler(), req_msg, cr.object_ref());

    // Now we have:
    //  spec |= pre ~> reconciler_at_after_get_cr_pc_and_pending_req /\ get_cr_req_in_flight
    //  spec |= get_cr_req_in_flight ~> get_cr_resp_msg_sent
    // By applying leads_to_partial_confluence, we will get spec |= pre ~> reconciler_at_after_get_cr_pc_and_pending_req /\ get_cr_resp_msg_sent
    leads_to_partial_confluence::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()), pre, reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr), get_cr_req_in_flight(req_msg, cr), get_cr_resp_msg_sent);
    // Now we have all the premise to fire the leads-to formula from lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc
    lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg, cr);
    leads_to_trans::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()),
        pre,
        |s| {
            &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
            &&& get_cr_resp_msg_sent(s)
        },
        reconciler_at_after_create_cm_pc
    );
}

proof fn lemma_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(resp_msg: Message, req_msg: Message, cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
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
    let post = reconciler_at_after_create_cm_pc(cr);
    let input = ControllerActionInput {
        recv: Option::Some(resp_msg),
        scheduled_cr_key: Option::Some(cr.object_ref()),
    };

    let next_and_invariant = |s, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& controller_runtime_safety::resp_matches_at_most_one_pending_req(resp_msg, cr.object_ref())(s)
    };

    controller_runtime_safety::lemma_always_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(simple_reconciler(), resp_msg, cr.object_ref());

    strengthen_next::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()), controller_runtime_safety::resp_matches_at_most_one_pending_req(resp_msg, cr.object_ref()), next_and_invariant);
    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<SimpleReconcileState>(simple_reconciler(), input, next_and_invariant, continue_reconcile(simple_reconciler()), pre, post);
}

proof fn lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg: Message, cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
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
    assert forall |msg: Message| #[trigger] sm_spec(simple_reconciler()).entails(m_to_pre1(msg).and(pre2).leads_to(post)) by {
        lemma_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(msg, req_msg, cr);
        let pre = lift_state(|s: State<SimpleReconcileState>| {
            &&& s.message_in_flight(msg)
            &&& resp_msg_matches_req_msg(msg, req_msg)
            &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
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
