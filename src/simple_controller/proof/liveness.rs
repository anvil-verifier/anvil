// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::{
    proof::{controller_runtime_liveness, kubernetes_api_liveness, kubernetes_api_safety},
    spec::{
        common::*,
        controller::common::{controller_req_msg, ControllerActionInput},
        controller::controller_runtime::{continue_reconcile, end_reconcile, trigger_reconcile},
        controller::state_machine::controller,
        distributed_system::*,
    },
};
use crate::pervasive::{option::*, result::*};
use crate::simple_controller::proof::safety;
use crate::simple_controller::spec::{simple_reconciler, simple_reconciler::simple_reconciler};
use crate::temporal_logic::{defs::*, rules::*};
use builtin::*;
use builtin_macros::*;

verus! {

spec fn match_cr(cr: ResourceObj) -> TempPred<State>
    recommends
        cr.key.kind.is_CustomResourceKind(),
{
    lift_state(|s: State| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))
}

spec fn liveness(cr: ResourceObj) -> TempPred<State>
    recommends
        cr.key.kind.is_CustomResourceKind(),
{
    lift_state(|s: State| s.resource_obj_exists(cr)).leads_to(always(match_cr(cr)))
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
            lift_state(|s: State| s.resource_obj_exists(cr))
                .leads_to(always(lift_state(|s: State| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    leads_to_weaken_auto::<State>(sm_spec(simple_reconciler()));
    kubernetes_api_safety::lemma_always_res_exists_implies_added_event_sent(simple_reconciler(), cr);
    lemma_cr_added_event_msg_sent_leads_to_cm_always_exists(cr);
}

proof fn lemma_cr_added_event_msg_sent_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(cr))))
                .leads_to(always(lift_state(|s: State| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    let cr_added_event_msg_sent = |s: State| s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(cr)));
    let controller_in_reconcile = |s: State| s.reconcile_state_contains(cr.key);
    let cm_exists = |s: State| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key);

    leads_to_weaken_auto::<State>(sm_spec(simple_reconciler()));

    lemma_cr_added_event_msg_sent_leads_to_controller_in_reconcile(cr);
    lemma_controller_in_reconcile_leads_to_cm_always_exists(cr);

    leads_to_trans_temp::<State>(sm_spec(simple_reconciler()), lift_state(cr_added_event_msg_sent), lift_state(controller_in_reconcile), always(lift_state(cm_exists)));

}

proof fn lemma_cr_added_event_msg_sent_leads_to_controller_in_reconcile(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(cr))))
                .leads_to(lift_state(|s: State| s.reconcile_state_contains(cr.key)))
        ),
{
    let cm = simple_reconciler::subresource_configmap(cr.key);
    let cr_added_event_msg = form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(cr));

    let cr_added_event_msg_sent_and_controller_not_in_reconcile = |s: State| {
        &&& s.message_sent(cr_added_event_msg)
        &&& !s.reconcile_state_contains(cr.key)
    };
    let cr_added_event_msg_sent_and_controller_in_reconcile = |s: State| {
        &&& s.message_sent(cr_added_event_msg)
        &&& s.reconcile_state_contains(cr.key)
    };
    let controller_in_reconcile = |s: State| s.reconcile_state_contains(cr.key);

    leads_to_weaken_auto::<State>(sm_spec(simple_reconciler()));

    // It calls wf1 to get cr_added_event_msg_sent_and_controller_not_in_reconcile ~> reconcile_at_init_pc
    // which also gives us cr_added_event_msg_sent_and_controller_not_in_reconcile ~> controller_in_reconcile by weakening
    lemma_relevant_event_sent_leads_to_init_pc(cr_added_event_msg, cr.key);

    // This lemma gives controller_in_reconcile ~> controller_in_reconcile
    // and also cr_added_event_msg_sent_and_controller_in_reconcile ~> controller_in_reconcile by weakening
    leads_to_self::<State>(controller_in_reconcile);

    // Combine the two leads-to above and we will get the postcondition
    or_leads_to_combine::<State>(sm_spec(simple_reconciler()), cr_added_event_msg_sent_and_controller_not_in_reconcile, cr_added_event_msg_sent_and_controller_in_reconcile, controller_in_reconcile);
}

proof fn lemma_controller_in_reconcile_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| s.reconcile_state_contains(cr.key))
                .leads_to(always(lift_state(|s: State| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    let cm = simple_reconciler::subresource_configmap(cr.key);

    let reconcile_at_init_pc = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::init_pc()
    };
    let reconciler_at_after_get_cr_pc = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
    };
    let reconciler_at_after_create_cm_pc = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
    };
    let reconciler_reconcile_done = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& (simple_reconciler().reconcile_done)(s.reconcile_state_of(cr.key).local_state)
    };
    let cm_exists = |s: State| s.resource_key_exists(cm.key);

    leads_to_weaken_auto::<State>(sm_spec(simple_reconciler()));

    // This proof is also straightforward once we have proved the four following lemmas
    // The four lemmas cover all the possible values of reconcile_pc
    lemma_init_pc_leads_to_cm_always_exists(cr); // reconcile_at_init_pc ~> []cm_exists
    lemma_after_get_cr_pc_leads_to_cm_always_exists(cr); // reconciler_at_after_get_cr_pc ~> []cm_exists
    lemma_after_create_cm_pc_leads_to_cm_always_exists(cr); // reconciler_at_after_create_cm_pc ~> []cm_exists
    lemma_reconcile_done_leads_to_cm_always_exists(cr); // reconciler_reconcile_done ~> []cm_exists

    // Now we combine the four cases together
    // and we will get s.reconcile_state_contains(cr.key) ~> []cm_exists
    or_leads_to_combine_temp::<State>(sm_spec(simple_reconciler()), lift_state(reconcile_at_init_pc), lift_state(reconciler_at_after_get_cr_pc), always(lift_state(cm_exists)));
    or_leads_to_combine_temp::<State>(sm_spec(simple_reconciler()), lift_state(reconciler_at_after_create_cm_pc), lift_state(reconciler_reconcile_done), always(lift_state(cm_exists)));
    or_leads_to_combine_temp::<State>(sm_spec(simple_reconciler()),
        lift_state(|s: State| {
            ||| reconcile_at_init_pc(s)
            ||| reconciler_at_after_get_cr_pc(s)
        }),
        lift_state(|s: State| {
            ||| reconciler_at_after_create_cm_pc(s)
            ||| reconciler_reconcile_done(s)
        }),
        always(lift_state(cm_exists))
    );
}

proof fn lemma_init_pc_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::init_pc()
            }).leads_to(always(lift_state(|s: State| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    let cm = simple_reconciler::subresource_configmap(cr.key);

    // Just layout all the state predicates we are going to repeatedly use later since they are so long
    let reconcile_at_init_pc = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::init_pc()
    };
    let reconcile_at_init_pc_and_no_pending_req = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::init_pc()
        &&& s.reconcile_state_of(cr.key).pending_req_msg.is_None()
    };
    let reconciler_at_after_get_cr_pc = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
    };
    let cm_exists = |s: State| s.resource_key_exists(cm.key);

    leads_to_weaken_auto::<State>(sm_spec(simple_reconciler()));

    leads_to_self::<State>(reconcile_at_init_pc);
    safety::lemma_always_reconcile_init_implies_no_pending_req(cr.key);
    // We get the following asserted leads-to formula by auto weakening the one from leads_to_self
    // with the always-implies formula from lemma_always_reconcile_init_implies_no_pending_req
    // We have to write down this assertion to further trigger leads_to_weaken_auto
    assert(sm_spec(simple_reconciler()).entails(
        lift_state(reconcile_at_init_pc)
            .leads_to(lift_state(reconcile_at_init_pc_and_no_pending_req))
    ));
    // Get the leads-to formula from lemma_init_pc_leads_to_after_get_cr_pc and connect it with the above asserted one
    lemma_init_pc_leads_to_after_get_cr_pc(cr.key);
    leads_to_trans::<State>(sm_spec(simple_reconciler()), reconcile_at_init_pc, reconcile_at_init_pc_and_no_pending_req, reconciler_at_after_get_cr_pc);
    // Since we have prove that spec |= reconciler_at_after_get_cr_pc ~> []cm_exists, we will just take a shortcut here
    lemma_after_get_cr_pc_leads_to_cm_always_exists(cr);
    leads_to_trans_temp::<State>(sm_spec(simple_reconciler()), lift_state(reconcile_at_init_pc), lift_state(reconciler_at_after_get_cr_pc), always(lift_state(cm_exists)));
}

proof fn lemma_after_get_cr_pc_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
            }).leads_to(always(lift_state(|s: State| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    let get_cr_req_msg = controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr.key}));
    let create_cm_req_msg = controller_req_msg(simple_reconciler::create_cm_req(cr.key));
    let cm = simple_reconciler::subresource_configmap(cr.key);

    // Just layout all the state predicates we are going to repeatedly use later since they are so long
    let reconciler_at_after_get_cr_pc = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
    };
    let reconciler_at_after_get_cr_pc_and_pending_get_cr_req = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr.key).pending_req_msg === Option::Some(get_cr_req_msg)
    };
    let reconciler_at_after_create_cm_pc = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
    };
    let get_cr_req_msg_sent = |s: State| s.message_sent(get_cr_req_msg);
    let get_cr_resp_msg_sent = |s: State| {
        exists |resp_msg: Message| {
            &&& #[trigger] s.message_sent(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, get_cr_req_msg)
        }
    };
    let cm_exists = |s: State| s.resource_key_exists(cm.key);

    leads_to_weaken_auto::<State>(sm_spec(simple_reconciler()));

    safety::lemma_always_reconcile_get_cr_done_implies_pending_get_cr_req(cr.key);
    leads_to_self::<State>(reconciler_at_after_get_cr_pc);
    // We get the following asserted leads-to formula by auto weakening the one from leads_to_self
    // with the always-implies formula from lemma_always_reconcile_get_cr_done_implies_pending_get_cr_req
    // We have to write down this assertion to further trigger leads_to_weaken_auto
    assert(sm_spec(simple_reconciler()).entails(
        lift_state(reconciler_at_after_get_cr_pc)
            .leads_to(lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
                &&& s.reconcile_state_of(cr.key).pending_req_msg === Option::Some(get_cr_req_msg)
                &&& s.message_sent(get_cr_req_msg)
            }))
    ));
    kubernetes_api_liveness::lemma_get_req_leads_to_some_resp(simple_reconciler(), get_cr_req_msg, cr.key);
    leads_to_trans::<State>(sm_spec(simple_reconciler()), reconciler_at_after_get_cr_pc, get_cr_req_msg_sent, get_cr_resp_msg_sent);
    // It is quite obvious that get_cr_resp_msg_sent is stable since we never remove a message from the network sent set
    // But we still need to prove it by providing a witness because of "exists" in get_cr_resp_msg_sent
    // Note that we want to prove it is stable because we want to use leads_to_confluence later
    assert forall |s, s_prime: State| get_cr_resp_msg_sent(s) && #[trigger] next(simple_reconciler())(s, s_prime) implies get_cr_resp_msg_sent(s_prime) by {
        let msg = choose |m: Message| {
            &&& #[trigger] s.message_sent(m)
            &&& resp_msg_matches_req_msg(m, get_cr_req_msg)
        };
        assert(s_prime.message_sent(msg));
    };
    leads_to_stable::<State>(sm_spec(simple_reconciler()), next(simple_reconciler()), reconciler_at_after_get_cr_pc, get_cr_resp_msg_sent);
    // Now we have:
    //  spec |= reconciler_at_after_get_cr_pc ~> reconciler_at_after_get_cr_pc_and_pending_get_cr_req
    //  spec |= reconciler_at_after_get_cr_pc ~> []get_cr_resp_msg_sent
    // And to make more progress, we need to make reconciler_at_after_get_cr_pc_and_pending_get_cr_req and get_cr_resp_msg_sent
    // both true at the same time
    // This is why we use leads_to_confluence here
    leads_to_confluence::<State>(sm_spec(simple_reconciler()), next(simple_reconciler()), reconciler_at_after_get_cr_pc, reconciler_at_after_get_cr_pc_and_pending_get_cr_req, get_cr_resp_msg_sent);
    // Now we have all the premise to fire the leads-to formula from lemma_exists_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc
    lemma_exists_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(cr.key);
    leads_to_trans::<State>(sm_spec(simple_reconciler()),
        reconciler_at_after_get_cr_pc,
        |s| {
            &&& reconciler_at_after_get_cr_pc_and_pending_get_cr_req(s)
            &&& get_cr_resp_msg_sent(s)
        },
        reconciler_at_after_create_cm_pc
    );
    // Since we have prove that spec |= reconciler_at_after_create_cm_pc ~> []cm_exists, we will just take a shortcut here
    lemma_after_create_cm_pc_leads_to_cm_always_exists(cr);
    leads_to_trans_temp::<State>(sm_spec(simple_reconciler()), lift_state(reconciler_at_after_get_cr_pc), lift_state(reconciler_at_after_create_cm_pc), always(lift_state(cm_exists)));
}

proof fn lemma_after_create_cm_pc_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
            }).leads_to(always(lift_state(|s: State| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    let create_cm_req_msg = controller_req_msg(simple_reconciler::create_cm_req(cr.key));
    let cm = simple_reconciler::subresource_configmap(cr.key);

    // Just layout all the state predicates we are going to repeatedly use later since they are so long
    let reconciler_at_after_create_cm_pc = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
    };
    let create_cm_req_msg_sent = |s: State| s.message_sent(create_cm_req_msg);
    let cm_exists = |s: State| {
        s.resource_key_exists(cm.key)
    };

    leads_to_weaken_auto::<State>(sm_spec(simple_reconciler()));

    safety::lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req(cr.key);
    leads_to_self::<State>(reconciler_at_after_create_cm_pc);
    // We get the following asserted leads-to formula by auto weakening the one from leads_to_self
    // with the always-implies formula from lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req
    // We have to write down this assertion to further trigger leads_to_weaken_auto
    assert(sm_spec(simple_reconciler()).entails(
        lift_state(reconciler_at_after_create_cm_pc)
            .leads_to(lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
                &&& s.reconcile_state_of(cr.key).pending_req_msg === Option::Some(create_cm_req_msg)
                &&& s.message_sent(create_cm_req_msg)
            }))
    ));
    // lemma_create_req_leads_to_res_exists gives us spec |= create_cm_req_msg_sent ~> cm_exists
    // and then apply leads_to_trans to get spec |= reconciler_at_after_create_cm_pc ~> cm_exists
    kubernetes_api_liveness::lemma_create_req_leads_to_res_exists(simple_reconciler(), create_cm_req_msg, cm);
    leads_to_trans::<State>(sm_spec(simple_reconciler()), reconciler_at_after_create_cm_pc, create_cm_req_msg_sent, cm_exists);

    // finally prove stability: spec |= reconciler_at_after_create_cm_pc ~> []cm_exists
    lemma_p_leads_to_cm_always_exists(cr, lift_state(reconciler_at_after_create_cm_pc));
}

proof fn lemma_reconcile_done_leads_to_cm_always_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& (simple_reconciler().reconcile_done)(s.reconcile_state_of(cr.key).local_state)
            }).leads_to(always(lift_state(|s: State| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    let cm = simple_reconciler::subresource_configmap(cr.key);

    let reconciler_reconcile_done = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& (simple_reconciler().reconcile_done)(s.reconcile_state_of(cr.key).local_state)
    };
    let reconcile_at_init_pc = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).local_state.reconcile_pc === simple_reconciler::init_pc()
    };
    let cm_exists = |s: State| s.resource_key_exists(cm.key);

    leads_to_weaken_auto::<State>(sm_spec(simple_reconciler()));

    // The key of this proof is that ending step label (Done or Error) will make the reconcile rescheduled
    // (yeah it is not super realistic but it is a good practice to always requeue your reconcile
    // and is one compromise I did in the spec to make it easier to start),
    // and the rescheduled reconcile leads to the init reconcile state,
    // which we have proved leads to cm_exists
    controller_runtime_liveness::lemma_reconcile_done_leads_to_reconcile_triggered(simple_reconciler(), cr.key);
    lemma_init_pc_leads_to_cm_always_exists(cr);
    leads_to_trans_temp::<State>(sm_spec(simple_reconciler()), lift_state(reconciler_reconcile_done), lift_state(reconcile_at_init_pc), always(lift_state(cm_exists)));
}

proof fn lemma_p_leads_to_cm_always_exists(cr: ResourceObj, p: TempPred<State>)
    requires
        cr.key.kind.is_CustomResourceKind(),
        sm_spec(simple_reconciler()).entails(
            p.leads_to(lift_state(|s: State| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key)))
        ),
    ensures
        sm_spec(simple_reconciler()).entails(
            p.leads_to(always(lift_state(|s: State| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.key).key))))
        ),
{
    let cm = simple_reconciler::subresource_configmap(cr.key);

    let cm_exists = |s: State| s.resource_key_exists(cm.key);
    let delete_cm_req_msg_not_sent = |s: State| !exists |m: Message| {
        &&& #[trigger] s.message_sent(m)
        &&& m.dst === HostId::KubernetesAPI
        &&& m.is_delete_request()
        &&& m.get_delete_request().key === simple_reconciler::subresource_configmap(cr.key).key
    };
    safety::lemma_delete_cm_req_msg_never_sent(cr.key);
    let next_and_invariant = |s: State, s_prime: State| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& delete_cm_req_msg_not_sent(s)
    };

    entails_and_temp::<State>(sm_spec(simple_reconciler()), always(lift_action(next(simple_reconciler()))), always(lift_state(delete_cm_req_msg_not_sent)));
    always_and_equality::<State>(lift_action(next(simple_reconciler())), lift_state(delete_cm_req_msg_not_sent));
    temp_pred_equality::<State>(lift_action(next(simple_reconciler())).and(lift_state(delete_cm_req_msg_not_sent)), lift_action(next_and_invariant));
    leads_to_stable_temp::<State>(sm_spec(simple_reconciler()), lift_action(next_and_invariant), p, lift_state(cm_exists));
}

proof fn lemma_relevant_event_sent_leads_to_init_pc(msg: Message, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| {
                &&& s.message_sent(msg)
                &&& msg.dst === HostId::CustomController
                &&& msg.content.is_WatchEvent()
                &&& simple_reconciler::reconcile_trigger(msg) === Option::Some(cr_key)
                &&& !s.reconcile_state_contains(cr_key)
            })
                .leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
                }))
        ),
{
    leads_to_weaken_auto::<State>(sm_spec(simple_reconciler()));
    controller_runtime_liveness::lemma_relevant_event_sent_leads_to_reconcile_triggered(simple_reconciler(), msg, cr_key);
}

proof fn lemma_init_pc_leads_to_after_get_cr_pc(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
                &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
            }).leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
                    &&& s.message_sent(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
                }))
        ),
{
    let pre = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    let post = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
        &&& s.message_sent(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
    };
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr_key),
    };
    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller(simple_reconciler(), input, continue_reconcile(simple_reconciler()), pre, post);
}

proof fn lemma_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(msg: Message, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            (|m: Message| lift_state(|s: State| {
                &&& s.message_sent(m)
                &&& resp_msg_matches_req_msg(m, controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
            }))(msg).and(lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
                &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
            })).leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
                    &&& s.message_sent(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
                }))
        ),
{
    let pre = |s: State| {
        &&& s.message_sent(msg)
        &&& resp_msg_matches_req_msg(msg, controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
    };
    let post = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
        &&& s.message_sent(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
    };
    let input = ControllerActionInput {
        recv: Option::Some(msg),
        scheduled_cr_key: Option::Some(cr_key),
    };
    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller(simple_reconciler(), input, continue_reconcile(simple_reconciler()), pre, post);

    let m_to_pre1 = |m: Message| lift_state(|s: State| {
        &&& s.message_sent(m)
        &&& resp_msg_matches_req_msg(m, controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
    });
    let pre2 = lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
    });
    temp_pred_equality::<State>(lift_state(pre), m_to_pre1(msg).and(pre2));
}

proof fn lemma_exists_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State| {
                exists |m: Message| {
                    &&& #[trigger] s.message_sent(m)
                    &&& resp_msg_matches_req_msg(m, controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
                }
            }).and(lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
                &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
            })).leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
                    &&& s.message_sent(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
                }))
        ),
{
    let m_to_pre1 = |m: Message| lift_state(|s: State| {
        &&& s.message_sent(m)
        &&& resp_msg_matches_req_msg(m, controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
    });
    let pre2 = lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
    });
    let post = lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
        &&& s.message_sent(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
    });
    assert forall |m: Message| #[trigger] sm_spec(simple_reconciler()).entails(m_to_pre1(m).and(pre2).leads_to(post)) by {
        lemma_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(m, cr_key);
    };
    leads_to_exists_intro::<State, Message>(sm_spec(simple_reconciler()), |m| m_to_pre1(m).and(pre2), post);
    tla_exists_and_equality::<State, Message>(m_to_pre1, pre2);

    // This is very tedious proof to show exists_m_to_pre1 === tla_exists(m_to_pre1)
    // I hope we can encapsulate this as a lemma
    let exists_m_to_pre1 = lift_state(|s: State| {
        exists |m: Message| {
            &&& #[trigger] s.message_sent(m)
            &&& resp_msg_matches_req_msg(m, controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
        }
    });
    assert forall |ex| #[trigger] exists_m_to_pre1.satisfied_by(ex) implies tla_exists(m_to_pre1).satisfied_by(ex) by {
        let m = choose |m: Message| {
            &&& #[trigger] ex.head().message_sent(m)
            &&& resp_msg_matches_req_msg(m, controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
        };
        assert(m_to_pre1(m).satisfied_by(ex));
    };
    temp_pred_equality::<State>(exists_m_to_pre1, tla_exists(m_to_pre1));
}

}
