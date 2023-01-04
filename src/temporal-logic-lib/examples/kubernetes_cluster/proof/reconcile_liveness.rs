// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::kubernetes_cluster::{
    proof::{
        controller_runtime_liveness, controller_runtime_safety, kubernetes_api_liveness,
        kubernetes_api_safety, reconcile_safety,
    },
    spec::{common::*, controller, controller::ControllerActionInput, distributed_system::*},
};
use crate::pervasive::{option::*, result::*};
use crate::temporal_logic::*;
use crate::temporal_logic_rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

spec fn liveness_property(cr: ResourceObj) -> TempPred<State>
    recommends
        cr.key.kind.is_CustomResourceKind(),
{
    // This liveness property is a quite simple as a start-off example
    // I will work on stability later...
    lift_state(|s: State| s.resource_obj_exists(cr))
        .leads_to(lift_state(|s: State| s.resource_key_exists(controller::subresource_configmap(cr.key).key)))
}

proof fn liveness_proof_forall_cr()
    ensures
        forall |cr: ResourceObj| cr.key.kind.is_CustomResourceKind() ==> #[trigger] sm_spec().entails(liveness_property(cr)),
{
    assert forall |cr: ResourceObj| cr.key.kind.is_CustomResourceKind() implies #[trigger] sm_spec().entails(liveness_property(cr)) by {
        liveness_proof(cr);
    };
}

proof fn liveness_proof(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| s.resource_obj_exists(cr))
                .leads_to(lift_state(|s: State| s.resource_key_exists(controller::subresource_configmap(cr.key).key)))
        ),
{
    leads_to_weaken_auto::<State>(sm_spec());
    controller_runtime_liveness::lemma_always_cr_exists_implies_added_event_sent(cr);
    lemma_cr_added_event_msg_sent_leads_to_cm_exists(cr);
}

proof fn lemma_cr_added_event_msg_sent_leads_to_cm_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(cr))))
                .leads_to(lift_state(|s: State| s.resource_key_exists(controller::subresource_configmap(cr.key).key)))
        ),
{
    let cr_added_event_msg_sent_and_controller_in_reconcile = |s: State| {
        &&& s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(cr)))
        &&& s.reconcile_state_contains(cr.key)
    };
    let cr_added_event_msg_sent_and_controller_not_in_reconcile = |s: State| {
        &&& s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(cr)))
        &&& !s.reconcile_state_contains(cr.key)
    };
    let cm_exists = |s: State| s.resource_key_exists(controller::subresource_configmap(cr.key).key);

    leads_to_weaken_auto::<State>(sm_spec());

    // You might wonder why do we want to split the cases by whether s.reconcile_state_contains(cr.key) here
    // The reason is that if !s.reconcile_state_contains(cr.key) then we can simply apply wf1 to make progress
    // because cr_added_event_msg_sent_and_controller_not_in_reconcile is basically the precondition of
    // controller's trigger_reconcile action as
    // what lemma_cr_added_event_msg_sent_and_controller_not_in_reconcile_leads_to_cm_exists does
    lemma_cr_added_event_msg_sent_and_controller_not_in_reconcile_leads_to_cm_exists(cr);
    // However, if s.reconcile_state_contains(cr.key) then it becomes very complicated -- it means the controller
    // is currently in reconcile and we need to reason about every reconcile step and prove each step leads to cm_exists
    // which is lemma_cr_added_event_msg_sent_and_controller_in_reconcile_leads_to_cm_exists does
    lemma_cr_added_event_msg_sent_and_controller_in_reconcile_leads_to_cm_exists(cr);

    or_leads_to_combine::<State>(sm_spec(), cr_added_event_msg_sent_and_controller_in_reconcile, cr_added_event_msg_sent_and_controller_not_in_reconcile, cm_exists);
}

proof fn lemma_cr_added_event_msg_sent_and_controller_not_in_reconcile_leads_to_cm_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(cr)))
                &&& !s.reconcile_state_contains(cr.key)
            }).leads_to(lift_state(|s: State| s.resource_key_exists(controller::subresource_configmap(cr.key).key)))
        ),
{
    let cm = controller::subresource_configmap(cr.key);
    let cr_added_event_msg = form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(cr));

    let cr_added_event_msg_sent_and_not_in_reconcile = |s: State| {
        &&& s.message_sent(cr_added_event_msg)
        &&& !s.reconcile_state_contains(cr.key)
    };
    let reconcile_at_init = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::Init
    };
    let cm_exists = |s: State| s.resource_key_exists(cm.key);

    leads_to_weaken_auto::<State>(sm_spec());

    // This proof is rather simple compared to the next one
    // It basically invokes wf1 to get cr_added_event_msg_sent_and_not_in_reconcile ~> reconcile_at_init
    // and then combine it with reconcile_at_init ~> cm_exists from lemma_init_leads_to_cm_exists
    // lemma_init_leads_to_cm_exists does the heavy lifting here
    controller_runtime_liveness::lemma_relevant_event_sent_leads_to_reconcile_triggered(cr_added_event_msg, cr.key);
    lemma_init_leads_to_cm_exists(cr);
    leads_to_trans::<State>(sm_spec(), cr_added_event_msg_sent_and_not_in_reconcile, reconcile_at_init, cm_exists);
}

proof fn lemma_cr_added_event_msg_sent_and_controller_in_reconcile_leads_to_cm_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(cr)))
                &&& s.reconcile_state_contains(cr.key)
            }).leads_to(lift_state(|s: State| s.resource_key_exists(controller::subresource_configmap(cr.key).key)))
        ),
{
    let cm = controller::subresource_configmap(cr.key);

    let reconcile_at_init = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::Init
    };
    let reconcile_at_get_cr_done = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
    };
    let reconcile_at_create_cm_done = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::CreateCMDone
    };
    let reconcile_ended = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& controller::ending_step(s.reconcile_state_of(cr.key).reconcile_step)
    };
    let cm_exists = |s: State| s.resource_key_exists(cm.key);

    leads_to_weaken_auto::<State>(sm_spec());

    // This proof is also straightforward once we have proved the four following lemmas
    // The four lemmas cover all the possible values of controller:ReconcileCoreStep
    lemma_init_leads_to_cm_exists(cr); // reconcile_at_init ~> cm_exists
    lemma_get_cr_done_leads_to_cm_exists(cr); // reconcile_at_get_cr_done ~> cm_exists
    lemma_create_cm_done_leads_to_cm_exists(cr); // reconcile_at_create_cm_done ~> cm_exists
    lemma_reconcile_ended_leads_to_cm_exists(cr); // reconcile_ended ~> cm_exists

    // Now we combine the four cases together
    // and we will get s.reconcile_state_contains(cr.key) ~> cm_exists
    or_leads_to_combine::<State>(sm_spec(), reconcile_at_init, reconcile_at_get_cr_done, cm_exists);
    or_leads_to_combine::<State>(sm_spec(), reconcile_at_create_cm_done, reconcile_ended, cm_exists);
    or_leads_to_combine::<State>(sm_spec(),
        |s: State| {
            ||| reconcile_at_init(s)
            ||| reconcile_at_get_cr_done(s)
        },
        |s: State| {
            ||| reconcile_at_create_cm_done(s)
            ||| reconcile_ended(s)
        },
        cm_exists
    );
    // And leads_to_weaken_auto directly gives us the leads-to formula in the postcondition
    // by prepending s.message_sent(form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(cr)))
    // to s.reconcile_state_contains(cr.key) ~> cm_exists
}

proof fn lemma_init_leads_to_cm_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::Init
            }).leads_to(lift_state(|s: State| s.resource_key_exists(controller::subresource_configmap(cr.key).key)))
        ),
{
    let cm = controller::subresource_configmap(cr.key);

    // Just layout all the state predicates we are going to repeatedly use later since they are so long
    let reconcile_at_init = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::Init
    };
    let reconcile_at_init_and_no_pending_req = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::Init
        &&& s.reconcile_state_of(cr.key).pending_req_msg.is_None()
    };
    let reconcile_at_get_cr_done = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
    };
    let cm_exists = |s: State| s.resource_key_exists(cm.key);

    leads_to_weaken_auto::<State>(sm_spec());

    leads_to_self::<State>(reconcile_at_init);
    controller_runtime_safety::lemma_always_reconcile_init_implies_no_pending_req(cr.key);
    // We get the following asserted leads-to formula by auto weakening the one from leads_to_self
    // with the always-implies formula from lemma_always_reconcile_init_implies_no_pending_req
    // We have to write down this assertion to further trigger leads_to_weaken_auto
    assert(sm_spec().entails(
        lift_state(reconcile_at_init)
            .leads_to(lift_state(reconcile_at_init_and_no_pending_req))
    ));
    // Get the leads-to formula from lemma_init_leads_to_get_cr_step and connect it with the above asserted one
    lemma_init_leads_to_get_cr_step(cr.key);
    leads_to_trans::<State>(sm_spec(), reconcile_at_init, reconcile_at_init_and_no_pending_req, reconcile_at_get_cr_done);
    // Since we have prove that spec |= reconcile_at_get_cr_done ~> cm_exists, we will just take a shortcut here
    lemma_get_cr_done_leads_to_cm_exists(cr);
    leads_to_trans::<State>(sm_spec(), reconcile_at_init, reconcile_at_get_cr_done, cm_exists);
}

proof fn lemma_get_cr_done_leads_to_cm_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
            }).leads_to(lift_state(|s: State| s.resource_key_exists(controller::subresource_configmap(cr.key).key)))
        ),
{
    let get_cr_req_msg = form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr.key})));
    let create_cm_req_msg = form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr.key)));
    let cm = controller::subresource_configmap(cr.key);

    // Just layout all the state predicates we are going to repeatedly use later since they are so long
    let reconcile_at_get_cr_done = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
    };
    let reconcile_at_get_cr_done_and_pending_get_cr_req = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
        &&& s.reconcile_state_of(cr.key).pending_req_msg === Option::Some(get_cr_req_msg)
    };
    let reconcile_at_create_cm_done = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::CreateCMDone
    };
    let get_cr_req_msg_sent = |s: State| s.message_sent(get_cr_req_msg);
    let get_cr_resp_msg_sent = |s: State| {
        exists |resp_msg: Message| {
            &&& #[trigger] s.message_sent(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, get_cr_req_msg)
        }
    };
    let cm_exists = |s: State| s.resource_key_exists(cm.key);

    leads_to_weaken_auto::<State>(sm_spec());

    reconcile_safety::lemma_always_reconcile_get_cr_done_implies_pending_get_cr_req(cr.key);
    leads_to_self::<State>(reconcile_at_get_cr_done);
    // We get the following asserted leads-to formula by auto weakening the one from leads_to_self
    // with the always-implies formula from lemma_always_reconcile_get_cr_done_implies_pending_get_cr_req
    // We have to write down this assertion to further trigger leads_to_weaken_auto
    assert(sm_spec().entails(
        lift_state(reconcile_at_get_cr_done)
            .leads_to(lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
                &&& s.reconcile_state_of(cr.key).pending_req_msg === Option::Some(get_cr_req_msg)
                &&& s.message_sent(get_cr_req_msg)
            }))
    ));
    kubernetes_api_liveness::lemma_get_req_leads_to_some_resp(get_cr_req_msg, cr.key);
    leads_to_trans::<State>(sm_spec(), reconcile_at_get_cr_done, get_cr_req_msg_sent, get_cr_resp_msg_sent);
    // It is quite obvious that get_cr_resp_msg_sent is stable since we never remove a message from the network sent set
    // But we still need to prove it by providing a witness because of "exists" in get_cr_resp_msg_sent
    // Note that we want to prove it is stable because we want to use leads_to_confluence later
    assert forall |s, s_prime: State| get_cr_resp_msg_sent(s) && action_pred_call(next(), s, s_prime) implies get_cr_resp_msg_sent(s_prime) by {
        let msg = choose |m: Message| {
            &&& #[trigger] s.message_sent(m)
            &&& resp_msg_matches_req_msg(m, get_cr_req_msg)
        };
        assert(s_prime.message_sent(msg));
    };
    leads_to_stable::<State>(sm_spec(), next(), reconcile_at_get_cr_done, get_cr_resp_msg_sent);
    // Now we have:
    //  spec |= reconcile_at_get_cr_done ~> reconcile_at_get_cr_done_and_pending_get_cr_req
    //  spec |= reconcile_at_get_cr_done ~> []get_cr_resp_msg_sent
    // And to make more progress, we need to make reconcile_at_get_cr_done_and_pending_get_cr_req and get_cr_resp_msg_sent
    // both true at the same time
    // This is why we use leads_to_confluence here
    leads_to_confluence::<State>(sm_spec(), next(), reconcile_at_get_cr_done, reconcile_at_get_cr_done_and_pending_get_cr_req, get_cr_resp_msg_sent);
    // Now we have all the premise to fire the leads-to formula from lemma_exists_get_resp_msg_sent_and_get_cr_leads_to_create_cm
    lemma_exists_get_resp_msg_sent_and_get_cr_leads_to_create_cm(cr.key);
    leads_to_trans::<State>(sm_spec(),
        reconcile_at_get_cr_done,
        |s| {
            &&& reconcile_at_get_cr_done_and_pending_get_cr_req(s)
            &&& get_cr_resp_msg_sent(s)
        },
        reconcile_at_create_cm_done
    );
    // Since we have prove that spec |= reconcile_at_create_cm_done ~> cm_exists, we will just take a shortcut here
    lemma_create_cm_done_leads_to_cm_exists(cr);
    leads_to_trans::<State>(sm_spec(), reconcile_at_get_cr_done, reconcile_at_create_cm_done, cm_exists);
}

proof fn lemma_create_cm_done_leads_to_cm_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::CreateCMDone
            }).leads_to(lift_state(|s: State| {
                s.resource_key_exists(controller::subresource_configmap(cr.key).key)
            }))
        ),
{
    let create_cm_req_msg = form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr.key)));
    let cm = controller::subresource_configmap(cr.key);

    // Just layout all the state predicates we are going to repeatedly use later since they are so long
    let reconcile_at_create_cm_done = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::CreateCMDone
    };
    let create_cm_req_msg_sent = |s: State| s.message_sent(create_cm_req_msg);
    let cm_exists = |s: State| {
        s.resource_key_exists(cm.key)
    };

    leads_to_weaken_auto::<State>(sm_spec());

    reconcile_safety::lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req(cr.key);
    leads_to_self::<State>(reconcile_at_create_cm_done);
    // We get the following asserted leads-to formula by auto weakening the one from leads_to_self
    // with the always-implies formula from lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req
    // We have to write down this assertion to further trigger leads_to_weaken_auto
    assert(sm_spec().entails(
        lift_state(reconcile_at_create_cm_done)
            .leads_to(lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::CreateCMDone
                &&& s.reconcile_state_of(cr.key).pending_req_msg === Option::Some(create_cm_req_msg)
                &&& s.message_sent(create_cm_req_msg)
            }))
    ));
    // lemma_create_req_leads_to_res_exists gives us spec |= create_cm_req_msg_sent ~> cm_exists
    // and then apply leads_to_trans we are done
    kubernetes_api_liveness::lemma_create_req_leads_to_res_exists(create_cm_req_msg, cm);
    leads_to_trans::<State>(sm_spec(), reconcile_at_create_cm_done, create_cm_req_msg_sent, cm_exists);
}

proof fn lemma_reconcile_ended_leads_to_cm_exists(cr: ResourceObj)
    requires
        cr.key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr.key)
                &&& controller::ending_step(s.reconcile_state_of(cr.key).reconcile_step)
            }).leads_to(lift_state(|s: State| s.resource_key_exists(controller::subresource_configmap(cr.key).key)))
        ),
{
    let cm = controller::subresource_configmap(cr.key);

    let reconcile_ended = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& controller::ending_step(s.reconcile_state_of(cr.key).reconcile_step)
    };
    let reconcile_at_init = |s: State| {
        &&& s.reconcile_state_contains(cr.key)
        &&& s.reconcile_state_of(cr.key).reconcile_step === controller::ReconcileCoreStep::Init
    };
    let cm_exists = |s: State| s.resource_key_exists(cm.key);

    leads_to_weaken_auto::<State>(sm_spec());

    // The key of this proof is that ending step label (Done or Error) will make the reconcile rescheduled
    // (yeah it is not super realistic but it is a good practice to always requeue your reconcile
    // and is one compromise I did in the spec to make it easier to start),
    // and the rescheduled reconcile leads to the init reconcile state,
    // which we have proved leads to cm_exists
    controller_runtime_liveness::lemma_reconcile_ended_leads_to_init(cr.key);
    lemma_init_leads_to_cm_exists(cr);
    leads_to_trans::<State>(sm_spec(), reconcile_ended, reconcile_at_init, cm_exists);
}

proof fn lemma_init_leads_to_get_cr_step(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::Init
                &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
            }).leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
                    &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
                }))
        ),
{
    let pre = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::Init
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    let post = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
        &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
    };
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr_key),
    };
    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller(input, controller::continue_reconcile(), pre, post);
}

proof fn lemma_msg_sent_and_get_cr_leads_to_create_cm(msg: Message, cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            (|m: Message| lift_state(|s: State| {
                &&& s.message_sent(m)
                &&& resp_msg_matches_req_msg(m, form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
            }))(msg).and(lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
                &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
            })).leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::CreateCMDone
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr_key))))
                    &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr_key))))
                }))
        ),
{
    let pre = |s: State| {
        &&& s.message_sent(msg)
        &&& resp_msg_matches_req_msg(msg, form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
    };
    let post = |s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::CreateCMDone
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr_key))))
        &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr_key))))
    };
    let input = ControllerActionInput {
        recv: Option::Some(msg),
        scheduled_cr_key: Option::Some(cr_key),
    };
    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller(input, controller::continue_reconcile(), pre, post);

    let m_to_pre1 = |m: Message| lift_state(|s: State| {
        &&& s.message_sent(m)
        &&& resp_msg_matches_req_msg(m, form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
    });
    let pre2 = lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
    });
    temp_pred_equality::<State>(lift_state(pre), m_to_pre1(msg).and(pre2));
}

proof fn lemma_tla_exists_get_resp_msg_sent_and_get_cr_leads_to_create_cm(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            tla_exists(|m: Message| lift_state(|s: State| {
                &&& s.message_sent(m)
                &&& resp_msg_matches_req_msg(m, form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
            })).and(lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
                &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
            })).leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::CreateCMDone
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr_key))))
                    &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr_key))))
                }))
        ),
{
    let m_to_pre1 = |m: Message| lift_state(|s: State| {
        &&& s.message_sent(m)
        &&& resp_msg_matches_req_msg(m, form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
    });
    let pre2 = lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
    });
    let post = lift_state(|s: State| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::CreateCMDone
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr_key))))
        &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr_key))))
    });
    assert forall |m: Message| #[trigger] sm_spec().entails(m_to_pre1(m).and(pre2).leads_to(post)) by {
        lemma_msg_sent_and_get_cr_leads_to_create_cm(m, cr_key);
    };
    leads_to_exists_intro::<State, Message>(sm_spec(), |m| m_to_pre1(m).and(pre2), post);
    tla_exists_and_equality::<State, Message>(m_to_pre1, pre2);
}

/// How to prove this? This is obvious according to lemma_tla_exists_get_resp_msg_sent_and_get_cr_leads_to_create_cm
/// but I find it difficult to prove tla_exists(|m| lift_state(|s| ...)) === lift_state(|s| exists |m| ...)
#[verifier(external_body)]
proof fn lemma_exists_get_resp_msg_sent_and_get_cr_leads_to_create_cm(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec().entails(
            lift_state(|s: State| {
                exists |m: Message| {
                    &&& #[trigger] s.message_sent(m)
                    &&& resp_msg_matches_req_msg(m, form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
                }
            }).and(lift_state(|s: State| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
                &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
            }))
                .leads_to(lift_state(|s: State| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::CreateCMDone
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr_key))))
                    &&& s.message_sent(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(controller::create_cm_req(cr_key))))
                }))
        ),
{}


// proof fn foo(cr_key: ResourceKey)
// {
//     let p = lift_state(|s: State| {
//         &&& s.reconcile_state_contains(cr_key)
//         &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
//         &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
//     });
//     let q = tla_exists(|m: Message| lift_state(|s: State| {
//         &&& s.message_sent(m)
//         &&& resp_msg_matches_req_msg(m, form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
//     }));
//     assert(sm_spec().entails(always(p.and(not(q)).and(lift_action(next())).implies(later(p))))); // failed
// }

// proof fn foo2(cr_key: ResourceKey)
// {
//     let p = |s: State| {
//         &&& s.reconcile_state_contains(cr_key)
//         &&& s.reconcile_state_of(cr_key).reconcile_step === controller::ReconcileCoreStep::GetCRDone
//         &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
//     };
//     let q = |s: State| exists |m: Message| {
//         &&& #[trigger] s.message_sent(m)
//         &&& resp_msg_matches_req_msg(m, form_msg(HostId::CustomController, HostId::KubernetesAPI, MessageContent::APIRequest(APIRequest::GetRequest(GetRequest{key: cr_key}))))
//     };
//     assert(forall |s, s_prime| p(s) && !q(s) && action_pred_call(next(), s, s_prime) ==> p(s_prime));
// }

// pub proof fn foo3() {
//     let p = lift_state(|s: State| forall |msg: Message| s.message_sent(msg));
//     let q = tla_forall(|msg: Message| lift_state(|s: State| s.message_sent(msg)));
//     assert(valid(p.implies(q)));
//     assert(valid(q.implies(p))); // failed

//     let p2 = lift_state(|s: State| exists |msg: Message| s.message_sent(msg));
//     let q2 = tla_exists(|msg: Message| lift_state(|s: State| s.message_sent(msg)));
//     assert(valid(p2.implies(q2))); // failed
//     assert(valid(q2.implies(p2)));
// }

}
