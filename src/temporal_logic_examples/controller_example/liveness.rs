// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_example::safety::*;
use crate::controller_example::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

spec fn sent1_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| state.sent_1_create)
}

spec fn sent2_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| state.sent_2_create)
}

spec fn obj1_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| state.obj_1_exists)
}

spec fn obj2_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| state.obj_2_exists)
}

/*
 * This is just a witness to show that reconcile is enabled by send1_pre_state_pred()
 */

proof fn send1_enabled()
    ensures forall |s: CState| send1_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(reconcile_action_pred()).satisfied_by(s)
{
    assert forall |s: CState| send1_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(reconcile_action_pred()).satisfied_by(s) by {
        if send1_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    sent_1_create: true,
                    messages: s.messages.insert(Message::CreateReq{id: 1}),
                    ..s
                }
            };
            assert(reconcile_action_pred().satisfied_by(witness_action));
        }
    };
}

/*
 * This is just a witness to show that reconcile is enabled by send2_pre_state_pred()
 */
proof fn send2_enabled()
    ensures forall |s: CState| send2_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(reconcile_action_pred()).satisfied_by(s)
{
    assert forall |s: CState| send2_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(reconcile_action_pred()).satisfied_by(s) by {
        if send2_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    sent_2_create: true,
                    messages: s.messages.insert(Message::CreateReq{id: 2}),
                    ..s
                }
            };
            assert(reconcile_action_pred().satisfied_by(witness_action));
        }
    };
}

/*
 * This is just a witness to show that create1 is enabled by create1_pre_state_pred()
 */
proof fn create1_enabled()
    ensures forall |s: CState| create1_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(create1_action_pred()).satisfied_by(s)
{
    assert forall |s: CState| create1_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(create1_action_pred()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                obj_1_exists: true,
                ..s
            }
        };
        assert(create1_action_pred().satisfied_by(witness_action));
    };
}

/*
 * This is just a witness to show that create2 is enabled by create2_pre_state_pred()
 */
proof fn create2_enabled()
    ensures forall |s: CState| create2_pre_state_pred().satisfied_by(s) ==> #[trigger] enabled(create2_action_pred()).satisfied_by(s)
{
    assert forall |s: CState| create2_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(create2_action_pred()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                obj_2_exists: true,
                ..s
            }
        };
        assert(create2_action_pred().satisfied_by(witness_action));
    };
}

proof fn lemma_init_leads_to_obj1()
    ensures
        valid(sm_spec()
            .implies(init_state_pred().lift()
                .leads_to(obj1_state_pred().lift()))),
{
    /*
     * This proof is straightforward:
     * We get each individual leads_to from `wf1` by providing the witness
     * and connect the leads_to together using `leads_to_trans` rule.
     */

    /*
     * `implies_apply_auto` is our old friend that helps us avoid writing `assert forall |ex| ... by {...}`
     */
    implies_apply_auto::<CState>();

    /*
     * `leads_to_weaken_auto` allows us to prove the desired leads_to
     * by proving a equally "strong" leads_to or a "stronger" leads_to
     * that is easier to be proved.
     * It seems that we are abusing this rule in this proof.
     * Hope there is a more efficient way to do this.
     */
    leads_to_weaken_auto::<CState>();

    send1_enabled();
    wf1::<CState>(next_action_pred(), reconcile_action_pred(), send1_pre_state_pred(), create1_pre_state_pred());

    create1_enabled();
    wf1::<CState>(next_action_pred(), create1_action_pred(), create1_pre_state_pred(), obj1_state_pred());

    leads_to_trans::<CState>(send1_pre_state_pred(), create1_pre_state_pred(), obj1_state_pred());
}

proof fn lemma_obj1_and_not_sent2_leads_to_obj2()
    ensures
        valid(sm_spec()
            .implies(obj1_state_pred().lift()
                .and(not(sent2_state_pred().lift()))
                    .leads_to(obj2_state_pred().lift()))),
{
    /*
     * This proof is also straightforward:
     * We get each individual leads_to from `wf1` by providing the witness
     * and connect the leads_to together using `leads_to_trans` rule.
     */

    implies_apply_auto::<CState>();

    leads_to_weaken_auto::<CState>();

    send2_enabled();
    wf1::<CState>(next_action_pred(), reconcile_action_pred(), send2_pre_state_pred(), create2_pre_state_pred());

    create2_enabled();
    wf1::<CState>(next_action_pred(), create2_action_pred(), create2_pre_state_pred(), obj2_state_pred());

    leads_to_trans::<CState>(send2_pre_state_pred(), create2_pre_state_pred(), obj2_state_pred());

    /*
     * Now we have `(s.obj_1_exists /\ ~s.obj_2_exists /\ ~s.sent_2_create) ~> s.obj_2_exists`.
     */
    // assert(valid(sm_spec()
    //     .implies(obj1_state_pred().lift()
    //         .and(not(obj2_state_pred().lift())
    //             .and(not(sent2_state_pred().lift())))
    //                 .leads_to(obj2_state_pred().lift()))));

    /*
     * With `leads_to_assume_not` we can kick out `~s.obj_2_exists`.
     */
    leads_to_assume_not::<CState>(sm_spec(), obj1_state_pred().lift().and(not(sent2_state_pred().lift())), obj2_state_pred().lift());

    /*
     * Should we just continue connecting the leads_to and reach our final goal?
     * Wait... there is a problem:
     * This proof gives us a leads_to starting at `s.obj_1_exists /\ ~s.sent_2_create`,
     * and the previous proof gives us a leads_to ending at `s.obj_1_exists`.
     * Help! Our old friend `leads_to_trans` cannot connect them together!
     *
     * To continue the liveness proof, we need to prove `s.obj_1_exists ~> s.obj_2_exists`.
     * Since we already have `s.obj_1_exists /\ ~s.sent_2_create`,
     * all we need to do is to prove another case:
     * `(s.obj_1_exists /\ s.sent_2_create) ~> s.obj_2_exists`.
     */
}

/*
 * This invariant itself is straightforward.
 * We will use it in the next proof.
 */
proof fn lemma_msg_inv()
    ensures
        valid(sm_spec().implies(always(msg_inv_state_pred().lift())))
{
    implies_apply_auto::<CState>();
    init_invariant::<CState>(init_state_pred(), next_action_pred(), msg_inv_state_pred());
}

proof fn lemma_obj1_and_sent2_leads_to_obj2()
    ensures
        valid(sm_spec()
            .implies(obj1_state_pred().lift()
                .and(sent2_state_pred().lift())
                    .leads_to(obj2_state_pred().lift()))),
{
    /*
     * This proof shows you `(s.obj_1_exists /\ ~s.obj_2_exists /\ s.sent_2_create) ~> s.obj_2_exists`
     * It is interesting and quite complex, so fasten your seat belt.
     */

    implies_apply_auto::<CState>();

    leads_to_weaken_auto::<CState>();

    /*
     * It is hard to even start the first step because `wf1` does not directly give you
     * `(s.obj_1_exists /\ s.sent_2_create) ~> s.obj_2_exists`.
     *
     * But thinking in this way:
     * why does `s.obj_1_exists /\ s.sent_2_create` happen
     * and why does it lead to `s.obj_2_exists`?
     *
     * We have `s.sent_2_create` only after `send2` happens.
     * And `send2` sends `Message::CreateReq{id: 2}`, which enables `create2`.
     * And `create2` is the action that makes `s.obj_2_exists` happen.
     *
     * So we should first get a leads_to by applying `wf1` to `create2`,
     * and try to build a bridge between the precondition of `create2` and `s.sent_2_create`.
     */

    create2_enabled();
    wf1::<CState>(next_action_pred(), create2_action_pred(), create2_pre_state_pred(), obj2_state_pred());

    /*
     * We have the following leads_to from `wf1`: `s.messages.contains(Message::CreateReq{id: 2}) ~> s.obj_2_exists`.
     *
     * But how to make a connection between `s.messages.contains(Message::CreateReq{id: 2})` and `s.sent_2_create`?
     */
    // assert(valid(implies(
    //     sm_spec(),
    //     create2_pre_state_pred().lift().leads_to(obj2_state_pred().lift())
    // )));

    /*
     * OK this is really the most difficult step in the entire proof I think.
     * If you realize that there is a safety property:
     * `s.sent_2_create <==> s.messages.contains(Message::CreateReq{id: 2})}`,
     * then everything goes through now.
     * The safety property, once you know it, is very straightforward.
     * We proved this safety property `msg_inv` in the previous proof.
     *
     * With this safety property, we can weaken the above leads_to to the following one.
     *
     * Thanks `leads_to_weaken_auto` for automatically weakening leads_to for us :)
     */
    assert(valid(sm_spec()
        .implies(sent2_state_pred().lift()
            .and(msg_inv_state_pred().lift())
                .leads_to(obj2_state_pred().lift()))));

    /*
     * Thanks `msg_inv` for giving us `s.sent_2_create`.
     * Now let's get rid of `msg_inv` since it does not appear in our goal :)
     *
     * Our new friend `leads_to_assume` allows us to remove it since `lemma_msg_inv` shows `msg_inv` always holds.
     */
    lemma_msg_inv();
    leads_to_assume::<CState>(sent2_state_pred().lift(), obj2_state_pred().lift(), msg_inv_state_pred().lift());

    /*
     * At this point we have `s.sent_2_create ~> s.obj_2_exists`.
     * `leads_to_weaken_auto` secretly helps us weaken the leads_to to the one we want to prove!
     */
    // assert(valid(sm_spec()
    //     .implies(sent2_state_pred().lift()
    //         .leads_to(obj2_state_pred().lift()))));

    // assert(valid(sm_spec()
    //     .implies(obj1_state_pred().lift()
    //         .and(sent2_state_pred().lift())
    //             .leads_to(obj2_state_pred().lift()))));
}


/*
 * To connect with the above leads_to and further prove
 * `valid(implies(sm_spec(), eventually(obj2_state_pred().lift()))`,
 * now we need to prove
 * `valid(implies(sm_spec(), leads_to(obj1_state_pred().lift(), obj2_state_pred().lift())))`.
 */

proof fn lemma_obj1_leads_to_obj2()
    ensures
        valid(sm_spec()
            .implies(obj1_state_pred().lift()
                .leads_to(obj2_state_pred().lift()))),
{

    implies_apply_auto::<CState>();

    leads_to_weaken_auto::<CState>();

    /*
     * With `lemma_premise1_leads_to_obj2` and `lemma_premise2_leads_to_obj2`,
     * things become much easier here.
     */
    lemma_obj1_and_not_sent2_leads_to_obj2();
    lemma_obj1_and_sent2_leads_to_obj2();

    /*
     * We will combine the two premises together with or using `leads_to_split`.
     */
    leads_to_split::<CState>(sm_spec(), obj1_state_pred().lift(), obj2_state_pred().lift(), sent2_state_pred().lift());
}

proof fn lemma_eventually_obj1()
    ensures
        valid(sm_spec().implies(eventually(obj1_state_pred().lift()))),
{
    /*
     * This proof is simple: just take the leads_to from `lemma_init_leads_to_obj1`
     * and use `leads_to_apply` rule to get eventually from leads_to.
     */

    implies_apply_auto::<CState>();

    lemma_init_leads_to_obj1();

    leads_to_apply::<CState>(init_state_pred(), obj1_state_pred());
}

proof fn lemma_eventually_obj2()
    ensures
        valid(sm_spec().implies(eventually(obj2_state_pred().lift())))
{
    /*
     * This proof is also simple: just take the two leads_to
     * from `lemma_init_leads_to_obj1` and `lemma_obj1_leads_to_obj2`,
     * connect them together with `leads_to_trans` rule
     * and use `leads_to_apply` rule to get eventually from leads_to.
     */

    implies_apply_auto::<CState>();

    lemma_init_leads_to_obj1();

    lemma_obj1_leads_to_obj2();

    leads_to_trans::<CState>(init_state_pred(), obj1_state_pred(), obj2_state_pred());

    leads_to_apply::<CState>(init_state_pred(), obj2_state_pred());
}

proof fn liveness()
    ensures
        valid(sm_spec()
            .implies(eventually(obj1_state_pred().lift().and(obj2_state_pred().lift())))),
{
    /*
     * This proof needs the safety property we proved in safety.rs
     * which says always obj2's existence implies obj1's existence.
     *
     * The proof itself is very intuitive:
     * if you have eventually obj2 exists,
     * and you have always obj2's existence implies obj1's existence,
     * then when obj2 exists, obj1 is also there.
     *
     * We use `always_and_eventually` rule to combine
     * the eventually from `lemma_eventually_obj2` and the always from `safety`
     * to one eventually.
     */

    implies_apply_auto::<CState>();

    lemma_eventually_obj2();
    // assert(valid(implies(sm_spec(), eventually(obj2_state_pred().lift()))));

    safety();
    // assert(valid(implies(sm_spec(), always(order_inv_state_pred().lift()))));

    always_and_eventually::<CState>(order_inv_state_pred().lift(), obj2_state_pred().lift());
    // assert(valid(implies(
    //     sm_spec(),
    //     eventually(and(order_inv_state_pred().lift(), obj2_state_pred().lift()))
    // )));

    /*
     * We get a weaker eventually, which is our goal, from `eventually_weaken`.
     */
    eventually_weaken::<CState>(order_inv_state_pred().lift().and(obj2_state_pred().lift()), obj1_state_pred().lift().and(obj2_state_pred().lift()));
}

}
