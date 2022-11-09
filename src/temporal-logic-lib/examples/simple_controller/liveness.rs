// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::simple_controller::safety::*;
use crate::examples::simple_controller::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

spec fn sent1() -> StatePred<CState> {
    |s: CState| s.sent_1_create
}

spec fn sent2() -> StatePred<CState> {
    |s: CState| s.sent_2_create
}

spec fn obj1_exists() -> StatePred<CState> {
    |s: CState| s.obj_1_exists
}

spec fn obj2_exists() -> StatePred<CState> {
    |s: CState| s.obj_2_exists
}

spec fn obj1_exists_and_not_sent2() -> StatePred<CState> {
    |s: CState| s.obj_1_exists && !s.sent_2_create
}

proof fn lemma_init_leads_to_obj1_exists()
    ensures
        sm_spec().entails(
            lift_state(init())
                .leads_to(lift_state(obj1_exists()))
        ),
{
    /*
     * This proof is straightforward:
     * We get each individual leads_to from `wf1` by providing the witness
     * and connect the leads_to together using `leads_to_trans` rule.
     */

    /*
     * `leads_to_weaken_lite_auto` allows us to prove the desired leads_to
     * by proving a equally "strong" leads_to or a "stronger" leads_to
     * that is easier to be proved.
     * It seems that we are abusing this rule in this proof.
     * Hope there is a more efficient way to do this.
     */
    leads_to_weaken_lite_auto::<CState>(sm_spec());

    send1_enabled();
    wf1::<CState>(sm_spec(), next(), reconcile(), send1_pre(), create1_pre());

    create1_enabled();
    wf1::<CState>(sm_spec(), next(), create1(), create1_pre(), obj1_exists());

    leads_to_trans::<CState>(sm_spec(), send1_pre(), create1_pre(), obj1_exists());
}

proof fn lemma_obj1_exists_and_not_sent2_leads_to_obj2_exists()
    ensures
        sm_spec().entails(
            lift_state(obj1_exists())
                .and(not(lift_state(sent2())))
                    .leads_to(lift_state(obj2_exists()))
        ),
{
    /*
     * This proof is also straightforward:
     * We get each individual leads_to from `wf1` by providing the witness
     * and connect the leads_to together using `leads_to_trans` rule.
     */

    leads_to_weaken_lite_auto::<CState>(sm_spec());

    send2_enabled();
    wf1::<CState>(sm_spec(), next(), reconcile(), send2_pre(), create2_pre());

    create2_enabled();
    wf1::<CState>(sm_spec(), next(), create2(), create2_pre(), obj2_exists());

    leads_to_trans::<CState>(sm_spec(), send2_pre(), create2_pre(), obj2_exists());

    /*
     * Now we have `(s.obj_1_exists /\ ~s.obj_2_exists /\ ~s.sent_2_create) ~> s.obj_2_exists`.
     */
    // assert(sm_spec().entails(
    //     lift_state(obj1_exists())
    //         .and(not(lift_state(obj2_exists()))
    //             .and(not(lift_state(sent2()))))
    //                 .leads_to(lift_state(obj2_exists()))
    // ));

    /*
     * With `leads_to_assume_not` we can kick out `~s.obj_2_exists`.
     */
    leads_to_assume_not::<CState>(sm_spec(), obj1_exists_and_not_sent2(), obj2_exists());

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
        sm_spec().entails(
            always(lift_state(msg_inv()))
        ),
{
    init_invariant::<CState>(sm_spec(), init(), next(), msg_inv());
}

proof fn lemma_obj1_exists_and_sent2_leads_to_obj2_exists()
    ensures
        sm_spec().entails(
            lift_state(obj1_exists())
                .and(lift_state(sent2()))
                    .leads_to(lift_state(obj2_exists()))
        ),
{
    /*
     * This proof shows you `(s.obj_1_exists /\ ~s.obj_2_exists /\ s.sent_2_create) ~> s.obj_2_exists`
     * It is interesting and quite complex, so fasten your seat belt.
     */

    leads_to_weaken_lite_auto::<CState>(sm_spec());

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
    wf1::<CState>(sm_spec(), next(), create2(), create2_pre(), obj2_exists());

    /*
     * We have the following leads_to from `wf1`: `s.messages.contains(Message::CreateReq{id: 2}) ~> s.obj_2_exists`.
     *
     * But how to make a connection between `s.messages.contains(Message::CreateReq{id: 2})` and `s.sent_2_create`?
     */

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
     * Thanks `leads_to_weaken_lite_auto` for automatically weakening leads_to for us :)
     */
    assert(sm_spec().entails(
        lift_state(sent2())
            .and(lift_state(msg_inv()))
                .leads_to(lift_state(obj2_exists()))
    ));

    /*
     * Thanks `msg_inv` for giving us `s.sent_2_create`.
     * Now let's get rid of `msg_inv` since it does not appear in our goal :)
     *
     * Our new friend `leads_to_assume` allows us to remove it since `lemma_msg_inv` shows `msg_inv` always holds.
     */
    lemma_msg_inv();
    leads_to_assume::<CState>(sm_spec(), sent2(), obj2_exists(), msg_inv());

    /*
     * At this point we have `s.sent_2_create ~> s.obj_2_exists`.
     * `leads_to_weaken_lite_auto` secretly helps us weaken the leads_to to the one we want to prove!
     */
}


/*
 * To connect with the above leads_to and further prove
 * `sm_spec().entails(eventually(lift_state(obj2_exists())))`,
 * now we need to prove
 * `sm_spec().entails(leads_to(lift_state(obj1_exists()), lift_state(obj2_exists())))`.
 */

proof fn lemma_obj1_exists_leads_to_obj2_exists()
    ensures
        sm_spec().entails(
            lift_state(obj1_exists())
                .leads_to(lift_state(obj2_exists()))
        ),
{
    leads_to_weaken_lite_auto::<CState>(sm_spec());

    /*
     * With `lemma_premise1_leads_to_obj2_exists` and `lemma_premise2_leads_to_obj2_exists`,
     * things become much easier here.
     */
    lemma_obj1_exists_and_not_sent2_leads_to_obj2_exists();
    lemma_obj1_exists_and_sent2_leads_to_obj2_exists();

    /*
     * We will combine the two premises together with or using `leads_to_combine`.
     */
    leads_to_combine::<CState>(sm_spec(), obj1_exists(), obj2_exists(), sent2());
}

proof fn lemma_eventually_obj1_exists()
    ensures
        sm_spec().entails(eventually(lift_state(obj1_exists()))),
{
    /*
     * This proof is simple: just take the leads_to from `lemma_init_leads_to_obj1_exists`
     * and use `leads_to_apply` rule to get eventually from leads_to.
     */

    lemma_init_leads_to_obj1_exists();

    leads_to_apply::<CState>(sm_spec(), init(), obj1_exists());
}

proof fn lemma_eventually_obj2_exits()
    ensures
        sm_spec().entails(eventually(lift_state(obj2_exists()))),
{
    /*
     * This proof is also simple: just take the two leads_to
     * from `lemma_init_leads_to_obj1_exists` and `lemma_obj1_exists_leads_to_obj2_exists`,
     * connect them together with `leads_to_trans` rule
     * and use `leads_to_apply` rule to get eventually from leads_to.
     */

    lemma_init_leads_to_obj1_exists();

    lemma_obj1_exists_leads_to_obj2_exists();

    leads_to_trans::<CState>(sm_spec(), init(), obj1_exists(), obj2_exists());

    leads_to_apply::<CState>(sm_spec(), init(), obj2_exists());
}

proof fn liveness()
    ensures
        sm_spec().entails(eventually(lift_state(obj1_exists()).and(lift_state(obj2_exists())))),
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
     * the eventually from `lemma_eventually_obj2_exits` and the always from `safety`
     * to one eventually.
     */

    lemma_eventually_obj2_exits();

    safety();

    always_and_eventually::<CState>(sm_spec(), order_inv(), obj2_exists());

    /*
     * We get a weaker eventually, which is our goal, from `eventually_weaken`.
     */
    eventually_weaken_auto::<CState>(sm_spec());
}

}
