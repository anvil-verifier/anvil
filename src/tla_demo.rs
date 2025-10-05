#![allow(unused_imports)]

use crate::state_machine::action::*;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

enum Tid {
    A,
    B
}

enum ThreadState {
    Waiting,
    Holding,
    Terminated,
}

struct ProgramState {
    lock: bool,
    threads: Map<Tid, ThreadState>,
}

spec fn init() -> StatePred<ProgramState> {
    |s: ProgramState| {
        &&& !s.lock
        &&& s.threads.contains_key(Tid::A)
        &&& s.threads[Tid::A] is Waiting
        &&& s.threads.contains_key(Tid::B)
        &&& s.threads[Tid::B] is Waiting
    }
}

spec fn next() -> ActionPred<ProgramState> {
    |s, s_prime: ProgramState| {
        ||| thread_acquires_lock().forward(Tid::A)(s, s_prime)
        ||| thread_releases_lock().forward(Tid::A)(s, s_prime)
        ||| thread_acquires_lock().forward(Tid::B)(s, s_prime)
        ||| thread_releases_lock().forward(Tid::B)(s, s_prime)
        ||| stutter().forward(())(s, s_prime)
    }
}

spec fn thread_acquires_lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState| {
            !s.lock && s.threads[tid] is Waiting
        },
        transition: |tid: Tid, s: ProgramState| {
            (ProgramState {
                lock: true,
                threads: s.threads.insert(tid, ThreadState::Holding)
            }, ())
        },
    }
}

spec fn thread_releases_lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState| {
            s.threads[tid] is Holding
        },
        transition: |tid: Tid, s: ProgramState| {
            (ProgramState {
                lock: false,
                threads: s.threads.insert(tid, ThreadState::Terminated)
            }, ())
        },
    }
}

spec fn stutter() -> Action<ProgramState, (), ()> {
    Action {
        precondition: |input: (), s: ProgramState| { true },
        transition: |input: (), s: ProgramState| { (s, ()) },
    }
}

spec fn both_threads_are_terminated() -> StatePred<ProgramState> {
    |s: ProgramState| s.threads[Tid::A] is Terminated && s.threads[Tid::B] is Terminated
}

proof fn both_threads_eventually_terminate(model: TempPred<ProgramState>)
    requires
        model.entails(lift_state(init())),
        model.entails(always(lift_action(next()))),
        model.entails(tla_forall(|tid| thread_acquires_lock().weak_fairness(tid))),
        model.entails(tla_forall(|tid| thread_releases_lock().weak_fairness(tid))),
    ensures
        model.entails(eventually(lift_state(both_threads_are_terminated())))
{
    let one_of_the_threads_is_holding = |s: ProgramState| {
        ||| s.threads[Tid::A] is Holding && s.threads[Tid::B] is Waiting && s.lock
        ||| s.threads[Tid::A] is Waiting && s.threads[Tid::B] is Holding && s.lock
    };
    assert(model.entails(lift_state(init()).leads_to(lift_state(one_of_the_threads_is_holding)))) by {
        use_tla_forall(model, |tid| thread_acquires_lock().weak_fairness(tid), Tid::A);
        thread_acquires_lock().wf1(Tid::A, model, next(), init(), one_of_the_threads_is_holding);
    };

    let ta_holding_tb_waiting = |s: ProgramState| s.threads[Tid::A] is Holding && s.threads[Tid::B] is Waiting && s.lock;
    assert(model.entails(lift_state(ta_holding_tb_waiting).leads_to(lift_state(both_threads_are_terminated())))) by {
        let ta_terminated_tb_waiting = |s: ProgramState| s.threads[Tid::A] is Terminated && s.threads[Tid::B] is Waiting && !s.lock;
        assert(model.entails(lift_state(ta_holding_tb_waiting).leads_to(lift_state(ta_terminated_tb_waiting)))) by {
            use_tla_forall(model, |tid| thread_releases_lock().weak_fairness(tid), Tid::A);
            thread_releases_lock().wf1(Tid::A, model, next(), ta_holding_tb_waiting, ta_terminated_tb_waiting);
        };

        let ta_terminated_tb_holding = |s: ProgramState| s.threads[Tid::A] is Terminated && s.threads[Tid::B] is Holding && s.lock;
        assert(model.entails(lift_state(ta_terminated_tb_waiting).leads_to(lift_state(ta_terminated_tb_holding)))) by {
            use_tla_forall(model, |tid| thread_acquires_lock().weak_fairness(tid), Tid::B);
            thread_acquires_lock().wf1(Tid::B, model, next(), ta_terminated_tb_waiting, ta_terminated_tb_holding);
        };

        assert(model.entails(lift_state(ta_terminated_tb_holding).leads_to(lift_state(both_threads_are_terminated())))) by {
            use_tla_forall(model, |tid| thread_releases_lock().weak_fairness(tid), Tid::B);
            thread_releases_lock().wf1(Tid::B, model, next(), ta_terminated_tb_holding, both_threads_are_terminated());
        };

        leads_to_trans_n!(
            model,
            lift_state(ta_holding_tb_waiting),
            lift_state(ta_terminated_tb_waiting),
            lift_state(ta_terminated_tb_holding),
            lift_state(both_threads_are_terminated())
        );
    }

    let tb_holding_ta_waiting = |s: ProgramState| s.threads[Tid::A] is Waiting && s.threads[Tid::B] is Holding && s.lock;
    assert(model.entails(lift_state(tb_holding_ta_waiting).leads_to(lift_state(both_threads_are_terminated())))) by {
        let tb_terminated_ta_waiting = |s: ProgramState| s.threads[Tid::A] is Waiting && s.threads[Tid::B] is Terminated && !s.lock;
        assert(model.entails(lift_state(tb_holding_ta_waiting).leads_to(lift_state(tb_terminated_ta_waiting)))) by {
            use_tla_forall(model, |tid| thread_releases_lock().weak_fairness(tid), Tid::B);
            thread_releases_lock().wf1(Tid::B, model, next(), tb_holding_ta_waiting, tb_terminated_ta_waiting);
        };

        let tb_terminated_ta_holding = |s: ProgramState| s.threads[Tid::A] is Holding && s.threads[Tid::B] is Terminated && s.lock;
        assert(model.entails(lift_state(tb_terminated_ta_waiting).leads_to(lift_state(tb_terminated_ta_holding)))) by {
            use_tla_forall(model, |tid| thread_acquires_lock().weak_fairness(tid), Tid::A);
            thread_acquires_lock().wf1(Tid::A, model, next(), tb_terminated_ta_waiting, tb_terminated_ta_holding);
        };

        assert(model.entails(lift_state(tb_terminated_ta_holding).leads_to(lift_state(both_threads_are_terminated())))) by {
            use_tla_forall(model, |tid| thread_releases_lock().weak_fairness(tid), Tid::A);
            thread_releases_lock().wf1(Tid::A, model, next(), tb_terminated_ta_holding, both_threads_are_terminated());
        };

        leads_to_trans_n!(
            model,
            lift_state(tb_holding_ta_waiting),
            lift_state(tb_terminated_ta_waiting),
            lift_state(tb_terminated_ta_holding),
            lift_state(both_threads_are_terminated())
        );
    }

    or_leads_to_combine(model, lift_state(ta_holding_tb_waiting), lift_state(tb_holding_ta_waiting), lift_state(both_threads_are_terminated()));

    temp_pred_equality(lift_state(ta_holding_tb_waiting).or(lift_state(tb_holding_ta_waiting)), lift_state(one_of_the_threads_is_holding));

    leads_to_trans(model, lift_state(init()), lift_state(one_of_the_threads_is_holding), lift_state(both_threads_are_terminated()));

    leads_to_apply(model, lift_state(init()), lift_state(both_threads_are_terminated()));
}

}
