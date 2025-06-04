#![allow(unused_imports)]
pub mod state_machine;
pub mod temporal_logic;
pub mod vstd_ext;

use state_machine::action::*;
use temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

enum ThreadState {
    Waiting,
    Holding,
    Terminated,
}

struct ProgramState {
    pub lock: bool,
    pub threads: Map<int, ThreadState>,
}

enum Step {
    ThreadAcquiresLock(int),
    ThreadReleasesLock(int),
    Stutter,
}

spec fn init() -> StatePred<ProgramState> {
    |s: ProgramState| {
        &&& !s.lock
        &&& s.threads.contains_key(0)
        &&& s.threads[0] is Waiting
        &&& s.threads.contains_key(1)
        &&& s.threads[1] is Waiting
    }
}

spec fn next() -> ActionPred<ProgramState> {
    |s, s_prime: ProgramState| exists |step: Step| next_step(s, s_prime, step)
}

spec fn next_step(s: ProgramState, s_prime: ProgramState, step: Step) -> bool {
    match step {
        Step::ThreadAcquiresLock(input) => thread_acquires_lock().forward(input)(s, s_prime),
        Step::ThreadReleasesLock(input) => thread_releases_lock().forward(input)(s, s_prime),
        Step::Stutter => stutter().forward(())(s, s_prime),
    }
}

spec fn thread_acquires_lock() -> Action<ProgramState, int, ()> {
    Action {
        precondition: |thread_id: int, s: ProgramState| {
            &&& !s.lock
            &&& thread_id == 0 || thread_id == 1
            &&& s.threads[thread_id] is Waiting
        },
        transition: |thread_id: int, s: ProgramState| {
            (ProgramState {
                lock: true,
                threads: s.threads.insert(thread_id, ThreadState::Holding)
            }, ())
        },
    }
}

spec fn thread_releases_lock() -> Action<ProgramState, int, ()> {
    Action {
        precondition: |thread_id: int, s: ProgramState| {
            &&& thread_id == 0 || thread_id == 1
            &&& s.threads[thread_id] is Holding
        },
        transition: |thread_id: int, s: ProgramState| {
            (ProgramState {
                lock: false,
                threads: s.threads.insert(thread_id, ThreadState::Terminated)
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
    |s: ProgramState| s.threads[0] is Terminated && s.threads[1] is Terminated
}

proof fn both_threads_eventually_terminate(model: TempPred<ProgramState>)
    requires
        model.entails(lift_state(init())),
        model.entails(always(lift_action(next()))),
        model.entails(tla_forall(|thread_id| thread_acquires_lock().weak_fairness(thread_id))),
        model.entails(tla_forall(|thread_id| thread_releases_lock().weak_fairness(thread_id))),
    ensures
        model.entails(eventually(lift_state(both_threads_are_terminated())))
{
    let one_of_the_threads_is_holding = |s: ProgramState| {
        ||| s.threads[0] is Holding && s.threads[1] is Waiting && s.lock
        ||| s.threads[0] is Waiting && s.threads[1] is Holding && s.lock
    };
    assert(model.entails(lift_state(init()).leads_to(lift_state(one_of_the_threads_is_holding)))) by {
        use_tla_forall(model, |thread_id: int| thread_acquires_lock().weak_fairness(thread_id), 0);
        thread_acquires_lock().wf1(0, model, next(), init(), one_of_the_threads_is_holding);
    };

    let t0_holding_t1_waiting = |s: ProgramState| s.threads[0] is Holding && s.threads[1] is Waiting && s.lock;
    assert(model.entails(lift_state(t0_holding_t1_waiting).leads_to(lift_state(both_threads_are_terminated())))) by {
        let t0_terminated_t1_waiting = |s: ProgramState| s.threads[0] is Terminated && s.threads[1] is Waiting && !s.lock;
        assert(model.entails(lift_state(t0_holding_t1_waiting).leads_to(lift_state(t0_terminated_t1_waiting)))) by {
            use_tla_forall(model, |thread_id: int| thread_releases_lock().weak_fairness(thread_id), 0);
            thread_releases_lock().wf1(0, model, next(), t0_holding_t1_waiting, t0_terminated_t1_waiting);
        };

        let t0_terminated_t1_holding = |s: ProgramState| s.threads[0] is Terminated && s.threads[1] is Holding && s.lock;
        assert(model.entails(lift_state(t0_terminated_t1_waiting).leads_to(lift_state(t0_terminated_t1_holding)))) by {
            use_tla_forall(model, |thread_id: int| thread_acquires_lock().weak_fairness(thread_id), 1);
            thread_acquires_lock().wf1(1, model, next(), t0_terminated_t1_waiting, t0_terminated_t1_holding);
        };

        assert(model.entails(lift_state(t0_terminated_t1_holding).leads_to(lift_state(both_threads_are_terminated())))) by {
            use_tla_forall(model, |thread_id: int| thread_releases_lock().weak_fairness(thread_id), 1);
            thread_releases_lock().wf1(1, model, next(), t0_terminated_t1_holding, both_threads_are_terminated());
        };

        leads_to_trans_n!(
            model,
            lift_state(t0_holding_t1_waiting),
            lift_state(t0_terminated_t1_waiting),
            lift_state(t0_terminated_t1_holding),
            lift_state(both_threads_are_terminated())
        );
    }

    let t1_holding_t0_waiting = |s: ProgramState| s.threads[0] is Waiting && s.threads[1] is Holding && s.lock;
    assert(model.entails(lift_state(t1_holding_t0_waiting).leads_to(lift_state(both_threads_are_terminated())))) by {
        let t1_terminated_t0_waiting = |s: ProgramState| s.threads[0] is Waiting && s.threads[1] is Terminated && !s.lock;
        assert(model.entails(lift_state(t1_holding_t0_waiting).leads_to(lift_state(t1_terminated_t0_waiting)))) by {
            use_tla_forall(model, |thread_id: int| thread_releases_lock().weak_fairness(thread_id), 1);
            thread_releases_lock().wf1(1, model, next(), t1_holding_t0_waiting, t1_terminated_t0_waiting);
        };

        let t1_terminated_t0_holding = |s: ProgramState| s.threads[0] is Holding && s.threads[1] is Terminated && s.lock;
        assert(model.entails(lift_state(t1_terminated_t0_waiting).leads_to(lift_state(t1_terminated_t0_holding)))) by {
            use_tla_forall(model, |thread_id: int| thread_acquires_lock().weak_fairness(thread_id), 0);
            thread_acquires_lock().wf1(0, model, next(), t1_terminated_t0_waiting, t1_terminated_t0_holding);
        };

        assert(model.entails(lift_state(t1_terminated_t0_holding).leads_to(lift_state(both_threads_are_terminated())))) by {
            use_tla_forall(model, |thread_id: int| thread_releases_lock().weak_fairness(thread_id), 0);
            thread_releases_lock().wf1(0, model, next(), t1_terminated_t0_holding, both_threads_are_terminated());
        };

        leads_to_trans_n!(
            model,
            lift_state(t1_holding_t0_waiting),
            lift_state(t1_terminated_t0_waiting),
            lift_state(t1_terminated_t0_holding),
            lift_state(both_threads_are_terminated())
        );
    }

    or_leads_to_combine(model, lift_state(t0_holding_t1_waiting), lift_state(t1_holding_t0_waiting), lift_state(both_threads_are_terminated()));

    temp_pred_equality(lift_state(t0_holding_t1_waiting).or(lift_state(t1_holding_t0_waiting)), lift_state(one_of_the_threads_is_holding));

    leads_to_trans(model, lift_state(init()), lift_state(one_of_the_threads_is_holding), lift_state(both_threads_are_terminated()));

    leads_to_apply(model, lift_state(init()), lift_state(both_threads_are_terminated()));
}

}
