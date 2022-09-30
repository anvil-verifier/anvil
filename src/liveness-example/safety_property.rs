#[allow(unused_imports)]
use crate::pervasive::seq::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;
#[allow(unused_imports)]
use crate::simple_state_machine::*;
#[allow(unused_imports)]
use crate::state::*;
#[allow(unused_imports)]
use crate::temporal_logic::*;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

pub open spec fn happy(s: SimpleState) -> bool {
    s.happy
}

pub open spec fn happy_as_set() -> Set<SimpleState> {
    Set::new(|state: SimpleState| happy(state))
}


pub open spec fn always_happy() -> bool {
    valid(
        implies(
            and(
                lift_state(init_as_set()),
                always(lift_action(next_as_set()))
            ),
            always(lift_state(happy_as_set()))
        )
    )
}

proof fn prove_always_happy()
    ensures
        always_happy()
{
}

}
