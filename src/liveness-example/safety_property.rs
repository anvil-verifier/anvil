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

pub open spec fn safety() -> bool {
    valid(
        implies(
            and(
                lift_state(|s: SimpleState| init(s)),
                always(lift_action(|s: SimpleState, s_prime: SimpleState| next(s, s_prime)))
            ),
            always(lift_state(|s: SimpleState| happy(s)))
        )
    )
}

proof fn prove_safety()
    ensures
        safety()
{
}

}
