// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositionality::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

// A is consumer and B is producer (A relies on B)
// step 1: prove that B is correct (the property) in an env (shape shifter) that does not interfere with B (B + shapeshifter)
// step 2: prove that A is correct assuming B is correct (A + B)
// step 3: prove that A does not interfere with B (A + B)

verus! {

// The top level property of the consumer controller (e.g., ESR)
spec fn consumer_property<S>() -> TempPred<S>;

// The top level property of the producer controller (e.g., ESR)
spec fn producer_property<S>() -> TempPred<S>;

// The inv saying that no one interferes with the producer's reconcile
spec fn no_one_interferes_producer<S>() -> StatePred<S>;

// Behaviors of consumer are covered by behaviors of the shape shifter
#[verifier(external_body)]
proof fn consumer_does_nothing_beyond_what_shape_shifter_does<S, I>(input: I) -> (ss_input: I)
    ensures forall |s, s_prime: S| #[trigger] ConsumerController::reconcile(input)(s, s_prime)
            ==> ShapeShifter::reconcile(ss_input)(s, s_prime)
{
    arbitrary()
}

#[verifier(external_body)]
proof fn producer_property_holds_if_no_interference<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(ProducerAndShapeShifter::<S, I>::init())),
        spec.entails(always(lift_action(ProducerAndShapeShifter::<S, I>::next()))),
        spec.entails(producer_fairness::<S, I>()),
        spec.entails(always(lift_state(no_one_interferes_producer::<S>()))),
    ensures
        spec.entails(producer_property::<S>()),
{}

#[verifier(external_body)]
proof fn consumer_property_holds_if_producer_property_holds<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(ConsumerAndProducer::<S, I>::init())),
        spec.entails(always(lift_action(ConsumerAndProducer::<S, I>::next()))),
        spec.entails(producer_fairness::<S, I>()),
        spec.entails(consumer_fairness::<S, I>()),
        spec.entails(producer_property::<S>()),
    ensures
        spec.entails(consumer_property::<S>()),
{}

#[verifier(external_body)]
proof fn consumer_does_not_interfere_with_the_producer<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(ConsumerAndProducer::<S, I>::init())),
        spec.entails(always(lift_action(ConsumerAndProducer::<S, I>::next()))),
    ensures
        spec.entails(always(lift_state(no_one_interferes_producer::<S>()))),
{}

proof fn consumer_property_holds<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(ConsumerAndProducer::<S, I>::init())),
        spec.entails(always(lift_action(ConsumerAndProducer::<S, I>::next()))),
        spec.entails(producer_fairness::<S, I>()),
        spec.entails(consumer_fairness::<S, I>()),
    ensures
        spec.entails(consumer_property::<S>()),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(lift_action(ProducerAndShapeShifter::<S, I>::next())).satisfied_by(ex) by {
        assert(spec.implies(always(lift_action(ConsumerAndProducer::<S, I>::next()))).satisfied_by(ex));
        assert forall |i| #[trigger] lift_action(ProducerAndShapeShifter::<S, I>::next()).satisfied_by(ex.suffix(i)) by {
            assert(lift_action(ConsumerAndProducer::<S, I>::next()).satisfied_by(ex.suffix(i)));
            cp_does_nothing_beyond_ps::<S, I>(ex.suffix(i).head(), ex.suffix(i).head_next());
        }
    }

    consumer_does_not_interfere_with_the_producer::<S, I>(spec);
    producer_property_holds_if_no_interference::<S, I>(spec);
    consumer_property_holds_if_producer_property_holds::<S, I>(spec);
}

proof fn cp_does_nothing_beyond_ps<S, I>(s: S, s_prime: S)
    requires
        ConsumerAndProducer::<S, I>::next()(s, s_prime),
    ensures
        ProducerAndShapeShifter::<S, I>::next()(s, s_prime),
{
    let step = choose |step: Step<I>| ConsumerAndProducer::next_step(s, s_prime, step);
    assert(ConsumerAndProducer::next_step(s, s_prime, step));
    match step {
        Step::TargetControllerStep(input) => {
            let ss_input = consumer_does_nothing_beyond_what_shape_shifter_does::<S, I>(input);
            assert(ProducerAndShapeShifter::next_step(s, s_prime, Step::AnotherControllerStep(ss_input)));
        }
        Step::AnotherControllerStep(input) => {
            assert(ProducerAndShapeShifter::next_step(s, s_prime, Step::TargetControllerStep(input)));
        }
        _ => {
            assert(ProducerAndShapeShifter::next_step(s, s_prime, step));
        }
    }
}

}
