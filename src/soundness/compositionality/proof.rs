// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositionality::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// The top level property of the consumer controller (e.g., ESR)
spec fn consumer_property<S>() -> TempPred<S>;

// The top level property of the producer controller (e.g., ESR)
spec fn producer_property<S>() -> TempPred<S>;

// The inv saying that no one interferes with the producer's reconcile
spec fn no_one_interferes_producer<S, I>(any: Seq<Controller<S, I>>) -> StatePred<S>;

// Our goal is to prove that both producer and consumer are correct
//    requires
//        spec.entails(lift_state(consumer_and_producer::<S, I>().init())),
//        spec.entails(always(lift_action(consumer_and_producer::<S, I>().next()))),
//        spec.entails(producer_fairness::<S, I>()),
//        spec.entails(consumer_fairness::<S, I>()),
//    ensures
//        spec.entails(producer_property::<S>()),
//        spec.entails(consumer_property::<S>()),
//
// To do so, there are three proof obligations:

// Proof obligation 1:
// Producer is correct when running with the shape shifter assuming no interference.
// In fact, this theorem is all you need if you only care about the producer, not the
// consumer.
#[verifier(external_body)]
proof fn producer_property_holds_if_no_interference<S, I>(spec: TempPred<S>, any: Seq<Controller<S, I>>)
    requires
        spec.entails(lift_state(any_and_producer::<S, I>(any).init())),
        spec.entails(always(lift_action(any_and_producer::<S, I>(any).next()))),
        spec.entails(producer_fairness::<S, I>()),
        spec.entails(always(lift_state(no_one_interferes_producer::<S, I>(any)))),
    ensures
        spec.entails(producer_property::<S>()),
{}

// Proof obligation 2:
// Consumer is correct when running with the producer assuming the producer is correct.
#[verifier(external_body)]
proof fn consumer_property_holds_if_producer_property_holds<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(consumer_and_producer::<S, I>().init())),
        spec.entails(always(lift_action(consumer_and_producer::<S, I>().next()))),
        spec.entails(producer_fairness::<S, I>()),
        spec.entails(consumer_fairness::<S, I>()),
        spec.entails(producer_property::<S>()),
    ensures
        spec.entails(consumer_property::<S>()),
{}

// Proof obligation 3:
// Consumer does not interfere with the producer.
#[verifier(external_body)]
proof fn consumer_does_not_interfere_with_the_producer<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(consumer_and_producer::<S, I>().init())),
        spec.entails(always(lift_action(consumer_and_producer::<S, I>().next()))),
    ensures
        spec.entails(always(lift_state(no_one_interferes_producer::<S, I>(seq![consumer()])))),
{}

// Now we can draw the final conclusion with the lemmas above.
proof fn consumer_property_holds<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(consumer_and_producer::<S, I>().init())),
        spec.entails(always(lift_action(consumer_and_producer::<S, I>().next()))),
        spec.entails(producer_fairness::<S, I>()),
        spec.entails(consumer_fairness::<S, I>()),
    ensures
        spec.entails(producer_property::<S>()),
        spec.entails(consumer_property::<S>()),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies lift_state(any_and_producer::<S, I>(seq![consumer()]).init()).satisfied_by(ex) by {
        assert(spec.implies(lift_state(consumer_and_producer::<S, I>().init())).satisfied_by(ex));
        assert(seq![consumer::<S, I>()].push(producer()) =~= seq![consumer(), producer()])
    }

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(lift_action(any_and_producer::<S, I>(seq![consumer()]).next())).satisfied_by(ex) by {
        assert(spec.implies(always(lift_action(consumer_and_producer::<S, I>().next()))).satisfied_by(ex));
        assert forall |i| #[trigger] lift_action(any_and_producer::<S, I>(seq![consumer()]).next()).satisfied_by(ex.suffix(i)) by {
            assert(lift_action(consumer_and_producer::<S, I>().next()).satisfied_by(ex.suffix(i)));
            assert(seq![consumer::<S, I>()].push(producer()) =~= seq![consumer(), producer()])
        }
    }

    consumer_does_not_interfere_with_the_producer::<S, I>(spec);
    producer_property_holds_if_no_interference::<S, I>(spec, seq![consumer()]);
    consumer_property_holds_if_producer_property_holds::<S, I>(spec);
}

}
