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
spec fn no_one_interferes_producer<S, I>(cluster: Cluster<S, I>) -> StatePred<S>;

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
proof fn producer_property_holds_if_no_interference<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>)
    requires
        spec.entails(lift_state(cluster.init())),
        forall |s| cluster.init()(s) ==> #[trigger] producer::<S, I>().init()(s),
        spec.entails(always(lift_action(cluster.next()))),
        forall |input, s, s_prime| #[trigger] producer::<S, I>().next(input)(s, s_prime) ==> cluster.next()(s, s_prime),
        spec.entails(producer_fairness::<S, I>()),
        spec.entails(always(lift_state(no_one_interferes_producer::<S, I>(cluster)))),
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
        spec.entails(always(lift_state(no_one_interferes_producer::<S, I>(consumer_and_producer::<S, I>())))),
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
    let cluster = consumer_and_producer::<S, I>();

    assert forall |s| cluster.init()(s) implies #[trigger] producer::<S, I>().init()(s) by {
        assert forall |i| 0 <= i < cluster.controllers.len() implies #[trigger] cluster.controllers[i].init()(s) by {}
        assert(producer::<S, I>() =~= cluster.controllers[1]);
    }

    assert forall |input, s, s_prime| #[trigger] producer::<S, I>().next(input)(s, s_prime) implies cluster.next()(s, s_prime) by {
        let step = Step::ControllerStep(1, input);
        assert(cluster.next_step(s, s_prime, step));
    }

    consumer_does_not_interfere_with_the_producer::<S, I>(spec);
    producer_property_holds_if_no_interference::<S, I>(spec, cluster);
    consumer_property_holds_if_producer_property_holds::<S, I>(spec);
}

}
