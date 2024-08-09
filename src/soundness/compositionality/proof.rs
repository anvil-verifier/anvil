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
spec fn producer_property<S>(p_index: int) -> TempPred<S>;

// The inv saying that no one interferes with the producer's reconcile
spec fn no_one_interferes_producer<S, I>(cluster: Cluster<S, I>, p_index: int) -> StatePred<S>;

// This is our end-goal theorem: in a cluster with all the producers and the consumer,
// all controllers are correct.
proof fn consumer_property_holds<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(consumer_and_producers::<S, I>().init())),
        spec.entails(always(lift_action(consumer_and_producers::<S, I>().next()))),
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len() ==> #[trigger] spec.entails(producer_fairness::<S, I>(p_index)),
        spec.entails(consumer_fairness::<S, I>()),
    ensures
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len() ==> #[trigger] spec.entails(producer_property::<S>(p_index)),
        spec.entails(consumer_property::<S>()),
{
    let cluster = consumer_and_producers::<S, I>();

    assert forall |p_index| 0 <= p_index < producers::<S, I>().len() implies #[trigger] spec.entails(producer_property::<S>(p_index)) by {
        assert forall |s| cluster.init()(s) implies #[trigger] producers::<S, I>()[p_index].init()(s) by {
            assert forall |i| 0 <= i < cluster.controllers.len() implies #[trigger] cluster.controllers[i].init()(s) by {}
            assert(producers::<S, I>()[p_index] =~= cluster.controllers[p_index]);
        }

        assert forall |input, s, s_prime| #[trigger] producers::<S, I>()[p_index].next(input)(s, s_prime) implies cluster.next()(s, s_prime) by {
            let step = Step::ControllerStep(p_index, input);
            assert(cluster.next_step(s, s_prime, step));
        }

        consumer_does_not_interfere_with_the_producer::<S, I>(spec, p_index);
        producer_property_holds_if_no_interference::<S, I>(spec, cluster, p_index);
    }

    consumer_property_holds_if_producer_property_holds::<S, I>(spec);
}

// To prove the above theorem, there are three proof obligations.

// Proof obligation 1:
// Producer is correct when running with the shape shifter assuming no interference.
// In fact, this theorem is all you need if you only care about the producer, not the
// consumer.
#[verifier(external_body)]
proof fn producer_property_holds_if_no_interference<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, p_index: int)
    requires
        0 <= p_index < producers::<S, I>().len(),
        spec.entails(lift_state(cluster.init())),
        forall |s| cluster.init()(s) ==> #[trigger] producers::<S, I>()[p_index].init()(s),
        spec.entails(always(lift_action(cluster.next()))),
        forall |input, s, s_prime| #[trigger] producers::<S, I>()[p_index].next(input)(s, s_prime) ==> cluster.next()(s, s_prime),
        spec.entails(producer_fairness::<S, I>(p_index)),
        spec.entails(always(lift_state(no_one_interferes_producer::<S, I>(cluster, p_index)))),
    ensures
        spec.entails(producer_property::<S>(p_index)),
{}

// Proof obligation 2:
// Consumer is correct when running with the producer assuming the producer is correct.
#[verifier(external_body)]
proof fn consumer_property_holds_if_producer_property_holds<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(consumer_and_producers::<S, I>().init())),
        spec.entails(always(lift_action(consumer_and_producers::<S, I>().next()))),
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len() ==> #[trigger] spec.entails(producer_fairness::<S, I>(p_index)),
        spec.entails(consumer_fairness::<S, I>()),
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len() ==> #[trigger] spec.entails(producer_property::<S>(p_index)),
    ensures
        spec.entails(consumer_property::<S>()),
{}

// Proof obligation 3:
// Consumer does not interfere with the producer.
#[verifier(external_body)]
proof fn consumer_does_not_interfere_with_the_producer<S, I>(spec: TempPred<S>, p_index: int)
    requires
        0 <= p_index < producers::<S, I>().len(),
        spec.entails(lift_state(consumer_and_producers::<S, I>().init())),
        spec.entails(always(lift_action(consumer_and_producers::<S, I>().next()))),
    ensures
        spec.entails(always(lift_state(no_one_interferes_producer::<S, I>(consumer_and_producers::<S, I>(), p_index)))),
{}

}
