// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositionality::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(I)]
pub struct ControllerSpecs<S, I> {
    pub controller: Controller<S, I>,
    // The key should be the one that points to controller in the cluster's controllers map
    pub key: int,
    // The top level property of the input controller (e.g., ESR)
    pub property: TempPred<S>,
    // The inv asserts that the controller indexed by good_citizen_id does not interfere with the input controller's reconcile
    // This invariant, if interpretable, should state something like:
    // forall |message| message is sent by the controller indexed by good_citizen_id ==> message does not modify object X,
    // where X is something that the input controller cares about.
    //
    // To tell whether a message in the network is sent by a controller, our cluster state machine should attach the
    // controller key to each message sent by the controller, regardless of the controller's implementation.
    //
    // Note that the invariant likely does not hold when good_citizen_id points to the input controller itself, that is,
    // if there are two instances of the same controller, they will interfere with each other.
    // This is not a problem because there is no reason to run two such instances at the same time.
    pub non_interference: spec_fn(good_citizen_id: int) -> StatePred<S>,
}

// This is our top-level theorem: the consumer and producers are correct in any cluster
// if the other controllers in that cluster do not interfere with the consumer or producers.
pub proof fn consumer_and_producers_are_correct<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer: ControllerSpecs<S, I>, producers: Seq<ControllerSpecs<S, I>>)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer.
        forall |s| #[trigger] cluster.init()(s) ==> consumer.controller.init()(s),
        // The cluster starts with the initial state of the producer.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |s| #[trigger] cluster.init()(s) ==> producers[p_index].controller.init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(controller_fairness::<S, I>(consumer.controller)),
        // The fairness condition is enough to say that each producer runs as part of the cluster's next transition.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> spec.entails(controller_fairness::<S, I>(producers[p_index].controller)),
        // The consumer.key points to the consumer.controller.
        cluster.controllers.contains_pair(consumer.key, consumer.controller),
        // Each producers[p_index].key points to producers[p_index].controller.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> cluster.controllers.contains_pair(producers[p_index].key, producers[p_index].controller),
        // No other controllers interfere with the consumer.
        forall |good_citizen_id| cluster.controllers.remove(consumer.key).remove_keys(producers.map_values(|p: ControllerSpecs<S, I>| p.key).to_set()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (consumer.non_interference)(good_citizen_id)))),
        // For each producer, no other controllers interfere with that producer.
        forall |p_index: int| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |good_citizen_id| cluster.controllers.remove(consumer.key).remove_keys(producers.map_values(|p: ControllerSpecs<S, I>| p.key).to_set()).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].non_interference)(good_citizen_id))))
    ensures
        // Consumer is correct.
        spec.entails(consumer.property),
        // Each producer is correct.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(producers[p_index].property),
        // No one interferes with the consumer (except the consumer itself).
        forall |good_citizen_id| cluster.controllers.remove(consumer.key).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (consumer.non_interference)(good_citizen_id)))),
        // For each producer, no one interferes with that producer (except that producer itself).
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |good_citizen_id| cluster.controllers.remove(producers[p_index].key).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].non_interference)(good_citizen_id)))),
{
    assert forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
    implies (forall |good_citizen_id| #[trigger] cluster.controllers.remove(producers[p_index].key).contains_key(good_citizen_id)
        ==> spec.entails(always(lift_state((producers[p_index].non_interference)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id| cluster.controllers.remove(producers[p_index].key).contains_key(good_citizen_id)
        implies spec.entails(always(lift_state(#[trigger] (producers[p_index].non_interference)(good_citizen_id)))) by {
            if good_citizen_id == consumer.key {
                consumer_does_not_interfere_with_the_producer(spec, cluster, consumer, producers, p_index);
            } else if producers.map_values(|p: ControllerSpecs<S, I>| p.key).to_set().contains(good_citizen_id) {
                let j = choose |j| 0 <= j < producers.len() && #[trigger] producers[j].key == good_citizen_id;
                producer_does_not_interfere_with_the_producer(spec, cluster, producers, j, p_index);
            } else {
                assert(spec.entails(always(lift_state((producers[p_index].non_interference)(good_citizen_id)))));
            }
        }
    }

    assert forall |p_index| 0 <= p_index < producers.len() implies #[trigger] spec.entails(producers[p_index].property) by {
        producer_is_correct(spec, cluster, producers, p_index);
    }

    assert forall |good_citizen_id| cluster.controllers.remove(consumer.key).contains_key(good_citizen_id)
    implies spec.entails(always(lift_state(#[trigger] (consumer.non_interference)(good_citizen_id)))) by {
        if producers.map_values(|p: ControllerSpecs<S, I>| p.key).to_set().contains(good_citizen_id) {
            let j = choose |j| 0 <= j < producers.len() && #[trigger] producers[j].key == good_citizen_id;
            producer_does_not_interfere_with_the_consumer(spec, cluster, consumer, producers, j);
        } else {
            assert(spec.entails(always(lift_state((consumer.non_interference)(good_citizen_id)))));
        }
    }
    consumer_is_correct(spec, cluster, consumer, producers);
}

// To prove consumer_and_producers_are_correct, there are five proof obligations.

// Proof obligation 1:
// Producer is correct when running in any cluster where there is no interference.
#[verifier(external_body)]
proof fn producer_is_correct<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, producers: Seq<ControllerSpecs<S, I>>, p_index: int)
    requires
        0 <= p_index < producers.len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the producer.
        forall |s| cluster.init()(s) ==> #[trigger] producers[p_index].controller.init()(s),
        // The fairness condition is enough to say that the producer runs as part of the cluster's next transition.
        spec.entails(controller_fairness::<S, I>(producers[p_index].controller)),
        // The next two preconditions say that no controller (except the producer itself) interferes with this producer.
        cluster.controllers.contains_pair(producers[p_index].key, producers[p_index].controller),
        forall |good_citizen_id| cluster.controllers.remove(producers[p_index].key).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].non_interference)(good_citizen_id)))),
    ensures
        spec.entails(producers[p_index].property),
{}

// Proof obligation 2:
// Consumer is correct when running in any cluster where each producer's spec is available and there is no interference.
#[verifier(external_body)]
proof fn consumer_is_correct<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer: ControllerSpecs<S, I>, producers: Seq<ControllerSpecs<S, I>>)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer.
        forall |s| cluster.init()(s) ==> #[trigger] consumer.controller.init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(controller_fairness::<S, I>(consumer.controller)),
        // The next two preconditions say that no controller (except the consumer itself) interferes with this consumer.
        cluster.controllers.contains_pair(consumer.key, consumer.controller),
        forall |good_citizen_id| cluster.controllers.remove(consumer.key).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (consumer.non_interference)(good_citizen_id)))),
        // We directly use the temporal property of the producers.
        forall |p_index: int| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(producers[p_index].property),
    ensures
        spec.entails(consumer.property),
{}

// Proof obligation 3:
// Consumer does not interfere with the producer in any cluster.
#[verifier(external_body)]
proof fn consumer_does_not_interfere_with_the_producer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer: ControllerSpecs<S, I>, producers: Seq<ControllerSpecs<S, I>>, p_index: int)
    requires
        0 <= p_index < producers.len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(consumer.key, consumer.controller),
    ensures
        // The consumer never interferes with the producer.
        spec.entails(always(lift_state((producers[p_index].non_interference)(consumer.key)))),
{}

// Proof obligation 4:
// Producer does not interfere with another producer in any cluster.
#[verifier(external_body)]
proof fn producer_does_not_interfere_with_the_producer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, producers: Seq<ControllerSpecs<S, I>>, p_index: int, q_index: int)
    requires
        0 <= p_index < producers.len(),
        0 <= q_index < producers.len(),
        // We require the two producers to be different because there is no point to prove
        // a producer does not interfere with another instance of itself.
        p_index != q_index,
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(producers[p_index].key, producers[p_index].controller),
    ensures
        // The producer (p_index) never interferes with the other producer (q_index).
        spec.entails(always(lift_state((producers[q_index].non_interference)(producers[p_index].key)))),
{}

// Proof obligation 5:
// Producer does not interfere with the consumer in any cluster.
#[verifier(external_body)]
proof fn producer_does_not_interfere_with_the_consumer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer: ControllerSpecs<S, I>, producers: Seq<ControllerSpecs<S, I>>, p_index: int)
    requires
        0 <= p_index < producers.len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(producers[p_index].key, producers[p_index].controller),
    ensures
        // The producer never interferes with the consumer.
        spec.entails(always(lift_state((consumer.non_interference)(producers[p_index].key)))),
{}

}
