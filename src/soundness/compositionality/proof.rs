// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositionality::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// The top level property of the input controller (e.g., ESR)
spec fn property<S, I>(controller: Controller<S, I>) -> TempPred<S>;

// The inv asserts that the controller indexed by good_citizen_id does not interfere with the input controller's reconcile
// This invariant, if interpretable, should state something like:
// forall |message| message is sent by the controller indexed by good_citizen_id ==> message does not modify object X,
// where X is something that the input controller cares about.
//
// To tell whether a message in the network is sent by a controller, our cluster state machine should attach the
// controller id (the index) to each message sent by the controller, regardless of the controller's implementation.
//
// Note that the invariant likely does not hold when good_citizen_id points to the input controller itself, that is,
// if there are two instances of the same controller, they will interfere with each other.
// This is not a problem because there is no reason to run two such instances at the same time.
spec fn one_does_not_interfere_with_this_controller<S, I>(cluster: Cluster<S, I>, good_citizen_id: int, controller: Controller<S, I>) -> StatePred<S>;

// This is our top-level theorem: the consumer and producers are correct in any cluster
// if the other controllers in that cluster do not interfere with the consumer or producers.
// # Arguments:
// * spec: the temporal predicate that represents the state machine
// * cluster: the cluster that we want to run the consumers/producers in
// * consumer_id: the key of the consumer in cluster.controllers
// * producer_ids: maps the index of each producer to the key used in cluster.controllers
proof fn consumer_and_producers_are_correct<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer: Controller<S, I>, consumer_id: int, producers: Seq<Controller<S, I>>, producer_ids: Map<int, int>)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer.
        forall |s| cluster.init()(s) ==> #[trigger] consumer.init()(s),
        // The cluster starts with the initial state of the producer.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |s| cluster.init()(s) ==> #[trigger] producers[p_index].init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(controller_fairness::<S, I>(consumer)),
        // The fairness condition is enough to say that each producer runs as part of the cluster's next transition.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(controller_fairness::<S, I>(producers[p_index])),
        // The consumer_id points to the consumer.
        cluster.controllers.contains_pair(consumer_id, consumer),
        // Each element in producer_ids points to each producer respectively.
        forall |key| producer_ids.contains_key(key)
            ==> cluster.controllers.contains_pair(#[trigger] producer_ids[key], producers[key]),
        // A key exists in producer_ids iff it's within the range of producers,
        // which guarantees that producer_ids covers and only covers all the producers.
        forall |key| #[trigger] producer_ids.contains_key(key) <==> 0 <= key < producers.len(),
        // No other controllers interfere with the consumer.
        forall |good_citizen_id| #[trigger] cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, consumer)))),
        // For each producer, no other controllers interfere with that producer.
        forall |p_index: int| #![trigger producer_ids[p_index]] 0 <= p_index < producers.len()
            ==> forall |good_citizen_id| #[trigger] cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, producers[p_index]))))
    ensures
        // Consumer is correct.
        spec.entails(property::<S, I>(consumer)),
        // Each producer is correct.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(property::<S, I>(producers[p_index])),
        // No one interferes with the consumer (except the consumer itself).
        forall |good_citizen_id| #[trigger] cluster.controllers.remove(consumer_id).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, consumer)))),
        // For each producer, no one interferes with that producer (except that producer itself).
        forall |p_index| #![trigger producer_ids[p_index]] 0 <= p_index < producers.len()
            ==> forall |good_citizen_id| #[trigger] cluster.controllers.remove(producer_ids[p_index]).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, producers[p_index])))),
{
    assert forall |p_index| #![trigger producer_ids[p_index]] 0 <= p_index < producers.len()
    implies (forall |good_citizen_id| #[trigger] cluster.controllers.remove(producer_ids[p_index]).contains_key(good_citizen_id)
        ==> spec.entails(always(lift_state(one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, producers[p_index])))))
    by {
        assert forall |good_citizen_id| #[trigger] cluster.controllers.contains_key(good_citizen_id) && good_citizen_id != producer_ids[p_index]
        implies spec.entails(always(lift_state(one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, producers[p_index])))) by {
            if good_citizen_id == consumer_id {
                consumer_does_not_interfere_with_the_producer(spec, cluster, consumer, producers, good_citizen_id, p_index);
            } else if producer_ids.contains_value(good_citizen_id) {
                let j = choose |j| producer_ids.dom().contains(j) && #[trigger] producer_ids[j] == good_citizen_id;
                producer_does_not_interfere_with_the_producer(spec, cluster, producers, good_citizen_id, j, p_index);
            } else {
                assert(cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id));
                assert(spec.entails(always(lift_state(one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, producers[p_index])))));
            }
        }
    }

    assert forall |p_index| 0 <= p_index < producers.len() implies #[trigger] spec.entails(property::<S, I>(producers[p_index])) by {
        assert(producer_ids.contains_key(p_index));
        let producer_id = producer_ids[p_index];
        producer_is_correct(spec, cluster, producers, producer_id, p_index);
    }

    assert forall |good_citizen_id| cluster.controllers.remove(consumer_id).contains_key(good_citizen_id)
    implies spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, consumer)))) by {
        if producer_ids.contains_value(good_citizen_id) {
            let j = choose |j| producer_ids.dom().contains(j) && #[trigger] producer_ids[j] == good_citizen_id;
            producer_does_not_interfere_with_the_consumer(spec, cluster, consumer, producers, good_citizen_id, j);
        } else {
            assert(cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id));
            assert(spec.entails(always(lift_state(one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, consumer)))));
        }
    }
    consumer_is_correct(spec, cluster, consumer, consumer_id, producers);
}

// To prove consumer_and_producers_are_correct, there are five proof obligations.

// Proof obligation 1:
// Producer is correct when running in any cluster where there is no interference.
#[verifier(external_body)]
proof fn producer_is_correct<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, producers: Seq<Controller<S, I>>, producer_id: int, p_index: int)
    requires
        0 <= p_index < producers.len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the producer.
        forall |s| cluster.init()(s) ==> #[trigger] producers[p_index].init()(s),
        // The fairness condition is enough to say that the producer runs as part of the cluster's next transition.
        spec.entails(controller_fairness::<S, I>(producers[p_index])),
        // The next two preconditions say that no controller (except the producer itself) interferes with this producer.
        cluster.controllers.contains_pair(producer_id, producers[p_index]),
        forall |good_citizen_id| cluster.controllers.remove(producer_id).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, producers[p_index])))),
    ensures
        spec.entails(property::<S, I>(producers[p_index])),
{}

// Proof obligation 2:
// Consumer is correct when running in any cluster where each producer's spec is available and there is no interference.
#[verifier(external_body)]
proof fn consumer_is_correct<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer: Controller<S, I>, consumer_id: int, producers: Seq<Controller<S, I>>)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer.
        forall |s| cluster.init()(s) ==> #[trigger] consumer.init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(controller_fairness::<S, I>(consumer)),
        // The next two preconditions say that no controller (except the consumer itself) interferes with this consumer.
        cluster.controllers.contains_pair(consumer_id, consumer),
        forall |good_citizen_id| cluster.controllers.remove(consumer_id).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, consumer)))),
        // We directly use the temporal spec of the producers.
        forall |p_index: int| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(property::<S, I>(producers[p_index])),
    ensures
        spec.entails(property::<S, I>(consumer)),
{}

// Proof obligation 3:
// Consumer does not interfere with the producer in any cluster.
#[verifier(external_body)]
proof fn consumer_does_not_interfere_with_the_producer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer: Controller<S, I>, producers: Seq<Controller<S, I>>, good_citizen_id: int, p_index: int)
    requires
        0 <= p_index < producers.len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(good_citizen_id, consumer),
    ensures
        // The consumer (which is the good citizen here) never interferes with the producer.
        spec.entails(always(lift_state(one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, producers[p_index])))),
{}

// Proof obligation 4:
// Producer does not interfere with another producer in any cluster.
#[verifier(external_body)]
proof fn producer_does_not_interfere_with_the_producer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, producers: Seq<Controller<S, I>>, good_citizen_id: int, p_index: int, q_index: int)
    requires
        0 <= p_index < producers.len(),
        0 <= q_index < producers.len(),
        // We require the two producers to be different because there is no point to prove
        // a producer does not interfere with another instance of itself.
        p_index != q_index,
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(good_citizen_id, producers[p_index]),
    ensures
        // The producer (p_index, which is the good citizen here) never interferes with the other producer (q_index).
        spec.entails(always(lift_state(one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, producers[q_index])))),
{}

// Proof obligation 5:
// Producer does not interfere with the consumer in any cluster.
#[verifier(external_body)]
proof fn producer_does_not_interfere_with_the_consumer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer: Controller<S, I>, producers: Seq<Controller<S, I>>, good_citizen_id: int, p_index: int)
    requires
        0 <= p_index < producers.len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(good_citizen_id, producers[p_index]),
    ensures
        // The producer (which is the good citizen here) never interferes with the consumer.
        spec.entails(always(lift_state(one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, consumer)))),
{}

// This is a use case of consumer_and_producers_are_correct:
// We can apply consumer_and_producers_are_correct to a concrete cluster that includes
// only a consumer and a sequence of producers.
pub spec fn producers<S, I>() -> Seq<Controller<S, I>>;

pub spec fn consumer<S, I>() -> Controller<S, I>;

// A concrete cluster with only producers and consumer
pub open spec fn consumer_and_producers<S, I>() -> Cluster<S, I> {
    Cluster {
        controllers: Map::new(|k| 0 <= k < producers::<S, I>().len(), |k| producers::<S, I>()[k])
            .insert(producers::<S, I>().len() as int, consumer::<S, I>())
    }
}

proof fn consumer_and_producers_are_correct_in_a_concrete_cluster<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(consumer_and_producers::<S, I>().init())),
        spec.entails(always(lift_action(consumer_and_producers::<S, I>().next()))),
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(controller_fairness::<S, I>(producers()[p_index])),
        spec.entails(controller_fairness::<S, I>(consumer())),
    ensures
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(property::<S, I>(producers()[p_index])),
        spec.entails(property::<S, I>(consumer())),
{
    let cluster = consumer_and_producers::<S, I>();

    let producer_ids = Map::new(|k: int| 0 <= k < producers::<S, I>().len(), |k: int| k);
    let consumer_id = producers::<S, I>().len() as int;

    assert forall |s| #[trigger] cluster.init()(s) implies consumer::<S, I>().init()(s) by {
        assert forall |i| #[trigger] cluster.controllers.contains_key(i) implies cluster.controllers[i].init()(s) by {}
        assert(cluster.controllers.contains_key(consumer_id));
    }

    assert forall |p_index| #![trigger producers::<S, I>()[p_index]] 0 <= p_index < producers::<S, I>().len()
    implies forall |s| #[trigger] cluster.init()(s) ==> producers::<S, I>()[p_index].init()(s) by {
        assert forall |s| #[trigger] cluster.init()(s) implies producers::<S, I>()[p_index].init()(s) by {
            assert forall |i| #[trigger] cluster.controllers.contains_key(i) implies cluster.controllers[i].init()(s) by {}
            assert(cluster.controllers.contains_key(p_index));
        }
    }

    // Due to our cluster construct, you won't find a good_citizen_id that is neither the consumer nor any producer.
    // So we prove the following assertion by contradiction.
    assert forall |good_citizen_id: int|
        #[trigger] cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
    implies
        spec.entails(always(lift_state(one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, consumer()))))
        && forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_this_controller::<S, I>(cluster, good_citizen_id, producers()[p_index]))))
    by {
        assert forall |controller_id| #[trigger] cluster.controllers.contains_key(controller_id)
        implies controller_id == consumer_id || producer_ids.values().contains(controller_id) by {
            if controller_id == producers::<S, I>().len() as int {
                assert(controller_id == consumer_id);
            } else {
                assert(producer_ids.dom().contains(controller_id) && producer_ids[controller_id] == controller_id);
            }
        }
        assert(!cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id));
    }

    consumer_and_producers_are_correct(spec, cluster, consumer(), consumer_id, producers(), producer_ids);
}


}
