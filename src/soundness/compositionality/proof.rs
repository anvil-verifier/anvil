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

// The inv asserts that the controller indexed by good_citizen_id does not interfere with the consumer's reconcile
// This invariant, if opened, should state something like:
// forall |message| message is sent by the controller indexed by good_citizen_id ==> message does not modify object X,
// where X is something that the consumer cares about.
//
// To tell whether a message in the network is sent by a controller, our cluster state machine should attach the
// controller id (the index) to each message sent by the controller, regardless of the controller's implementation.
//
// Note that the invariant likely does not hold when good_citizen_id points to the consumer itself, that is,
// if there are two consumers, they will interfere with each other.
// This is not a problem because there is no reason to run two separate consumer instances at the same time.
// However, when proving the invariant we need to be careful so that good_citizen_id does not point to another
// consumer instance.
spec fn one_does_not_interfere_with_consumer<S, I>(cluster: Cluster<S, I>, good_citizen_id: int) -> StatePred<S>;

// The inv asserts that the controller indexed by good_citizen_id does not interfere with the producer's reconcile,
// similar to the one above.
spec fn one_does_not_interfere_with_producer<S, I>(cluster: Cluster<S, I>, good_citizen_id: int, p_index: int) -> StatePred<S>;

// The only reason I need this spec fun is to use it as a trigger in the case that no one else can serve as a trigger.
pub open spec fn within_range<A>(seq: Seq<A>, index: int) -> bool {
    0 <= index < seq.len()
}

// This is our top-level theorem: the consumer and producers are correct in any cluster
// if the other controllers in that cluster do not interfere with the consumer or producers.
// # Arguments:
// * spec: the temporal predicate that represents the state machine
// * cluster: the cluster that we want to run the consumers/producers in
// * consumer_id: the key of the consumer in cluster.controllers
// * producer_ids: maps the index of each producer to the key used in cluster.controllers
proof fn consumer_and_producers_are_correct<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer_id: int, producer_ids: Map<int, int>)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer.
        forall |s| cluster.init()(s) ==> #[trigger] consumer::<S, I>().init()(s),
        // The cluster starts with the initial state of the producer.
        forall |p_index| #![trigger producers::<S, I>()[p_index]] 0 <= p_index < producers::<S, I>().len()
            ==> forall |s| cluster.init()(s) ==> #[trigger] producers::<S, I>()[p_index].init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(consumer_fairness::<S, I>()),
        // The fairness condition is enough to say that each producer runs as part of the cluster's next transition.
        forall |p_index| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(producer_fairness::<S, I>(p_index)),
        // The consumer_id points to the consumer.
        cluster.controllers.contains_pair(consumer_id, consumer::<S, I>()),
        // Each element in producer_ids points to each producer respectively,
        // and each producer is pointed by some element in producer_ids.
        forall |key| #[trigger] producer_ids.contains_key(key) <==> 0 <= key < producers::<S, I>().len(),
        forall |key| producer_ids.contains_key(key)
            ==> cluster.controllers.contains_pair(#[trigger] producer_ids[key], producers::<S, I>()[key]),
        // For any other controller in the cluster that is not pointed by the consumer or producer id,
        // that controller does not interfere with the consumer or any producer.
        forall |good_citizen_id| #[trigger] cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id))))
                && forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
                    ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index))))
    ensures
        spec.entails(consumer_property::<S>()),
        forall |good_citizen_id| #[trigger] cluster.controllers.contains_key(good_citizen_id) && good_citizen_id != consumer_id
            ==> spec.entails(always(lift_state(one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id)))),
        forall |p_index| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(producer_property::<S>(p_index)),
        forall |p_index| #![trigger producer_ids[p_index]] 0 <= p_index < producers::<S, I>().len()
            ==> forall |good_citizen_id| #[trigger] cluster.controllers.contains_key(good_citizen_id) && good_citizen_id != producer_ids[p_index]
                ==> spec.entails(always(lift_state(one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index)))),
{
    assert forall |p_index| #![trigger producer_ids[p_index]] 0 <= p_index < producers::<S, I>().len()
    implies (forall |good_citizen_id| #[trigger] cluster.controllers.contains_key(good_citizen_id) && good_citizen_id != producer_ids[p_index]
        ==> spec.entails(always(lift_state(one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index)))))
    by {
        assert forall |good_citizen_id| #[trigger] cluster.controllers.contains_key(good_citizen_id) && good_citizen_id != producer_ids[p_index]
        implies spec.entails(always(lift_state(one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index)))) by {
            if good_citizen_id == consumer_id {
                consumer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, p_index);
            } else if producer_ids.contains_value(good_citizen_id) {
                let j = choose |j| producer_ids.dom().contains(j) && #[trigger] producer_ids[j] == good_citizen_id;
                producer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, j, p_index);
            } else {
                assert(cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id));
                assert(spec.entails(always(lift_state(one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index)))));
            }
        }
    }

    assert forall |p_index| 0 <= p_index < producers::<S, I>().len() implies #[trigger] spec.entails(producer_property::<S>(p_index)) by {
        assert(producer_ids.contains_key(p_index));
        let producer_id = producer_ids[p_index];
        producer_is_correct(spec, cluster, producer_id, p_index);
    }

    assert forall |good_citizen_id| cluster.controllers.contains_key(good_citizen_id) && good_citizen_id != consumer_id
    implies spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id)))) by {
        if producer_ids.contains_value(good_citizen_id) {
            let j = choose |j| producer_ids.dom().contains(j) && #[trigger] producer_ids[j] == good_citizen_id;
            producer_does_not_interfere_with_the_consumer(spec, cluster, good_citizen_id, j);
        } else {
            assert(cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id));
            assert(spec.entails(always(lift_state(one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id)))));
        }
    }
    consumer_is_correct(spec, cluster, consumer_id);
}

// A concrete cluster with only producers and consumer
pub open spec fn consumer_and_producers<S, I>() -> Cluster<S, I> {
    Cluster {
        controllers: Map::new(|k| 0 <= k < producers::<S, I>().len(), |k| producers::<S, I>()[k])
            .insert(producers::<S, I>().len() as int, consumer::<S, I>())
    }
}

// We can apply consumer_and_producers_are_correct to the concrete cluster above to conclude that
// the consumer and producers are correct in a cluster where there are only consumer and producers.
proof fn consumer_and_producers_are_correct_in_a_concrete_cluster<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(consumer_and_producers::<S, I>().init())),
        spec.entails(always(lift_action(consumer_and_producers::<S, I>().next()))),
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(producer_fairness::<S, I>(p_index)),
        spec.entails(consumer_fairness::<S, I>()),
    ensures
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(producer_property::<S>(p_index)),
        spec.entails(consumer_property::<S>()),
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
        spec.entails(always(lift_state(one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id))))
        && forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index))))
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

    consumer_and_producers_are_correct(spec, cluster, consumer_id, producer_ids);
}

// To prove consumer_and_producers_are_correct, there are five proof obligations.

// Proof obligation 1:
// Producer is correct when running in any cluster where there is no interference.
#[verifier(external_body)]
proof fn producer_is_correct<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, producer_id: int, p_index: int)
    requires
        0 <= p_index < producers::<S, I>().len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the producer.
        forall |s| cluster.init()(s) ==> #[trigger] producers::<S, I>()[p_index].init()(s),
        // The fairness condition is enough to say that the producer runs as part of the cluster's next transition.
        spec.entails(producer_fairness::<S, I>(p_index)),
        // The next two preconditions say that no controller (except the producer itself) interferes with this producer.
        cluster.controllers.contains_pair(producer_id, producers::<S, I>()[p_index]),
        forall |good_citizen_id| cluster.controllers.contains_key(good_citizen_id) && good_citizen_id != producer_id
            ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index)))),
    ensures
        spec.entails(producer_property::<S>(p_index)),
{}

// Proof obligation 2:
// Consumer is correct when running in any cluster where each producer's spec is available and there is no interference.
#[verifier(external_body)]
proof fn consumer_is_correct<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer.
        forall |s| cluster.init()(s) ==> #[trigger] consumer::<S, I>().init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(consumer_fairness::<S, I>()),
        // The next two preconditions say that no controller (except the consumer itself) interferes with this consumer.
        cluster.controllers.contains_pair(consumer_id, consumer::<S, I>()),
        forall |good_citizen_id| cluster.controllers.contains_key(good_citizen_id) && good_citizen_id != consumer_id
            ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id)))),
        // We directly use the temporal spec of the producers.
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(producer_property::<S>(p_index)),
    ensures
        spec.entails(consumer_property::<S>()),
{}

// Proof obligation 3:
// Consumer does not interfere with the producer in any cluster.
#[verifier(external_body)]
proof fn consumer_does_not_interfere_with_the_producer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int)
    requires
        0 <= p_index < producers::<S, I>().len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(good_citizen_id, consumer::<S, I>()),
    ensures
        // The consumer (which is the good citizen here) never interferes with the producer.
        spec.entails(always(lift_state(one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index)))),
{}

// Proof obligation 4:
// Producer does not interfere with another producer in any cluster.
#[verifier(external_body)]
proof fn producer_does_not_interfere_with_the_producer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int, q_index: int)
    requires
        0 <= p_index < producers::<S, I>().len(),
        0 <= q_index < producers::<S, I>().len(),
        // We require the two producers to be different because there is no point to prove
        // a producer does not interfere with another instance of itself.
        p_index != q_index,
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(good_citizen_id, producers::<S, I>()[p_index]),
    ensures
        // The producer (p_index, which is the good citizen here) never interferes with the other producer (q_index).
        spec.entails(always(lift_state(one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, q_index)))),
{}

// Proof obligation 5:
// Producer does not interfere with the consumer in any cluster.
#[verifier(external_body)]
proof fn producer_does_not_interfere_with_the_consumer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int)
    requires
        0 <= p_index < producers::<S, I>().len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(good_citizen_id, producers::<S, I>()[p_index]),
    ensures
        // The producer (which is the good citizen here) never interferes with the consumer.
        spec.entails(always(lift_state(one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id)))),
{}

}
