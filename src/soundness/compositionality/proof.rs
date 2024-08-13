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
// Note that the invariant likely will not hold when good_citizen_id points to the consumer itself, that is,
// if there are two consumers, they will interfere with each other.
// This is not a problem because there is no reason to run two separate consumer instances at the same time.
// However, when proving the invariant we need to be careful so that good_citizen_id does not point to another consumer.
spec fn one_does_not_interfere_with_consumer<S, I>(cluster: Cluster<S, I>, good_citizen_id: int) -> StatePred<S>;

// The inv asserts that the controller indexed by good_citizen_id does not interfere with the producer's reconcile
spec fn one_does_not_interfere_with_producer<S, I>(cluster: Cluster<S, I>, good_citizen_id: int, p_index: int) -> StatePred<S>;

// The only reason I need this spec fun is to use it as a trigger (in the case that no one else can serve as a trigger).
pub open spec fn within_range<A>(seq: Seq<A>, index: int) -> bool {
    0 <= index < seq.len()
}

pub open spec fn consumer_and_producers<S, I>() -> Cluster<S, I> {
    Cluster {
        controllers: producers::<S, I>().push(consumer::<S, I>()),
    }
}

// This is our end-goal theorem: in a cluster with all the producers and the consumer,
// all controllers are correct.
proof fn consumer_and_producer_properties_hold_in_a_concrete_cluster<S, I>(spec: TempPred<S>)
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

    let producer_ids = producers::<S, I>().map(|i: int, producer: Controller<S, I>| i);
    let consumer_id = cluster.controllers.len() - 1;

    assert forall |s| #[trigger] cluster.init()(s) implies consumer::<S, I>().init()(s) by {
        assert forall |i| 0 <= i < cluster.controllers.len() implies #[trigger] cluster.controllers[i].init()(s) by {}
        assert(consumer::<S, I>() =~= cluster.controllers.last());
    }

    assert forall |p_index| #![trigger producers::<S, I>()[p_index]] 0 <= p_index < producers::<S, I>().len()
    implies forall |s| #[trigger] cluster.init()(s) ==> producers::<S, I>()[p_index].init()(s) by {
        assert forall |s| #[trigger] cluster.init()(s) implies producers::<S, I>()[p_index].init()(s) by {
            assert forall |i| 0 <= i < cluster.controllers.len() implies #[trigger] cluster.controllers[i].init()(s) by {}
            assert(producers::<S, I>()[p_index] =~= cluster.controllers[p_index]);
        }
    }

    assert forall |good_citizen_id: int| 0 <= good_citizen_id < cluster.controllers.len()
        && good_citizen_id != consumer_id
        && !(exists |i| 0 <= i < producer_ids.len() && good_citizen_id == producer_ids[i])
    implies
        spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id))))
        && forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index))))
    by {
        assert forall |controller_id| #[trigger] within_range(cluster.controllers, controller_id)
        implies controller_id == consumer_id || exists |i| #[trigger] within_range(producer_ids, i) && controller_id == producer_ids[i] by {
            if controller_id == cluster.controllers.len() - 1 {
                assert(controller_id == consumer_id);
            } else {
                let i = controller_id;
                assert(within_range(producer_ids, i) && controller_id == producer_ids[i]);
            }
        }
        assert(within_range(cluster.controllers, good_citizen_id));
        assert(good_citizen_id == consumer_id || exists |i| #[trigger] within_range(producer_ids, i) && good_citizen_id == producer_ids[i]);
    }

    consumer_and_producer_properties_hold(spec, cluster, consumer_id, producer_ids);
}

proof fn consumer_and_producer_properties_hold<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer_id: int, producer_ids: Seq<int>)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer.
        forall |s| cluster.init()(s) ==> #[trigger] consumer::<S, I>().init()(s),
        // The cluster starts with the initial state of the producer.
        forall |p_index: int| #![trigger producers::<S, I>()[p_index]] 0 <= p_index < producers::<S, I>().len()
            ==> forall |s| cluster.init()(s) ==> #[trigger] producers::<S, I>()[p_index].init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(consumer_fairness::<S, I>()),
        // The fairness condition is enough to say that each producer runs as part of the cluster's next transition.
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(producer_fairness::<S, I>(p_index)),
        // The next five preconditions say that each consumer/producer id points to the consumer and producers
        // in cluster.controllers.
        0 <= consumer_id < cluster.controllers.len(),
        producer_ids.len() == producers::<S, I>().len(),
        forall |i| #![trigger producer_ids[i]] 0 <= i < producer_ids.len() ==> 0 <= producer_ids[i] < cluster.controllers.len(),
        cluster.controllers[consumer_id] == consumer::<S, I>(),
        forall |i| #![trigger producer_ids[i]] 0 <= i < producer_ids.len() ==> cluster.controllers[producer_ids[i]] == producers::<S, I>()[i],
        // For any other controller in the cluster that is not pointed by the consumer or producer id...
        forall |good_citizen_id: int| 0 <= good_citizen_id < cluster.controllers.len()
            && good_citizen_id != consumer_id
            && !(exists |i| 0 <= i < producer_ids.len() && good_citizen_id == producer_ids[i])
            // ..., that controller does not interfere with the consumer...
            ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id))))
                // ...and does not interfere with any producer.
                && forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
                    ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index))))
    ensures
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(producer_property::<S>(p_index)),
        spec.entails(consumer_property::<S>()),
{
    assert forall |p_index| 0 <= p_index < producers::<S, I>().len() implies #[trigger] spec.entails(producer_property::<S>(p_index)) by {
        let producer_id = producer_ids[p_index];
        assert forall |good_citizen_id| 0 <= good_citizen_id < cluster.controllers.len() && good_citizen_id != producer_id
        implies spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index)))) by {
            if good_citizen_id == consumer_id {
                consumer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, p_index);
            } else if exists |j| 0 <= j < producer_ids.len() && good_citizen_id == producer_ids[j] {
                let j = choose |j| 0 <= j < producer_ids.len() && good_citizen_id == producer_ids[j];
                assert(cluster.controllers[good_citizen_id] == producers::<S, I>()[j]);
                producer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, j, p_index);
            } else {
                assert(spec.entails(always(lift_state(one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id))))); // this assert is just used for triggering
                assert(spec.entails(always(lift_state(one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index)))));
            }
        }
        producer_property_holds_if_no_interference(spec, cluster, producer_id, p_index);
    }

    assert forall |good_citizen_id| 0 <= good_citizen_id < cluster.controllers.len() && good_citizen_id != consumer_id
    implies spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id)))) by {
        if exists |j| 0 <= j < producer_ids.len() && good_citizen_id == producer_ids[j] {
            let j = choose |j| 0 <= j < producer_ids.len() && good_citizen_id == producer_ids[j];
            producer_does_not_interfere_with_the_consumer(spec, cluster, good_citizen_id, j);
        } else {
            assert(spec.entails(always(lift_state(one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id)))));
        }
    }
    consumer_property_holds_if_no_interference(spec, cluster, consumer_id);
}

// To prove the above theorem, there are three proof obligations.

// Proof obligation 1:
// Producer is correct when running in any cluster where there is no interference.
#[verifier(external_body)]
proof fn producer_property_holds_if_no_interference<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, producer_id: int, p_index: int)
    requires
        0 <= p_index < producers::<S, I>().len(),
        0 <= producer_id < cluster.controllers.len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the producer.
        forall |s| cluster.init()(s) ==> #[trigger] producers::<S, I>()[p_index].init()(s),
        // The fairness condition is enough to say that the producer runs as part of the cluster's next transition.
        spec.entails(producer_fairness::<S, I>(p_index)),
        // The next two preconditions say that no controller (except the producer itself) interferes with this producer.
        cluster.controllers[producer_id] == producers::<S, I>()[p_index],
        forall |good_citizen_id| 0 <= good_citizen_id < cluster.controllers.len() && good_citizen_id != producer_id
            ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index)))),
    ensures
        spec.entails(producer_property::<S>(p_index)),
{}

// Proof obligation 2:
// Consumer is correct when running in any cluster where each producer's spec is available and there is no interference.
#[verifier(external_body)]
proof fn consumer_property_holds_if_no_interference<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer_id: int)
    requires
        0 <= consumer_id < cluster.controllers.len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer.
        forall |s| cluster.init()(s) ==> #[trigger] consumer::<S, I>().init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(consumer_fairness::<S, I>()),
        // The next two preconditions say that no controller (except the consumer itself) interferes with this consumer.
        cluster.controllers[consumer_id] == consumer::<S, I>(),
        forall |good_citizen_id| 0 <= good_citizen_id < cluster.controllers.len() && good_citizen_id != consumer_id
            ==> spec.entails(always(lift_state(#[trigger] one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id)))),
        // We directly use the temporal spec of the producers.
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(producer_property::<S>(p_index)),
    ensures
        spec.entails(consumer_property::<S>()),
{}

// Proof obligation 3:
// Consumer does not interfere with the producer.
#[verifier(external_body)]
proof fn consumer_does_not_interfere_with_the_producer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int)
    requires
        0 <= p_index < producers::<S, I>().len(),
        0 <= good_citizen_id < cluster.controllers.len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers[good_citizen_id] == consumer::<S, I>(),
    ensures
        // The consumer (which is the good citizen here) never interferes with the producer.
        spec.entails(always(lift_state(one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, p_index)))),
{}


#[verifier(external_body)]
proof fn producer_does_not_interfere_with_the_consumer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int)
    requires
        0 <= p_index < producers::<S, I>().len(),
        0 <= good_citizen_id < cluster.controllers.len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers[good_citizen_id] == producers::<S, I>()[p_index],
    ensures
        // The producer (which is the good citizen here) never interferes with the consumer.
        spec.entails(always(lift_state(one_does_not_interfere_with_consumer::<S, I>(cluster, good_citizen_id)))),
{}

#[verifier(external_body)]
proof fn producer_does_not_interfere_with_the_producer<S, I>(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int, q_index: int)
    requires
        0 <= p_index < producers::<S, I>().len(),
        0 <= q_index < producers::<S, I>().len(),
        p_index != q_index,
        0 <= good_citizen_id < cluster.controllers.len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers[good_citizen_id] == producers::<S, I>()[p_index],
    ensures
        // The producer (p_index, which is the good citizen here) never interferes with the other producer (q_index).
        spec.entails(always(lift_state(one_does_not_interfere_with_producer::<S, I>(cluster, good_citizen_id, q_index)))),
{}

}
