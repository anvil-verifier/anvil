// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositionality::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(I)]
pub struct ControllerPredGroup<S, I> {
    pub controller: Controller<S, I>,
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
    pub not_interfered_by: spec_fn(good_citizen_id: int) -> StatePred<S>,
}

proof fn compose_producers<S, I, BC>(spec: TempPred<S>, cluster: Cluster<S, I>, producers: Seq<ControllerPredGroup<S, I>>, producer_ids: Map<int, int>)
    where
        BC: BaseComposition<S, I>,
    requires
        BC::producers() == producers,
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the producer.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |s| #[trigger] cluster.init()(s) ==> producers[p_index].controller.init()(s),
        // The fairness condition is enough to say that each producer runs as part of the cluster's next transition.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> spec.entails(controller_fairness::<S, I>(producers[p_index].controller)),
        // A key exists in producer_ids iff it's within the range of producers,
        // which guarantees that producer_ids covers and only covers all the producers.
        forall |key| #[trigger] producer_ids.contains_key(key) <==> 0 <= key < producers.len(),
        // Each element in producer_ids points to each producer respectively.
        forall |key| producer_ids.contains_key(key)
            ==> cluster.controllers.contains_pair(#[trigger] producer_ids[key], producers[key].controller),
        // For each producer, no other controllers interfere with that producer.
        forall |p_index: int| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |good_citizen_id| cluster.controllers.remove_keys(producer_ids.values()).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))),
    ensures
        // Each producer is correct.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(producers[p_index].property),
        // // For each producer, no one interferes with that producer (except that producer itself).
        // forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
        //     ==> forall |good_citizen_id| cluster.controllers.remove(producer_ids[p_index]).contains_key(good_citizen_id)
        //         ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))),
{
    assert forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
    implies (forall |good_citizen_id| #[trigger] cluster.controllers.remove(producer_ids[p_index]).contains_key(good_citizen_id)
        ==> spec.entails(always(lift_state((producers[p_index].not_interfered_by)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id| cluster.controllers.remove(producer_ids[p_index]).contains_key(good_citizen_id)
        implies spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))) by {
            if producer_ids.values().contains(good_citizen_id) {
                let j = choose |j| producer_ids.dom().contains(j) && #[trigger] producer_ids[j] == good_citizen_id;
                BC::producer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, j, p_index);
            } else {
                assert(spec.entails(always(lift_state((producers[p_index].not_interfered_by)(good_citizen_id)))));
            }
        }
    }

    assert forall |p_index| 0 <= p_index < producers.len() implies #[trigger] spec.entails(producers[p_index].property) by {
        assert(producer_ids.contains_key(p_index));
        let producer_id = producer_ids[p_index];
        BC::producer_is_correct(spec, cluster, producer_id, p_index);
    }
}

pub proof fn compose_producers_and_consumer<S, I, BC>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer: ControllerPredGroup<S, I>, producers: Seq<ControllerPredGroup<S, I>>, consumer_id: int, producer_ids: Map<int, int>)
    where
        BC: BaseComposition<S, I>
    requires
        BC::producers() == producers,
        BC::consumer() == consumer,
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer().
        forall |s| #[trigger] cluster.init()(s) ==> consumer.controller.init()(s),
        // The cluster starts with the initial state of the producer.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |s| #[trigger] cluster.init()(s) ==> producers[p_index].controller.init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(controller_fairness::<S, I>(consumer.controller)),
        // The fairness condition is enough to say that each producer runs as part of the cluster's next transition.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> spec.entails(controller_fairness::<S, I>(producers[p_index].controller)),
        // The consumer().key points to the consumer().controller.
        cluster.controllers.contains_pair(consumer_id, consumer.controller),
        // A key exists in producer_ids iff it's within the range of producers,
        // which guarantees that producer_ids covers and only covers all the producers.
        forall |key| #[trigger] producer_ids.contains_key(key) <==> 0 <= key < producers.len(),
        // Each element in producer_ids points to each producer respectively.
        forall |key| producer_ids.contains_key(key)
            ==> cluster.controllers.contains_pair(#[trigger] producer_ids[key], producers[key].controller),
        // No other controllers interfere with the consumer().
        forall |good_citizen_id| cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (consumer.not_interfered_by)(good_citizen_id)))),
        // For each producer, no other controllers interfere with that producer.
        forall |p_index: int| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |good_citizen_id| cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))),
    ensures
        // Consumer is correct.
        spec.entails(consumer.property),
        // Each producer is correct.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(producers[p_index].property),
        // // No one interferes with the consumer (except the consumer itself).
        // forall |good_citizen_id| cluster.controllers.remove(consumer_id).contains_key(good_citizen_id)
        //     ==> spec.entails(always(lift_state(#[trigger] (consumer.not_interfered_by)(good_citizen_id)))),
        // // For each producer, no one interferes with that producer (except that producer itself).
        // forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
        //     ==> forall |good_citizen_id| cluster.controllers.remove(producer_ids[p_index]).contains_key(good_citizen_id)
        //         ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))),
{
    assert forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
    implies (forall |good_citizen_id| cluster.controllers.remove_keys(producer_ids.values()).contains_key(good_citizen_id)
        ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id| cluster.controllers.remove_keys(producer_ids.values()).contains_key(good_citizen_id)
        implies spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))) by {
            if good_citizen_id == consumer_id {
                BC::consumer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, p_index);
            } else { }
        }
    }

    compose_producers::<S, I, BC>(spec, cluster, producers, producer_ids);

    assert forall |good_citizen_id| cluster.controllers.remove(consumer_id).contains_key(good_citizen_id)
    implies spec.entails(always(lift_state(#[trigger] (consumer.not_interfered_by)(good_citizen_id)))) by {
        if producer_ids.values().contains(good_citizen_id) {
            let j = choose |j| producer_ids.dom().contains(j) && #[trigger] producer_ids[j] == good_citizen_id;
            BC::producer_does_not_interfere_with_the_consumer(spec, cluster, good_citizen_id, j);
        } else {
            assert(spec.entails(always(lift_state((consumer.not_interfered_by)(good_citizen_id)))));
        }
    }
    BC::consumer_is_correct(spec, cluster, consumer_id);
}

pub proof fn compose_consumer_incrementally<S, I, IC>(spec: TempPred<S>, cluster: Cluster<S, I>, consumer: ControllerPredGroup<S, I>, producers: Seq<ControllerPredGroup<S, I>>, consumer_id: int, producer_ids: Map<int, int>)
    where
        IC: IncrementalComposition<S, I>,
    requires
        IC::producers() == producers,
        IC::consumer() == consumer,
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer().
        forall |s| #[trigger] cluster.init()(s) ==> consumer.controller.init()(s),
        // The cluster starts with the initial state of the producer.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |s| #[trigger] cluster.init()(s) ==> producers[p_index].controller.init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(controller_fairness::<S, I>(consumer.controller)),
        // The fairness condition is enough to say that each producer runs as part of the cluster's next transition.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> spec.entails(controller_fairness::<S, I>(producers[p_index].controller)),
        // The consumer().key points to the consumer().controller.
        cluster.controllers.contains_pair(consumer_id, consumer.controller),
        // A key exists in producer_ids iff it's within the range of producers,
        // which guarantees that producer_ids covers and only covers all the producers.
        forall |key| #[trigger] producer_ids.contains_key(key) <==> 0 <= key < producers.len(),
        // Each element in producer_ids points to each producer respectively.
        forall |key| producer_ids.contains_key(key)
            ==> cluster.controllers.contains_pair(#[trigger] producer_ids[key], producers[key].controller),
        // No other controllers interfere with the consumer().
        forall |good_citizen_id| cluster.controllers.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (consumer.not_interfered_by)(good_citizen_id)))),
        // Each producer is correct.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(producers[p_index].property),
    ensures
        // Consumer is correct.
        spec.entails(consumer.property),
        // // No one interferes with the consumer (except the consumer itself).
        // forall |good_citizen_id| cluster.controllers.remove(consumer_id).contains_key(good_citizen_id)
        //     ==> spec.entails(always(lift_state(#[trigger] (consumer.not_interfered_by)(good_citizen_id)))),
{
    assert forall |good_citizen_id| cluster.controllers.remove(consumer_id).contains_key(good_citizen_id)
    implies spec.entails(always(lift_state(#[trigger] (consumer.not_interfered_by)(good_citizen_id)))) by {
        if producer_ids.values().contains(good_citizen_id) {
            let j = choose |j| producer_ids.dom().contains(j) && #[trigger] producer_ids[j] == good_citizen_id;
            IC::producer_does_not_interfere_with_the_consumer(spec, cluster, good_citizen_id, j);
        } else {
            assert(spec.entails(always(lift_state((consumer.not_interfered_by)(good_citizen_id)))));
        }
    }
    IC::consumer_is_correct(spec, cluster, consumer_id);
}

pub trait BaseComposition<S, I>: Sized {

    spec fn consumer() -> ControllerPredGroup<S, I>;

    spec fn producers() -> Seq<ControllerPredGroup<S, I>>;

    // Proof obligation 1:
    // Consumer is correct when running in any cluster where each producer's spec is available and there is no interference.
    proof fn consumer_is_correct(spec: TempPred<S>, cluster: Cluster<S, I>, consumer_id: int)
        requires
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            // The cluster starts with the initial state of the consumer().
            forall |s| cluster.init()(s) ==> #[trigger] Self::consumer().controller.init()(s),
            // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
            spec.entails(controller_fairness::<S, I>(Self::consumer().controller)),
            // The next two preconditions say that no controller (except the consumer itself) interferes with this consumer().
            cluster.controllers.contains_pair(consumer_id, Self::consumer().controller),
            forall |good_citizen_id| cluster.controllers.remove(consumer_id).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (Self::consumer().not_interfered_by)(good_citizen_id)))),
            // We directly use the temporal property of the producers().
            forall |p_index: int| 0 <= p_index < Self::producers().len()
                ==> #[trigger] spec.entails(Self::producers()[p_index].property),
        ensures
            spec.entails(Self::consumer().property),
        ;

    // Proof obligation 2:
    // Producer is correct when running in any cluster where there is no interference.
    proof fn producer_is_correct(spec: TempPred<S>, cluster: Cluster<S, I>, producer_id: int, p_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            // The cluster starts with the initial state of the producer.
            forall |s| cluster.init()(s) ==> #[trigger] Self::producers()[p_index].controller.init()(s),
            // The fairness condition is enough to say that the producer runs as part of the cluster's next transition.
            spec.entails(controller_fairness::<S, I>(Self::producers()[p_index].controller)),
            // The next two preconditions say that no controller (except the producer itself) interferes with this producer.
            cluster.controllers.contains_pair(producer_id, Self::producers()[p_index].controller),
            forall |good_citizen_id| cluster.controllers.remove(producer_id).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (Self::producers()[p_index].not_interfered_by)(good_citizen_id)))),
        ensures
            spec.entails(Self::producers()[p_index].property),
        ;

    // Proof obligation 3:
    // Consumer does not interfere with the producer in any cluster.
    proof fn consumer_does_not_interfere_with_the_producer(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            cluster.controllers.contains_pair(good_citizen_id, Self::consumer().controller),
        ensures
            // The consumer never interferes with the producer.
            spec.entails(always(lift_state((Self::producers()[p_index].not_interfered_by)(good_citizen_id)))),
        ;

    // Proof obligation 4:
    // Producer does not interfere with the consumer in any cluster.
    proof fn producer_does_not_interfere_with_the_consumer(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            cluster.controllers.contains_pair(good_citizen_id, Self::producers()[p_index].controller),
        ensures
            // The producer never interferes with the consumer().
            spec.entails(always(lift_state((Self::consumer().not_interfered_by)(good_citizen_id)))),
        ;

    // Proof obligation 5:
    // Producer does not interfere with another producer in any cluster.
    proof fn producer_does_not_interfere_with_the_producer(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int, q_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            0 <= q_index < Self::producers().len(),
            // We require the two producers to be different because there is no point to prove
            // a producer does not interfere with another instance of itself.
            p_index != q_index,
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            cluster.controllers.contains_pair(good_citizen_id, Self::producers()[p_index].controller),
        ensures
            // The producer (p_index) never interferes with the other producer (q_index).
            spec.entails(always(lift_state((Self::producers()[q_index].not_interfered_by)(good_citizen_id)))),
        ;
}

pub trait IncrementalComposition<S, I>: Sized {

    spec fn consumer() -> ControllerPredGroup<S, I>;

    spec fn producers() -> Seq<ControllerPredGroup<S, I>>;

    // Proof obligation 1:
    // Consumer is correct when running in any cluster where each producer's spec is available and there is no interference.
    proof fn consumer_is_correct(spec: TempPred<S>, cluster: Cluster<S, I>, consumer_id: int)
        requires
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            // The cluster starts with the initial state of the consumer().
            forall |s| cluster.init()(s) ==> #[trigger] Self::consumer().controller.init()(s),
            // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
            spec.entails(controller_fairness::<S, I>(Self::consumer().controller)),
            // The next two preconditions say that no controller (except the consumer itself) interferes with this consumer().
            cluster.controllers.contains_pair(consumer_id, Self::consumer().controller),
            forall |good_citizen_id| cluster.controllers.remove(consumer_id).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (Self::consumer().not_interfered_by)(good_citizen_id)))),
            // We directly use the temporal property of the producers().
            forall |p_index: int| 0 <= p_index < Self::producers().len()
                ==> #[trigger] spec.entails(Self::producers()[p_index].property),
        ensures
            spec.entails(Self::consumer().property),
        ;

    // Proof obligation 2:
    // Consumer does not interfere with the producer in any cluster.
    proof fn consumer_does_not_interfere_with_the_producer(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            cluster.controllers.contains_pair(good_citizen_id, Self::consumer().controller),
        ensures
            // The consumer never interferes with the producer.
            spec.entails(always(lift_state((Self::producers()[p_index].not_interfered_by)(good_citizen_id)))),
        ;

    // Proof obligation 3:
    // Producer does not interfere with the consumer in any cluster.
    proof fn producer_does_not_interfere_with_the_consumer(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            cluster.controllers.contains_pair(good_citizen_id, Self::producers()[p_index].controller),
        ensures
            // The producer never interferes with the consumer().
            spec.entails(always(lift_state((Self::consumer().not_interfered_by)(good_citizen_id)))),
        ;
}


}
