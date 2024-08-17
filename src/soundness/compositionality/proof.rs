// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositionality::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(I)]
pub struct ControllerSpecGroup<S, I> {
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
    pub not_interfered_by: spec_fn(good_citizen_id: int) -> StatePred<S>,
}

pub trait Compositional<S, I>: Sized {

    spec fn consumer() -> ControllerSpecGroup<S, I>;

    spec fn producers() -> Seq<ControllerSpecGroup<S, I>>;

// This is our top-level theorem: the consumer and producers are correct in any cluster
// if the other controllers in that cluster do not interfere with the consumer or Self::producers().
proof fn consumer_and_producers_are_correct(spec: TempPred<S>, cluster: Cluster<S, I>)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer().
        forall |s| #[trigger] cluster.init()(s) ==> Self::consumer().controller.init()(s),
        // The cluster starts with the initial state of the producer.
        forall |p_index| #![trigger Self::producers()[p_index]] 0 <= p_index < Self::producers().len()
            ==> forall |s| #[trigger] cluster.init()(s) ==> Self::producers()[p_index].controller.init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(controller_fairness::<S, I>(Self::consumer().controller)),
        // The fairness condition is enough to say that each producer runs as part of the cluster's next transition.
        forall |p_index| #![trigger Self::producers()[p_index]] 0 <= p_index < Self::producers().len()
            ==> spec.entails(controller_fairness::<S, I>(Self::producers()[p_index].controller)),
        // The consumer().key points to the consumer().controller.
        cluster.controllers.contains_pair(Self::consumer().key, Self::consumer().controller),
        // Each producers()[p_index].key points to producers()[p_index].controller.
        forall |p_index| #![trigger Self::producers()[p_index]] 0 <= p_index < Self::producers().len()
            ==> cluster.controllers.contains_pair(Self::producers()[p_index].key, Self::producers()[p_index].controller),
        // No other controllers interfere with the consumer().
        forall |good_citizen_id| cluster.controllers.remove(Self::consumer().key).remove_keys(Self::producers().map_values(|p: ControllerSpecGroup<S, I>| p.key).to_set()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (Self::consumer().not_interfered_by)(good_citizen_id)))),
        // For each producer, no other controllers interfere with that producer.
        forall |p_index: int| #![trigger Self::producers()[p_index]] 0 <= p_index < Self::producers().len()
            ==> forall |good_citizen_id| cluster.controllers.remove(Self::consumer().key).remove_keys(Self::producers().map_values(|p: ControllerSpecGroup<S, I>| p.key).to_set()).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (Self::producers()[p_index].not_interfered_by)(good_citizen_id))))
    ensures
        // Consumer is correct.
        spec.entails(Self::consumer().property),
        // Each producer is correct.
        forall |p_index| 0 <= p_index < Self::producers().len()
            ==> #[trigger] spec.entails(Self::producers()[p_index].property),
        // No one interferes with the consumer (except the consumer itself).
        forall |good_citizen_id| cluster.controllers.remove(Self::consumer().key).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (Self::consumer().not_interfered_by)(good_citizen_id)))),
        // For each producer, no one interferes with that producer (except that producer itself).
        forall |p_index| #![trigger Self::producers()[p_index]] 0 <= p_index < Self::producers().len()
            ==> forall |good_citizen_id| cluster.controllers.remove(Self::producers()[p_index].key).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (Self::producers()[p_index].not_interfered_by)(good_citizen_id)))),
{
    assert forall |p_index| #![trigger Self::producers()[p_index]] 0 <= p_index < Self::producers().len()
    implies (forall |good_citizen_id| #[trigger] cluster.controllers.remove(Self::producers()[p_index].key).contains_key(good_citizen_id)
        ==> spec.entails(always(lift_state((Self::producers()[p_index].not_interfered_by)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id| cluster.controllers.remove(Self::producers()[p_index].key).contains_key(good_citizen_id)
        implies spec.entails(always(lift_state(#[trigger] (Self::producers()[p_index].not_interfered_by)(good_citizen_id)))) by {
            if good_citizen_id == Self::consumer().key {
                Self::consumer_does_not_interfere_with_the_producer(spec, cluster, p_index);
            } else if Self::producers().map_values(|p: ControllerSpecGroup<S, I>| p.key).to_set().contains(good_citizen_id) {
                let j = choose |j| 0 <= j < Self::producers().len() && #[trigger] Self::producers()[j].key == good_citizen_id;
                Self::producer_does_not_interfere_with_the_producer(spec, cluster, j, p_index);
            } else {
                assert(spec.entails(always(lift_state((Self::producers()[p_index].not_interfered_by)(good_citizen_id)))));
            }
        }
    }

    assert forall |p_index| 0 <= p_index < Self::producers().len() implies #[trigger] spec.entails(Self::producers()[p_index].property) by {
        Self::producer_is_correct(spec, cluster, p_index);
    }

    assert forall |good_citizen_id| cluster.controllers.remove(Self::consumer().key).contains_key(good_citizen_id)
    implies spec.entails(always(lift_state(#[trigger] (Self::consumer().not_interfered_by)(good_citizen_id)))) by {
        if Self::producers().map_values(|p: ControllerSpecGroup<S, I>| p.key).to_set().contains(good_citizen_id) {
            let j = choose |j| 0 <= j < Self::producers().len() && #[trigger] Self::producers()[j].key == good_citizen_id;
            Self::producer_does_not_interfere_with_the_consumer(spec, cluster, j);
        } else {
            assert(spec.entails(always(lift_state((Self::consumer().not_interfered_by)(good_citizen_id)))));
        }
    }
    Self::consumer_is_correct(spec, cluster);
}

// To prove consumer_and_producers_are_correct, there are five proof obligations.

// Proof obligation 1:
// Producer is correct when running in any cluster where there is no interference.
proof fn producer_is_correct(spec: TempPred<S>, cluster: Cluster<S, I>, p_index: int)
    requires
        0 <= p_index < Self::producers().len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the producer.
        forall |s| cluster.init()(s) ==> #[trigger] Self::producers()[p_index].controller.init()(s),
        // The fairness condition is enough to say that the producer runs as part of the cluster's next transition.
        spec.entails(controller_fairness::<S, I>(Self::producers()[p_index].controller)),
        // The next two preconditions say that no controller (except the producer itself) interferes with this producer.
        cluster.controllers.contains_pair(Self::producers()[p_index].key, Self::producers()[p_index].controller),
        forall |good_citizen_id| cluster.controllers.remove(Self::producers()[p_index].key).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (Self::producers()[p_index].not_interfered_by)(good_citizen_id)))),
    ensures
        spec.entails(Self::producers()[p_index].property),
    ;

// Proof obligation 2:
// Consumer is correct when running in any cluster where each producer's spec is available and there is no interference.
proof fn consumer_is_correct(spec: TempPred<S>, cluster: Cluster<S, I>)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The cluster starts with the initial state of the consumer().
        forall |s| cluster.init()(s) ==> #[trigger] Self::consumer().controller.init()(s),
        // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
        spec.entails(controller_fairness::<S, I>(Self::consumer().controller)),
        // The next two preconditions say that no controller (except the consumer itself) interferes with this consumer().
        cluster.controllers.contains_pair(Self::consumer().key, Self::consumer().controller),
        forall |good_citizen_id| cluster.controllers.remove(Self::consumer().key).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (Self::consumer().not_interfered_by)(good_citizen_id)))),
        // We directly use the temporal property of the producers().
        forall |p_index: int| 0 <= p_index < Self::producers().len()
            ==> #[trigger] spec.entails(Self::producers()[p_index].property),
    ensures
        spec.entails(Self::consumer().property),
    ;

// Proof obligation 3:
// Consumer does not interfere with the producer in any cluster.
proof fn consumer_does_not_interfere_with_the_producer(spec: TempPred<S>, cluster: Cluster<S, I>, p_index: int)
    requires
        0 <= p_index < Self::producers().len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(Self::consumer().key, Self::consumer().controller),
    ensures
        // The consumer never interferes with the producer.
        spec.entails(always(lift_state((Self::producers()[p_index].not_interfered_by)(Self::consumer().key)))),
    ;

// Proof obligation 4:
// Producer does not interfere with another producer in any cluster.
proof fn producer_does_not_interfere_with_the_producer(spec: TempPred<S>, cluster: Cluster<S, I>, p_index: int, q_index: int)
    requires
        0 <= p_index < Self::producers().len(),
        0 <= q_index < Self::producers().len(),
        // We require the two producers to be different because there is no point to prove
        // a producer does not interfere with another instance of itself.
        p_index != q_index,
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(Self::producers()[p_index].key, Self::producers()[p_index].controller),
    ensures
        // The producer (p_index) never interferes with the other producer (q_index).
        spec.entails(always(lift_state((Self::producers()[q_index].not_interfered_by)(Self::producers()[p_index].key)))),
    ;

// Proof obligation 5:
// Producer does not interfere with the consumer in any cluster.
proof fn producer_does_not_interfere_with_the_consumer(spec: TempPred<S>, cluster: Cluster<S, I>, p_index: int)
    requires
        0 <= p_index < Self::producers().len(),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controllers.contains_pair(Self::producers()[p_index].key, Self::producers()[p_index].controller),
    ensures
        // The producer never interferes with the consumer().
        spec.entails(always(lift_state((Self::consumer().not_interfered_by)(Self::producers()[p_index].key)))),
    ;

}

}
