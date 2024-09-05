// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster_v2::spec::{
    cluster_state_machine::*, controller::state_machine::controller,
};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub struct ControllerPredGroup {
    pub controller: ControllerModel,
    // The top level property of the input controller (e.g., ESR)
    pub property: TempPred<ClusterState>,
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
    pub not_interfered_by: spec_fn(good_citizen_id: int) -> StatePred<ClusterState>,
}

proof fn compose_horizontally<HC>(spec: TempPred<ClusterState>, cluster: Cluster, producers: Seq<ControllerPredGroup>, producer_ids: Map<int, int>)
    where
        HC: HorizontalComposition,
    requires
        HC::producers() == producers,
        // A key exists in producer_ids iff it's within the range of producers,
        // which guarantees that producer_ids covers and only covers all the producers.
        forall |key| #[trigger] producer_ids.contains_key(key) <==> 0 <= key < producers.len(),
        // Each element in producer_ids points to each producer respectively.
        forall |key| producer_ids.contains_key(key)
            ==> cluster.controller_models.contains_pair(#[trigger] producer_ids[key], producers[key].controller),
        // The cluster starts with the initial state of the producer.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |s| #[trigger] cluster.init()(s)
                ==> (controller(HC::producers()[p_index].controller.reconcile_model, producer_ids[p_index]).init)(s.controller_and_externals[producer_ids[p_index]].controller),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The fairness conditions for all the producers.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> spec.entails(tla_forall(|input| cluster.chosen_controller_next(producer_ids[p_index]).weak_fairness(input))),
        // For each producer, no other controllers interfere with that producer.
        forall |p_index: int| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |good_citizen_id| cluster.controller_models.remove_keys(producer_ids.values()).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))),
    ensures
        // Each producer is correct.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(producers[p_index].property),
{
    assert forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
    implies (forall |good_citizen_id| #[trigger] cluster.controller_models.remove(producer_ids[p_index]).contains_key(good_citizen_id)
        ==> spec.entails(always(lift_state((producers[p_index].not_interfered_by)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id| cluster.controller_models.remove(producer_ids[p_index]).contains_key(good_citizen_id)
        implies spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))) by {
            if producer_ids.values().contains(good_citizen_id) {
                let j = choose |j| producer_ids.dom().contains(j) && #[trigger] producer_ids[j] == good_citizen_id;
                HC::producer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, j, p_index);
            } else {
                assert(spec.entails(always(lift_state((producers[p_index].not_interfered_by)(good_citizen_id)))));
            }
        }
    }

    assert forall |p_index| 0 <= p_index < producers.len() implies #[trigger] spec.entails(producers[p_index].property) by {
        assert(producer_ids.contains_key(p_index));
        let producer_id = producer_ids[p_index];
        HC::producer_is_correct(spec, cluster, producer_id, p_index);
    }
}

pub proof fn compose_vertically<VC>(spec: TempPred<ClusterState>, cluster: Cluster, consumer: ControllerPredGroup, producers: Seq<ControllerPredGroup>, consumer_id: int, producer_ids: Map<int, int>)
    where
        VC: VerticalComposition,
    requires
        VC::producers() == producers,
        VC::consumer() == consumer,
        // The consumer_id points to the consumer().controller.
        cluster.controller_models.contains_pair(consumer_id, consumer.controller),
        // A key exists in producer_ids iff it's within the range of producers,
        // which guarantees that producer_ids covers and only covers all the producers.
        forall |key| #[trigger] producer_ids.contains_key(key) <==> 0 <= key < producers.len(),
        // Each element in producer_ids points to each producer respectively.
        forall |key| producer_ids.contains_key(key)
            ==> cluster.controller_models.contains_pair(#[trigger] producer_ids[key], producers[key].controller),
        // The cluster starts with the initial state of the consumer().
        forall |s| #[trigger] cluster.init()(s)
            ==> (controller(VC::consumer().controller.reconcile_model, consumer_id).init)(s.controller_and_externals[consumer_id].controller),
        // The cluster starts with the initial state of the producer.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |s| #[trigger] cluster.init()(s)
                ==> (controller(VC::producers()[p_index].controller.reconcile_model, producer_ids[p_index]).init)(s.controller_and_externals[producer_ids[p_index]].controller),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The fairness condition for the consumer.
        spec.entails(tla_forall(|input| cluster.chosen_controller_next(consumer_id).weak_fairness(input))),
        // The fairness conditions for all the producers.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> spec.entails(tla_forall(|input| cluster.chosen_controller_next(producer_ids[p_index]).weak_fairness(input))),
        // No other controllers interfere with the consumer().
        forall |good_citizen_id| cluster.controller_models.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (consumer.not_interfered_by)(good_citizen_id)))),
        // Each producer is correct.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(producers[p_index].property),
    ensures
        // Consumer is correct.
        spec.entails(consumer.property),
{
    assert forall |good_citizen_id| cluster.controller_models.remove(consumer_id).contains_key(good_citizen_id)
    implies spec.entails(always(lift_state(#[trigger] (consumer.not_interfered_by)(good_citizen_id)))) by {
        if producer_ids.values().contains(good_citizen_id) {
            let j = choose |j| producer_ids.dom().contains(j) && #[trigger] producer_ids[j] == good_citizen_id;
            VC::producer_does_not_interfere_with_the_consumer(spec, cluster, good_citizen_id, j);
        } else {
            assert(spec.entails(always(lift_state((consumer.not_interfered_by)(good_citizen_id)))));
        }
    }
    VC::consumer_is_correct(spec, cluster, consumer_id);
}

pub proof fn compose<HC, VC>(spec: TempPred<ClusterState>, cluster: Cluster, consumer: ControllerPredGroup, producers: Seq<ControllerPredGroup>, consumer_id: int, producer_ids: Map<int, int>)
    where
        HC: HorizontalComposition,
        VC: VerticalComposition,
    requires
        HC::producers() == producers,
        VC::producers() == producers,
        VC::consumer() == consumer,
        // The consumer_id points to the consumer().controller.
        cluster.controller_models.contains_pair(consumer_id, consumer.controller),
        // A key exists in producer_ids iff it's within the range of producers,
        // which guarantees that producer_ids covers and only covers all the producers.
        forall |key| #[trigger] producer_ids.contains_key(key) <==> 0 <= key < producers.len(),
        // Each element in producer_ids points to each producer respectively.
        forall |key| producer_ids.contains_key(key)
            ==> cluster.controller_models.contains_pair(#[trigger] producer_ids[key], producers[key].controller),
        // The cluster starts with the initial state of the consumer().
        forall |s| #[trigger] cluster.init()(s)
            ==> (controller(VC::consumer().controller.reconcile_model, consumer_id).init)(s.controller_and_externals[consumer_id].controller),
        // The cluster starts with the initial state of the producer.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |s| #[trigger] cluster.init()(s)
                ==> (controller(VC::producers()[p_index].controller.reconcile_model, producer_ids[p_index]).init)(s.controller_and_externals[producer_ids[p_index]].controller),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The fairness condition for the consumer.
        spec.entails(tla_forall(|input| cluster.chosen_controller_next(consumer_id).weak_fairness(input))),
        // The fairness conditions for all the producers.
        forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> spec.entails(tla_forall(|input| cluster.chosen_controller_next(producer_ids[p_index]).weak_fairness(input))),
        // No other controllers interfere with the consumer().
        forall |good_citizen_id| cluster.controller_models.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (consumer.not_interfered_by)(good_citizen_id)))),
        // For each producer, no other controllers interfere with that producer.
        forall |p_index: int| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |good_citizen_id| cluster.controller_models.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))),
    ensures
        // Consumer is correct.
        spec.entails(consumer.property),
        // Each producer is correct.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(producers[p_index].property),
{
    assert forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
    implies (forall |good_citizen_id| cluster.controller_models.remove_keys(producer_ids.values()).contains_key(good_citizen_id)
        ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id| cluster.controller_models.remove_keys(producer_ids.values()).contains_key(good_citizen_id)
        implies spec.entails(always(lift_state(#[trigger] (producers[p_index].not_interfered_by)(good_citizen_id)))) by {
            if good_citizen_id == consumer_id {
                VC::consumer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, p_index);
            } else { }
        }
    }

    compose_horizontally::<HC>(spec, cluster, producers, producer_ids);
    compose_vertically::<VC>(spec, cluster, consumer, producers, consumer_id, producer_ids);
}


pub trait HorizontalComposition: Sized {

    spec fn producers() -> Seq<ControllerPredGroup>;

    // Proof obligation 2:
    // Producer is correct when running in any cluster where there is no interference.
    proof fn producer_is_correct(spec: TempPred<ClusterState>, cluster: Cluster, producer_id: int, p_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            // The cluster starts with the initial state of the producer.
            forall |s| #[trigger] cluster.init()(s)
                ==> (controller(Self::producers()[p_index].controller.reconcile_model, producer_id).init)(s.controller_and_externals[producer_id].controller),
            // The fairness condition is enough to say that the producer runs as part of the cluster's next transition.
            spec.entails(tla_forall(|input| cluster.chosen_controller_next(producer_id).weak_fairness(input))),
            // The next two preconditions say that no controller (except the producer itself) interferes with this producer.
            cluster.controller_models.contains_pair(producer_id, Self::producers()[p_index].controller),
            forall |good_citizen_id| cluster.controller_models.remove(producer_id).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (Self::producers()[p_index].not_interfered_by)(good_citizen_id)))),
        ensures
            spec.entails(Self::producers()[p_index].property),
        ;

    // Proof obligation 5:
    // Producer does not interfere with another producer in any cluster.
    proof fn producer_does_not_interfere_with_the_producer(spec: TempPred<ClusterState>, cluster: Cluster, good_citizen_id: int, p_index: int, q_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            0 <= q_index < Self::producers().len(),
            // We require the two producers to be different because there is no point to prove
            // a producer does not interfere with another instance of itself.
            p_index != q_index,
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            cluster.controller_models.contains_pair(good_citizen_id, Self::producers()[p_index].controller),
        ensures
            // The producer (p_index) never interferes with the other producer (q_index).
            spec.entails(always(lift_state((Self::producers()[q_index].not_interfered_by)(good_citizen_id)))),
        ;
}

pub trait VerticalComposition: Sized {

    spec fn consumer() -> ControllerPredGroup;

    spec fn producers() -> Seq<ControllerPredGroup>;

    // Proof obligation 1:
    // Consumer is correct when running in any cluster where each producer's spec is available and there is no interference.
    proof fn consumer_is_correct(spec: TempPred<ClusterState>, cluster: Cluster, consumer_id: int)
        requires
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            // The cluster starts with the initial state of the consumer().
            forall |s| #[trigger] cluster.init()(s)
                ==> (controller(Self::consumer().controller.reconcile_model, consumer_id).init)(s.controller_and_externals[consumer_id].controller),
            // The fairness condition is enough to say that the consumer runs as part of the cluster's next transition.
            spec.entails(tla_forall(|input| cluster.chosen_controller_next(consumer_id).weak_fairness(input))),
            // The next two preconditions say that no controller (except the consumer itself) interferes with this consumer().
            cluster.controller_models.contains_pair(consumer_id, Self::consumer().controller),
            forall |good_citizen_id| cluster.controller_models.remove(consumer_id).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (Self::consumer().not_interfered_by)(good_citizen_id)))),
            // We directly use the temporal property of the producers().
            forall |p_index: int| 0 <= p_index < Self::producers().len()
                ==> #[trigger] spec.entails(Self::producers()[p_index].property),
        ensures
            spec.entails(Self::consumer().property),
        ;

    // Proof obligation 2:
    // Consumer does not interfere with the producer in any cluster.
    proof fn consumer_does_not_interfere_with_the_producer(spec: TempPred<ClusterState>, cluster: Cluster, good_citizen_id: int, p_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            cluster.controller_models.contains_pair(good_citizen_id, Self::consumer().controller),
        ensures
            // The consumer never interferes with the producer.
            spec.entails(always(lift_state((Self::producers()[p_index].not_interfered_by)(good_citizen_id)))),
        ;

    // Proof obligation 3:
    // Producer does not interfere with the consumer in any cluster.
    proof fn producer_does_not_interfere_with_the_consumer(spec: TempPred<ClusterState>, cluster: Cluster, good_citizen_id: int, p_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            cluster.controller_models.contains_pair(good_citizen_id, Self::producers()[p_index].controller),
        ensures
            // The producer never interferes with the consumer().
            spec.entails(always(lift_state((Self::consumer().not_interfered_by)(good_citizen_id)))),
        ;
}


}
