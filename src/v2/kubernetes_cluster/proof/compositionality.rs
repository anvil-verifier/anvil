use crate::kubernetes_cluster::spec::cluster::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub struct ControllerPredGroup {
    pub controller: ControllerModel,
    // The top level property of the input controller (e.g., ESR)
    pub property: TempPred<ClusterState>,
    // The condition on the cluster, e.g., the custom resource type is installed in the cluster
    pub cluster_condition: spec_fn(Cluster) -> bool,
    // The fairness condition, e.g., the controller runs weakly fair.
    pub fairness_condition: TempPred<ClusterState>,
    // The inv asserts that the controller indexed by good_citizen_id does not interfere with the input controller's reconcile.
    //
    // Note that the invariant likely does not hold when good_citizen_id points to the input controller itself, that is,
    // if there are two instances of the same controller, they will interfere with each other.
    // This is not a problem because there is no reason to run two such instances at the same time.
    pub non_interference_condition: spec_fn(good_citizen_id: int) -> StatePred<ClusterState>,
}

proof fn compose_horizontally<HC>(spec: TempPred<ClusterState>, cluster: Cluster, producers: Seq<ControllerPredGroup>, producer_ids: Map<int, int>)
    where
        HC: HorizontalComposition,
    requires
        HC::producers() == producers,
        // Cluster condition for each producer is satisfied.
        forall |p_index| 0 <= p_index < producers.len() ==> #[trigger] (producers[p_index].cluster_condition)(cluster),
        // Each producer runs in the cluster, pointed by producer_ids[p_index].
        forall |key| #[trigger] producer_ids.contains_key(key) <==> 0 <= key < producers.len(),
        forall |key| producer_ids.contains_key(key)
            ==> cluster.controller_models.contains_pair(#[trigger] producer_ids[key], producers[key].controller),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The fairness conditions for all the producers.
        forall |p_index| 0 <= p_index < producers.len() ==> spec.entails(#[trigger] producers[p_index].fairness_condition),
        // For each producer, no other controllers interfere with that producer.
        forall |p_index: int| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |good_citizen_id| cluster.controller_models.remove_keys(producer_ids.values()).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].non_interference_condition)(good_citizen_id)))),
    ensures
        // Each producer is correct.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(producers[p_index].property),
{
    assert forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
    implies (forall |good_citizen_id| #[trigger] cluster.controller_models.remove(producer_ids[p_index]).contains_key(good_citizen_id)
        ==> spec.entails(always(lift_state((producers[p_index].non_interference_condition)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id| cluster.controller_models.remove(producer_ids[p_index]).contains_key(good_citizen_id)
        implies spec.entails(always(lift_state(#[trigger] (producers[p_index].non_interference_condition)(good_citizen_id)))) by {
            if producer_ids.values().contains(good_citizen_id) {
                let j = choose |j| producer_ids.dom().contains(j) && #[trigger] producer_ids[j] == good_citizen_id;
                HC::producer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, j, p_index);
            } else {
                assert(spec.entails(always(lift_state((producers[p_index].non_interference_condition)(good_citizen_id)))));
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
        // Cluster condition for the consumer is satisfied.
        (consumer.cluster_condition)(cluster),
        // Cluster condition for each producer is satisfied.
        forall |p_index| 0 <= p_index < producers.len() ==> #[trigger] (producers[p_index].cluster_condition)(cluster),
        // The consumer runs in the cluster, pointed to by consumer_id.
        cluster.controller_models.contains_pair(consumer_id, consumer.controller),
        // Each producer runs in the cluster, pointed by producer_ids[p_index].
        forall |key| #[trigger] producer_ids.contains_key(key) <==> 0 <= key < producers.len(),
        forall |key| producer_ids.contains_key(key)
            ==> cluster.controller_models.contains_pair(#[trigger] producer_ids[key], producers[key].controller),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The fairness condition for the consumer.
        spec.entails(consumer.fairness_condition),
        // The fairness conditions for all the producers.
        forall |p_index| 0 <= p_index < producers.len() ==> spec.entails(#[trigger] producers[p_index].fairness_condition),
        // No other controllers interfere with the consumer().
        forall |good_citizen_id| cluster.controller_models.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (consumer.non_interference_condition)(good_citizen_id)))),
        // Each producer is correct.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(producers[p_index].property),
    ensures
        // Consumer is correct.
        spec.entails(consumer.property),
{
    assert forall |good_citizen_id| cluster.controller_models.remove(consumer_id).contains_key(good_citizen_id)
    implies spec.entails(always(lift_state(#[trigger] (consumer.non_interference_condition)(good_citizen_id)))) by {
        if producer_ids.values().contains(good_citizen_id) {
            let j = choose |j| producer_ids.dom().contains(j) && #[trigger] producer_ids[j] == good_citizen_id;
            VC::producer_does_not_interfere_with_the_consumer(spec, cluster, good_citizen_id, j);
        } else {
            assert(spec.entails(always(lift_state((consumer.non_interference_condition)(good_citizen_id)))));
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
        // Cluster condition for the consumer is satisfied.
        (consumer.cluster_condition)(cluster),
        // Cluster condition for each producer is satisfied.
        forall |p_index| 0 <= p_index < producers.len() ==> #[trigger] (producers[p_index].cluster_condition)(cluster),
        // The consumer runs in the cluster, pointed to by consumer_id.
        cluster.controller_models.contains_pair(consumer_id, consumer.controller),
        // Each producer runs in the cluster, pointed by producer_ids[p_index].
        forall |key| #[trigger] producer_ids.contains_key(key) <==> 0 <= key < producers.len(),
        forall |key| producer_ids.contains_key(key)
            ==> cluster.controller_models.contains_pair(#[trigger] producer_ids[key], producers[key].controller),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        // The fairness condition for the consumer.
        spec.entails(consumer.fairness_condition),
        // The fairness conditions for all the producers.
        forall |p_index| 0 <= p_index < producers.len() ==> spec.entails(#[trigger] producers[p_index].fairness_condition),
        // No other controllers interfere with the consumer.
        forall |good_citizen_id| cluster.controller_models.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (consumer.non_interference_condition)(good_citizen_id)))),
        // For each producer, no other controllers interfere with that producer.
        forall |p_index: int| #![trigger producers[p_index]] 0 <= p_index < producers.len()
            ==> forall |good_citizen_id| cluster.controller_models.remove(consumer_id).remove_keys(producer_ids.values()).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].non_interference_condition)(good_citizen_id)))),
    ensures
        // Consumer is correct.
        spec.entails(consumer.property),
        // Each producer is correct.
        forall |p_index| 0 <= p_index < producers.len()
            ==> #[trigger] spec.entails(producers[p_index].property),
{
    assert forall |p_index| #![trigger producers[p_index]] 0 <= p_index < producers.len()
    implies (forall |good_citizen_id| cluster.controller_models.remove_keys(producer_ids.values()).contains_key(good_citizen_id)
        ==> spec.entails(always(lift_state(#[trigger] (producers[p_index].non_interference_condition)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id| cluster.controller_models.remove_keys(producer_ids.values()).contains_key(good_citizen_id)
        implies spec.entails(always(lift_state(#[trigger] (producers[p_index].non_interference_condition)(good_citizen_id)))) by {
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

    // Proof obligation 1:
    // Producer is correct when running in any cluster where there is no interference.
    proof fn producer_is_correct(spec: TempPred<ClusterState>, cluster: Cluster, producer_id: int, p_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            (Self::producers()[p_index].cluster_condition)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            // The producer runs in the cluster.
            cluster.controller_models.contains_pair(producer_id, Self::producers()[p_index].controller),
            // The fairness condition of the producer.
            spec.entails(Self::producers()[p_index].fairness_condition),
            // No other controllers interfere with this producer.
            forall |good_citizen_id| cluster.controller_models.remove(producer_id).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (Self::producers()[p_index].non_interference_condition)(good_citizen_id)))),
        ensures
            spec.entails(Self::producers()[p_index].property),
        ;

    // Proof obligation 2:
    // Producer does not interfere with another producer in any cluster.
    proof fn producer_does_not_interfere_with_the_producer(spec: TempPred<ClusterState>, cluster: Cluster, good_citizen_id: int, p_index: int, q_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            0 <= q_index < Self::producers().len(),
            // We require the two producers to be different because there is no point to prove
            // a producer does not interfere with another instance of itself.
            p_index != q_index,
            (Self::producers()[p_index].cluster_condition)(cluster),
            (Self::producers()[q_index].cluster_condition)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            cluster.controller_models.contains_pair(good_citizen_id, Self::producers()[p_index].controller),
        ensures
            // The producer (p_index) never interferes with the other producer (q_index).
            spec.entails(always(lift_state((Self::producers()[q_index].non_interference_condition)(good_citizen_id)))),
        ;
}

pub trait VerticalComposition: Sized {

    spec fn consumer() -> ControllerPredGroup;

    spec fn producers() -> Seq<ControllerPredGroup>;

    // Proof obligation 1:
    // Consumer is correct when running in any cluster where each producer is correct and there is no interference.
    proof fn consumer_is_correct(spec: TempPred<ClusterState>, cluster: Cluster, consumer_id: int)
        requires
            (Self::consumer().cluster_condition)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            // The consumer runs in the cluster.
            cluster.controller_models.contains_pair(consumer_id, Self::consumer().controller),
            // The fairness condition of the consumer.
            spec.entails(Self::consumer().fairness_condition),
            // No other controllers interfere with the consumer.
            forall |good_citizen_id| cluster.controller_models.remove(consumer_id).contains_key(good_citizen_id)
                ==> spec.entails(always(lift_state(#[trigger] (Self::consumer().non_interference_condition)(good_citizen_id)))),
            // Producers are correct.
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
            (Self::consumer().cluster_condition)(cluster),
            (Self::producers()[p_index].cluster_condition)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            cluster.controller_models.contains_pair(good_citizen_id, Self::consumer().controller),
        ensures
            spec.entails(always(lift_state((Self::producers()[p_index].non_interference_condition)(good_citizen_id)))),
        ;

    // Proof obligation 3:
    // Producer does not interfere with the consumer in any cluster.
    proof fn producer_does_not_interfere_with_the_consumer(spec: TempPred<ClusterState>, cluster: Cluster, good_citizen_id: int, p_index: int)
        requires
            0 <= p_index < Self::producers().len(),
            (Self::consumer().cluster_condition)(cluster),
            (Self::producers()[p_index].cluster_condition)(cluster),
            spec.entails(lift_state(cluster.init())),
            spec.entails(always(lift_action(cluster.next()))),
            cluster.controller_models.contains_pair(good_citizen_id, Self::producers()[p_index].controller),
        ensures
            spec.entails(always(lift_state((Self::consumer().non_interference_condition)(good_citizen_id)))),
        ;
}

mod example {

use crate::kubernetes_cluster::spec::{api_server::types::InstalledTypes, cluster::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use super::*;

// Here is an example on how to use HorizontalComposition and VerticalComposition to compose controllers.

pub spec fn cook_controllers() -> Seq<ControllerModel>;
pub spec fn cook_property(i: int) -> TempPred<ClusterState>;
pub spec fn cook_cluster_condition(i: int) -> spec_fn(Cluster) -> bool;
pub spec fn cook_fairness_condition(i: int) -> TempPred<ClusterState>;
pub spec fn cook_non_interference_condition(i: int) -> spec_fn(good_citizen_id: int) -> StatePred<ClusterState>;

pub spec fn waiter_controller() -> ControllerModel;
pub spec fn waiter_cluster_condition() -> spec_fn(Cluster) -> bool;
pub spec fn waiter_fairness_condition() -> TempPred<ClusterState>;
pub spec fn waiter_property() -> TempPred<ClusterState>;
pub spec fn waiter_non_interference_condition() -> spec_fn(good_citizen_id: int) -> StatePred<ClusterState>;

pub spec fn waiter_and_cooks_installed_types() -> InstalledTypes;

pub open spec fn waiter_and_cooks() -> Cluster {
    Cluster {
        controller_models: Map::new(|k| 0 <= k < cook_controllers().len(), |k| cook_controllers()[k])
            .insert(cook_controllers().len() as int, waiter_controller()),
        installed_types: waiter_and_cooks_installed_types(),
    }
}

pub open spec fn cooks() -> Seq<ControllerPredGroup> {
    cook_controllers().map(|i, v| ControllerPredGroup {
        controller: v,
        property: cook_property(i),
        cluster_condition: cook_cluster_condition(i),
        fairness_condition: cook_fairness_condition(i),
        non_interference_condition: cook_non_interference_condition(i),
    })
}

pub open spec fn waiter() -> ControllerPredGroup {
    ControllerPredGroup {
        controller: waiter_controller(),
        property: waiter_property(),
        cluster_condition: waiter_cluster_condition(),
        fairness_condition: waiter_fairness_condition(),
        non_interference_condition: waiter_non_interference_condition(),
    }
}

pub struct CooksComposition {}

pub struct WaiterCooksComposition {}

impl HorizontalComposition for CooksComposition {
    open spec fn producers() -> Seq<ControllerPredGroup> { cooks() }

    #[verifier(external_body)]
    proof fn producer_is_correct(spec: TempPred<ClusterState>, cluster: Cluster, producer_id: int, p_index: int) {}

    #[verifier(external_body)]
    proof fn producer_does_not_interfere_with_the_producer(spec: TempPred<ClusterState>, cluster: Cluster, good_citizen_id: int, p_index: int, q_index: int) {}
}

impl VerticalComposition for WaiterCooksComposition {
    open spec fn consumer() -> ControllerPredGroup { waiter() }

    open spec fn producers() -> Seq<ControllerPredGroup> { cooks() }

    #[verifier(external_body)]
    proof fn consumer_is_correct(spec: TempPred<ClusterState>, cluster: Cluster, consumer_id: int) {}

    #[verifier(external_body)]
    proof fn consumer_does_not_interfere_with_the_producer(spec: TempPred<ClusterState>, cluster: Cluster, good_citizen_id: int, p_index: int) {}

    #[verifier(external_body)]
    proof fn producer_does_not_interfere_with_the_consumer(spec: TempPred<ClusterState>, cluster: Cluster, good_citizen_id: int, p_index: int) {}
}

proof fn waiter_and_cooks_are_correct(spec: TempPred<ClusterState>)
    requires
        (waiter().cluster_condition)(waiter_and_cooks()),
        forall |p_index| 0 <= p_index < cooks().len() ==> #[trigger] (cooks()[p_index].cluster_condition)(waiter_and_cooks()),
        spec.entails(lift_state(waiter_and_cooks().init())),
        spec.entails(always(lift_action(waiter_and_cooks().next()))),
        spec.entails(waiter().fairness_condition),
        forall |p_index: int| 0 <= p_index < cooks().len() ==> #[trigger] spec.entails(cooks()[p_index].fairness_condition),
    ensures
        spec.entails(waiter().property),
        forall |p_index: int| 0 <= p_index < cooks().len() ==> #[trigger] spec.entails(cooks()[p_index].property),
{
    let cluster = waiter_and_cooks();

    let cook_ids = Map::new(|k: int| 0 <= k < cook_controllers().len(), |k: int| k);
    let waiter_id = cook_controllers().len() as int;

    // The good_citizen_id must point to the waiter.
    assert forall |p_index| #![trigger cooks()[p_index]] 0 <= p_index < cooks().len()
    implies
        (forall |good_citizen_id| cluster.controller_models.remove_keys(cook_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (cooks()[p_index].non_interference_condition)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id| cluster.controller_models.remove_keys(cook_ids.values()).contains_key(good_citizen_id)
        implies spec.entails(always(lift_state(#[trigger] (cooks()[p_index].non_interference_condition)(good_citizen_id))))
        by {
            assert forall |controller_id| #[trigger] cluster.controller_models.contains_key(controller_id)
            implies controller_id == waiter_id || cook_ids.values().contains(controller_id) by {
                if controller_id == cook_controllers().len() as int {
                    assert(controller_id == waiter_id);
                } else {
                    assert(cook_ids.dom().contains(controller_id) && cook_ids[controller_id] == controller_id);
                }
            }
            assert(good_citizen_id == waiter_id);
            WaiterCooksComposition::consumer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, p_index);
        }
    }
    // Compose cooks horizontally.
    compose_horizontally::<CooksComposition>(spec, cluster, cooks(), cook_ids);

    // There is no good_citizen_id that is neither the waiter nor any cook.
    // So we prove the following assertion by contradiction.
    assert forall |good_citizen_id: int| cluster.controller_models.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id)
    implies #[trigger] spec.entails(always(lift_state((waiter().non_interference_condition)(good_citizen_id))))
    by {
        assert forall |controller_id| #[trigger] cluster.controller_models.contains_key(controller_id)
        implies controller_id == waiter_id || cook_ids.values().contains(controller_id) by {
            if controller_id == cook_controllers().len() as int {
                assert(controller_id == waiter_id);
            } else {
                assert(cook_ids.dom().contains(controller_id) && cook_ids[controller_id] == controller_id);
            }
        }
        assert(!cluster.controller_models.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id));
    }
    // Compose the waiter and cooks vertically.
    compose_vertically::<WaiterCooksComposition>(spec, cluster, waiter(), cooks(), waiter_id, cook_ids);
}


}

}
