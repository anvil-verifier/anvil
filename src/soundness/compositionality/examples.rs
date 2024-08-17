// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositionality::proof::*;
use crate::soundness::compositionality::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// This is a use case of consumer_and_producers_are_correct:
// We can apply consumer_and_producers_are_correct to a concrete cluster that includes
// only a consumer and a sequence of producers.
pub spec fn producer_controllers<S, I>() -> Seq<Controller<S, I>>;

pub spec fn consumer_controller<S, I>() -> Controller<S, I>;

pub open spec fn producers<S, I>() -> Seq<ControllerSpecs<S, I>> {
    producer_controllers().map(|i, v| ControllerSpecs {
        controller: v,
        key: i,
        property: arbitrary(),
        non_interference: arbitrary(),
    })
}

pub open spec fn consumer<S, I>() -> ControllerSpecs<S, I> {
    ControllerSpecs::<S, I> {
        controller: consumer_controller(),
        key: producers::<S, I>().len() as int,
        property: arbitrary(),
        non_interference: arbitrary(),
    }
}

// A concrete cluster with only producers and consumer
pub open spec fn consumer_and_producers<S, I>() -> Cluster<S, I> {
    Cluster {
        controllers: Map::new(|k| 0 <= k < producer_controllers::<S, I>().len(), |k| producer_controllers::<S, I>()[k])
            .insert(producer_controllers::<S, I>().len() as int, consumer_controller::<S, I>())
    }
}

proof fn consumer_and_producers_are_correct_in_a_concrete_cluster<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(consumer_and_producers::<S, I>().init())),
        spec.entails(always(lift_action(consumer_and_producers::<S, I>().next()))),
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(controller_fairness::<S, I>(producers()[p_index].controller)),
        spec.entails(controller_fairness::<S, I>(consumer().controller)),
    ensures
        forall |p_index: int| 0 <= p_index < producers::<S, I>().len()
            ==> #[trigger] spec.entails(producers::<S, I>()[p_index].property),
        spec.entails(consumer::<S, I>().property),
{
    let cluster = consumer_and_producers::<S, I>();

    assert forall |s| #[trigger] cluster.init()(s) implies consumer::<S, I>().controller.init()(s) by {
        assert forall |i| #[trigger] cluster.controllers.contains_key(i) implies cluster.controllers[i].init()(s) by {}
        assert(cluster.controllers.contains_key(consumer::<S, I>().key));
    }

    assert forall |p_index| #![trigger producers::<S, I>()[p_index]] 0 <= p_index < producers::<S, I>().len()
    implies forall |s| #[trigger] cluster.init()(s) ==> producers::<S, I>()[p_index].controller.init()(s) by {
        assert forall |s| #[trigger] cluster.init()(s) implies producers::<S, I>()[p_index].controller.init()(s) by {
            assert forall |i| #[trigger] cluster.controllers.contains_key(i) implies cluster.controllers[i].init()(s) by {}
            assert(cluster.controllers.contains_key(p_index));
        }
    }

    let producer_keys = producers().map_values(|p: ControllerSpecs<S, I>| p.key);
    let producer_key_set = producer_keys.to_set();

    // Due to our cluster construct, you won't find a good_citizen_id that is neither the consumer nor any producer.
    // So we prove the following assertion by contradiction.
    assert forall |good_citizen_id: int|
        cluster.controllers.remove(consumer::<S, I>().key).remove_keys(producer_key_set).contains_key(good_citizen_id)
    implies
        #[trigger] spec.entails(always(lift_state((consumer::<S, I>().non_interference)(good_citizen_id))))
    by {
        assert forall |controller_id| #[trigger] cluster.controllers.contains_key(controller_id)
        implies controller_id == consumer::<S, I>().key || producer_key_set.contains(controller_id) by {
            if controller_id == producers::<S, I>().len() as int {
                assert(controller_id == consumer::<S, I>().key);
            } else {
                assert(0 <= controller_id < producer_keys.len() && producer_keys[controller_id] == controller_id);
            }
        }
        assert(!cluster.controllers.remove(consumer::<S, I>().key).remove_keys(producer_key_set).contains_key(good_citizen_id));
    }

    assert forall |p_index| #![trigger producers::<S, I>()[p_index]] 0 <= p_index < producers::<S, I>().len()
    implies
        (forall |good_citizen_id| cluster.controllers.remove(consumer::<S, I>().key).remove_keys(producer_key_set).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (producers::<S, I>()[p_index].non_interference)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id|
            cluster.controllers.remove(consumer::<S, I>().key).remove_keys(producer_key_set).contains_key(good_citizen_id)
        implies
            #[trigger] spec.entails(always(lift_state(#[trigger] (producers::<S, I>()[p_index].non_interference)(good_citizen_id))))
        by {
            assert forall |controller_id| #[trigger] cluster.controllers.contains_key(controller_id)
            implies controller_id == consumer::<S, I>().key || producer_key_set.contains(controller_id) by {
                if controller_id == producers::<S, I>().len() as int {
                    assert(controller_id == consumer::<S, I>().key);
                } else {
                    assert(0 <= controller_id < producer_keys.len() && producer_keys[controller_id] == controller_id);
                }
            }
            assert(!cluster.controllers.remove(consumer::<S, I>().key).remove_keys(producer_key_set).contains_key(good_citizen_id));
        }
    }

    consumer_and_producers_are_correct(spec, cluster, consumer(), producers());
}

}
