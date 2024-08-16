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
