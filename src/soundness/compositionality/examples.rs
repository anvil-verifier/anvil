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
// only a waiter and a sequence of cooks.
pub spec fn cooks<S, I>() -> Seq<Controller<S, I>>;

pub spec fn waiter<S, I>() -> Controller<S, I>;

pub open spec fn cook_spec_groups<S, I>() -> Seq<ControllerSpecGroup<S, I>> {
    cooks().map(|i, v| ControllerSpecGroup {
        controller: v,
        key: i,
        property: arbitrary(),
        not_interfered_by: arbitrary(),
    })
}

pub open spec fn waiter_spec_group<S, I>() -> ControllerSpecGroup<S, I> {
    ControllerSpecGroup::<S, I> {
        controller: waiter(),
        key: cook_spec_groups::<S, I>().len() as int,
        property: arbitrary(),
        not_interfered_by: arbitrary(),
    }
}

pub struct WaiterAndCooks<S, I> {
    dummy_s: std::marker::PhantomData<S>,
    dummy_i: std::marker::PhantomData<I>,
}

impl<S, I> Compositional<S, I> for WaiterAndCooks<S, I> {
    open spec fn consumer() -> ControllerSpecGroup<S, I> {
        waiter_spec_group()
    }

    open spec fn producers() -> Seq<ControllerSpecGroup<S, I>> {
        cook_spec_groups()
    }

    #[verifier(external_body)]
    proof fn producer_is_correct(spec: TempPred<S>, cluster: Cluster<S, I>, p_index: int) {}

    #[verifier(external_body)]
    proof fn consumer_is_correct(spec: TempPred<S>, cluster: Cluster<S, I>) {}

    #[verifier(external_body)]
    proof fn consumer_does_not_interfere_with_the_producer(spec: TempPred<S>, cluster: Cluster<S, I>, p_index: int) {}

    #[verifier(external_body)]
    proof fn producer_does_not_interfere_with_the_producer(spec: TempPred<S>, cluster: Cluster<S, I>, p_index: int, q_index: int) {}

    #[verifier(external_body)]
    proof fn producer_does_not_interfere_with_the_consumer(spec: TempPred<S>, cluster: Cluster<S, I>, p_index: int) {}
}

// A concrete cluster with only cooks and waiter_spec_group
pub open spec fn waiter_and_cooks<S, I>() -> Cluster<S, I> {
    Cluster {
        controllers: Map::new(|k| 0 <= k < cooks::<S, I>().len(), |k| cooks::<S, I>()[k])
            .insert(cooks::<S, I>().len() as int, waiter::<S, I>())
    }
}

proof fn waiter_and_cooks_are_correct<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(waiter_and_cooks::<S, I>().init())),
        spec.entails(always(lift_action(waiter_and_cooks::<S, I>().next()))),
        forall |p_index: int| 0 <= p_index < cook_spec_groups::<S, I>().len()
            ==> #[trigger] spec.entails(controller_fairness::<S, I>(cook_spec_groups()[p_index].controller)),
        spec.entails(controller_fairness::<S, I>(waiter_spec_group().controller)),
    ensures
        forall |p_index: int| 0 <= p_index < cook_spec_groups::<S, I>().len()
            ==> #[trigger] spec.entails(cook_spec_groups::<S, I>()[p_index].property),
        spec.entails(waiter_spec_group::<S, I>().property),
{
    let cluster = waiter_and_cooks::<S, I>();

    assert forall |s| #[trigger] cluster.init()(s) implies waiter_spec_group::<S, I>().controller.init()(s) by {
        assert forall |i| #[trigger] cluster.controllers.contains_key(i) implies cluster.controllers[i].init()(s) by {}
        assert(cluster.controllers.contains_key(waiter_spec_group::<S, I>().key));
    }

    assert forall |p_index| #![trigger cook_spec_groups::<S, I>()[p_index]] 0 <= p_index < cook_spec_groups::<S, I>().len()
    implies forall |s| #[trigger] cluster.init()(s) ==> cook_spec_groups::<S, I>()[p_index].controller.init()(s) by {
        assert forall |s| #[trigger] cluster.init()(s) implies cook_spec_groups::<S, I>()[p_index].controller.init()(s) by {
            assert forall |i| #[trigger] cluster.controllers.contains_key(i) implies cluster.controllers[i].init()(s) by {}
            assert(cluster.controllers.contains_key(p_index));
        }
    }

    let cook_keys = cook_spec_groups().map_values(|p: ControllerSpecGroup<S, I>| p.key);
    let cook_key_set = cook_keys.to_set();

    // Due to our cluster construct, you won't find a good_citizen_id that is neither the waiter_spec_group nor any cook.
    // So we prove the following assertion by contradiction.
    assert forall |good_citizen_id: int|
        cluster.controllers.remove(waiter_spec_group::<S, I>().key).remove_keys(cook_key_set).contains_key(good_citizen_id)
    implies
        #[trigger] spec.entails(always(lift_state((waiter_spec_group::<S, I>().not_interfered_by)(good_citizen_id))))
    by {
        assert forall |controller_id| #[trigger] cluster.controllers.contains_key(controller_id)
        implies controller_id == waiter_spec_group::<S, I>().key || cook_key_set.contains(controller_id) by {
            if controller_id == cook_spec_groups::<S, I>().len() as int {
                assert(controller_id == waiter_spec_group::<S, I>().key);
            } else {
                assert(0 <= controller_id < cook_keys.len() && cook_keys[controller_id] == controller_id);
            }
        }
        assert(!cluster.controllers.remove(waiter_spec_group::<S, I>().key).remove_keys(cook_key_set).contains_key(good_citizen_id));
    }

    assert forall |p_index| #![trigger cook_spec_groups::<S, I>()[p_index]] 0 <= p_index < cook_spec_groups::<S, I>().len()
    implies
        (forall |good_citizen_id| cluster.controllers.remove(waiter_spec_group::<S, I>().key).remove_keys(cook_key_set).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (cook_spec_groups::<S, I>()[p_index].not_interfered_by)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id|
            cluster.controllers.remove(waiter_spec_group::<S, I>().key).remove_keys(cook_key_set).contains_key(good_citizen_id)
        implies
            #[trigger] spec.entails(always(lift_state(#[trigger] (cook_spec_groups::<S, I>()[p_index].not_interfered_by)(good_citizen_id))))
        by {
            assert forall |controller_id| #[trigger] cluster.controllers.contains_key(controller_id)
            implies controller_id == waiter_spec_group::<S, I>().key || cook_key_set.contains(controller_id) by {
                if controller_id == cook_spec_groups::<S, I>().len() as int {
                    assert(controller_id == waiter_spec_group::<S, I>().key);
                } else {
                    assert(0 <= controller_id < cook_keys.len() && cook_keys[controller_id] == controller_id);
                }
            }
            assert(!cluster.controllers.remove(waiter_spec_group::<S, I>().key).remove_keys(cook_key_set).contains_key(good_citizen_id));
        }
    }

    WaiterAndCooks::consumer_and_producers_are_correct(spec, cluster);
}

}
