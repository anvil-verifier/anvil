// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositionality::proof::*;
use crate::soundness::compositionality::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// Here are two examples on how to use BaseComposition and IncrementalComposition.

// Example 1: we use BaseComposition to prove that the waiter_controller (the consumer)
// and the cook_controllers (the producers) are correct when running together.

pub spec fn cook_controllers<S, I>() -> Seq<Controller<S, I>>;

pub spec fn waiter_controller<S, I>() -> Controller<S, I>;

pub open spec fn waiter_and_cooks<S, I>() -> Cluster<S, I> {
    Cluster {
        controllers: Map::new(|k| 0 <= k < cook_controllers::<S, I>().len(), |k| cook_controllers::<S, I>()[k])
            .insert(cook_controllers::<S, I>().len() as int, waiter_controller::<S, I>())
    }
}

pub open spec fn cooks<S, I>() -> Seq<ControllerPredGroup<S, I>> {
    cook_controllers().map(|i, v| ControllerPredGroup {
        controller: v,
        property: cook_property(i),
        not_interfered_by: cook_not_interfered_by(i),
    })
}

pub open spec fn waiter<S, I>() -> ControllerPredGroup<S, I> {
    ControllerPredGroup::<S, I> {
        controller: waiter_controller(),
        property: waiter_property(),
        not_interfered_by: waiter_not_interfered_by(),
    }
}

pub struct BaseCompositionProof<S, I> {
    dummy_s: std::marker::PhantomData<S>,
    dummy_i: std::marker::PhantomData<I>,
}

// Developers need to first prove the five lemmas (proof functions)
// required by the BaseComposition trait for waiter() and cooks().
impl<S, I> BaseComposition<S, I> for BaseCompositionProof<S, I> {
    open spec fn consumer() -> ControllerPredGroup<S, I> {
        waiter()
    }

    open spec fn producers() -> Seq<ControllerPredGroup<S, I>> {
        cooks()
    }

    #[verifier(external_body)]
    proof fn consumer_is_correct(spec: TempPred<S>, cluster: Cluster<S, I>, consumer_id: int) {}

    #[verifier(external_body)]
    proof fn producer_is_correct(spec: TempPred<S>, cluster: Cluster<S, I>, producer_id: int, p_index: int) {}

    #[verifier(external_body)]
    proof fn consumer_does_not_interfere_with_the_producer(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int) {}

    #[verifier(external_body)]
    proof fn producer_does_not_interfere_with_the_consumer(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int) {}

    #[verifier(external_body)]
    proof fn producer_does_not_interfere_with_the_producer(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int, q_index: int) {}
}

// This proof applies compose_producers_and_consumer to the cluster waiter_and_cooks
// and concludes that the waiter and cooks are all correct.
proof fn waiter_and_cooks_are_correct<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(waiter_and_cooks::<S, I>().init())),
        spec.entails(always(lift_action(waiter_and_cooks::<S, I>().next()))),
        spec.entails(controller_fairness::<S, I>(waiter().controller)),
        forall |p_index: int| 0 <= p_index < cooks::<S, I>().len()
            ==> #[trigger] spec.entails(controller_fairness::<S, I>(cooks()[p_index].controller)),
    ensures
        spec.entails(waiter::<S, I>().property),
        forall |p_index: int| 0 <= p_index < cooks::<S, I>().len()
            ==> #[trigger] spec.entails(cooks::<S, I>()[p_index].property),
{
    let cluster = waiter_and_cooks::<S, I>();

    let cook_ids = Map::new(|k: int| 0 <= k < cook_controllers::<S, I>().len(), |k: int| k);
    let waiter_id = cook_controllers::<S, I>().len() as int;

    assert forall |s| #[trigger] cluster.init()(s) implies waiter::<S, I>().controller.init()(s) by {
        assert forall |i| #[trigger] cluster.controllers.contains_key(i) implies cluster.controllers[i].init()(s) by {}
        assert(cluster.controllers.contains_key(waiter_id));
    }

    assert forall |p_index| #![trigger cooks::<S, I>()[p_index]] 0 <= p_index < cooks::<S, I>().len()
    implies forall |s| #[trigger] cluster.init()(s) ==> cooks::<S, I>()[p_index].controller.init()(s) by {
        assert forall |s| #[trigger] cluster.init()(s) implies cooks::<S, I>()[p_index].controller.init()(s) by {
            assert forall |i| #[trigger] cluster.controllers.contains_key(i) implies cluster.controllers[i].init()(s) by {}
            assert(cluster.controllers.contains_key(p_index));
        }
    }

    // Due to our cluster construct, you won't find a good_citizen_id that is neither the waiter nor any cook.
    // So we prove the following assertion by contradiction.
    assert forall |good_citizen_id: int|
        cluster.controllers.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id)
    implies
        #[trigger] spec.entails(always(lift_state((waiter::<S, I>().not_interfered_by)(good_citizen_id))))
    by {
        assert forall |controller_id| #[trigger] cluster.controllers.contains_key(controller_id)
        implies controller_id == waiter_id || cook_ids.values().contains(controller_id) by {
            if controller_id == cook_controllers::<S, I>().len() as int {
                assert(controller_id == waiter_id);
            } else {
                assert(cook_ids.dom().contains(controller_id) && cook_ids[controller_id] == controller_id);
            }
        }
        assert(!cluster.controllers.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id));
    }

    // Same as above.
    assert forall |p_index| #![trigger cooks::<S, I>()[p_index]] 0 <= p_index < cooks::<S, I>().len()
    implies
        (forall |good_citizen_id| cluster.controllers.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (cooks::<S, I>()[p_index].not_interfered_by)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id|
            cluster.controllers.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id)
        implies
            #[trigger] spec.entails(always(lift_state(#[trigger] (cooks::<S, I>()[p_index].not_interfered_by)(good_citizen_id))))
        by {
            assert forall |controller_id| #[trigger] cluster.controllers.contains_key(controller_id)
            implies controller_id == waiter_id || cook_ids.values().contains(controller_id) by {
                if controller_id == cook_controllers::<S, I>().len() as int {
                    assert(controller_id == waiter_id);
                } else {
                    assert(cook_ids.dom().contains(controller_id) && cook_ids[controller_id] == controller_id);
                }
            }
            assert(!cluster.controllers.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id));
        }
    }

    compose_producers_and_consumer::<S, I, BaseCompositionProof<S, I>>(spec, cluster, waiter::<S, I>(), cooks::<S, I>(), waiter_id, cook_ids);
}

// Example 2: we use IncrementalComposition to further prove that when the waiter_controller
// and cook_controllers run with a customer_controller, they are all correct. The key is to
// first use BaseComposition to prove the correctness of the waiter and cooks, and then use
// IncrementalComposition to prove the correctness of the customer.

pub spec fn customer_controller<S, I>() -> Controller<S, I>;

pub open spec fn customer_and_waiter_and_cooks<S, I>() -> Cluster<S, I> {
    Cluster {
        controllers: Map::new(|k| 0 <= k < cook_controllers::<S, I>().len(), |k| cook_controllers::<S, I>()[k])
            .insert(cook_controllers::<S, I>().len() as int, waiter_controller::<S, I>())
            .insert(cook_controllers::<S, I>().len() as int + 1, customer_controller::<S, I>())
    }
}

pub open spec fn customer<S, I>() -> ControllerPredGroup<S, I> {
    ControllerPredGroup::<S, I> {
        controller: customer_controller(),
        property: customer_property(),
        not_interfered_by: customer_not_interfered_by(),
    }
}

pub struct IncrementalCompositionProof<S, I> {
    dummy_s: std::marker::PhantomData<S>,
    dummy_i: std::marker::PhantomData<I>,
}

// IncrementalComposition poses only three lemmas for developers to prove
// and it assumes that producers are already proved correct.
// For the customer, the producers are the cooks and the waiter.

impl<S, I> IncrementalComposition<S, I> for IncrementalCompositionProof<S, I> {
    open spec fn consumer() -> ControllerPredGroup<S, I> {
        customer()
    }

    open spec fn producers() -> Seq<ControllerPredGroup<S, I>> {
        cooks().push(waiter())
    }

    #[verifier(external_body)]
    proof fn consumer_is_correct(spec: TempPred<S>, cluster: Cluster<S, I>, consumer_id: int) {}

    #[verifier(external_body)]
    proof fn consumer_does_not_interfere_with_the_producer(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int) {}

    #[verifier(external_body)]
    proof fn producer_does_not_interfere_with_the_consumer(spec: TempPred<S>, cluster: Cluster<S, I>, good_citizen_id: int, p_index: int) {}
}

proof fn customer_and_waiter_and_cooks_are_correct<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(customer_and_waiter_and_cooks::<S, I>().init())),
        spec.entails(always(lift_action(customer_and_waiter_and_cooks::<S, I>().next()))),
        spec.entails(controller_fairness::<S, I>(customer().controller)),
        spec.entails(controller_fairness::<S, I>(waiter().controller)),
        forall |p_index: int| 0 <= p_index < cooks::<S, I>().len()
            ==> #[trigger] spec.entails(controller_fairness::<S, I>(cooks()[p_index].controller)),
    ensures
        spec.entails(customer::<S, I>().property),
        spec.entails(waiter::<S, I>().property),
        forall |p_index: int| 0 <= p_index < cooks::<S, I>().len()
            ==> #[trigger] spec.entails(cooks::<S, I>()[p_index].property),
{
    let cluster = customer_and_waiter_and_cooks::<S, I>();

    let cook_ids = Map::new(|k: int| 0 <= k < cook_controllers::<S, I>().len(), |k: int| k);
    let waiter_id = cook_controllers::<S, I>().len() as int;
    let customer_id = cook_controllers::<S, I>().len() as int + 1;

    assert forall |s| #[trigger] cluster.init()(s) implies waiter::<S, I>().controller.init()(s) by {
        assert forall |i| #[trigger] cluster.controllers.contains_key(i) implies cluster.controllers[i].init()(s) by {}
        assert(cluster.controllers.contains_key(waiter_id));
    }

    assert forall |p_index| #![trigger cooks::<S, I>()[p_index]] 0 <= p_index < cooks::<S, I>().len()
    implies forall |s| #[trigger] cluster.init()(s) ==> cooks::<S, I>()[p_index].controller.init()(s) by {
        assert forall |s| #[trigger] cluster.init()(s) implies cooks::<S, I>()[p_index].controller.init()(s) by {
            assert forall |i| #[trigger] cluster.controllers.contains_key(i) implies cluster.controllers[i].init()(s) by {}
            assert(cluster.controllers.contains_key(p_index));
        }
    }

    assert forall |good_citizen_id: int|
        cluster.controllers.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id)
    implies
        #[trigger] spec.entails(always(lift_state((waiter::<S, I>().not_interfered_by)(good_citizen_id))))
    by {
        assert forall |good_citizen_id| #[trigger] cluster.controllers.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id)
        implies good_citizen_id == customer_id by {
            assert(0 <= good_citizen_id < cook_controllers::<S, I>().len() || waiter_id == good_citizen_id || customer_id == good_citizen_id);
            if 0 <= good_citizen_id < cook_controllers::<S, I>().len() {
                assert(cook_ids.dom().contains(good_citizen_id) && cook_ids[good_citizen_id] == good_citizen_id);
                assert(cook_ids.values().contains(good_citizen_id));
                assert(!cook_ids.values().contains(good_citizen_id));
            } else if waiter_id == good_citizen_id {
                assert(waiter_id != good_citizen_id);
            }
        }
        IncrementalCompositionProof::consumer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, cook_controllers::<S, I>().len() as int);
    }

    assert forall |p_index| #![trigger cooks::<S, I>()[p_index]] 0 <= p_index < cooks::<S, I>().len()
    implies
        (forall |good_citizen_id| cluster.controllers.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (cooks::<S, I>()[p_index].not_interfered_by)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id|
            cluster.controllers.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id)
        implies
            #[trigger] spec.entails(always(lift_state(#[trigger] (cooks::<S, I>()[p_index].not_interfered_by)(good_citizen_id))))
        by {
            assert forall |good_citizen_id| #[trigger] cluster.controllers.remove(waiter_id).remove_keys(cook_ids.values()).contains_key(good_citizen_id)
            implies good_citizen_id == customer_id by {
                assert(0 <= good_citizen_id < cook_controllers::<S, I>().len() || waiter_id == good_citizen_id || customer_id == good_citizen_id);
                if 0 <= good_citizen_id < cook_controllers::<S, I>().len() {
                    assert(cook_ids.dom().contains(good_citizen_id) && cook_ids[good_citizen_id] == good_citizen_id);
                    assert(cook_ids.values().contains(good_citizen_id));
                    assert(!cook_ids.values().contains(good_citizen_id));
                } else if waiter_id == good_citizen_id {
                    assert(waiter_id != good_citizen_id);
                }
            }
            IncrementalCompositionProof::consumer_does_not_interfere_with_the_producer(spec, cluster, good_citizen_id, p_index);
        }
    }

    compose_producers_and_consumer::<S, I, BaseCompositionProof<S, I>>(spec, cluster, waiter::<S, I>(), cooks::<S, I>(), waiter_id, cook_ids);

    let cooks_and_waiter = cooks().push(waiter());
    let cooks_and_waiter_ids = Map::new(|k: int| 0 <= k < cook_controllers::<S, I>().len() + 1, |k: int| k);

    assert forall |s| #[trigger] cluster.init()(s) implies customer::<S, I>().controller.init()(s) by {
        assert forall |i| #[trigger] cluster.controllers.contains_key(i) implies cluster.controllers[i].init()(s) by {}
        assert(cluster.controllers.contains_key(customer_id));
    }

    assert forall |good_citizen_id: int|
        cluster.controllers.remove(customer_id).remove_keys(cooks_and_waiter_ids.values()).contains_key(good_citizen_id)
    implies
        #[trigger] spec.entails(always(lift_state((customer::<S, I>().not_interfered_by)(good_citizen_id))))
    by {
        assert forall |controller_id| #[trigger] cluster.controllers.contains_key(controller_id)
        implies controller_id == customer_id || cooks_and_waiter_ids.values().contains(controller_id) by {
            if controller_id == cook_controllers::<S, I>().len() as int + 1 {
                assert(controller_id == customer_id);
            } else {
                assert(cooks_and_waiter_ids.dom().contains(controller_id) && cooks_and_waiter_ids[controller_id] == controller_id);
            }
        }
        assert(!cluster.controllers.remove(customer_id).remove_keys(cooks_and_waiter_ids.values()).contains_key(good_citizen_id));
    }

    assert forall |p_index| #![trigger cooks_and_waiter[p_index]] 0 <= p_index < cooks_and_waiter.len()
    implies
        (forall |good_citizen_id| cluster.controllers.remove(customer_id).remove_keys(cooks_and_waiter_ids.values()).contains_key(good_citizen_id)
            ==> spec.entails(always(lift_state(#[trigger] (cooks_and_waiter[p_index].not_interfered_by)(good_citizen_id)))))
    by {
        assert forall |good_citizen_id|
            cluster.controllers.remove(customer_id).remove_keys(cooks_and_waiter_ids.values()).contains_key(good_citizen_id)
        implies
            #[trigger] spec.entails(always(lift_state(#[trigger] (cooks_and_waiter[p_index].not_interfered_by)(good_citizen_id))))
        by {
            assert forall |controller_id| #[trigger] cluster.controllers.contains_key(controller_id)
            implies controller_id == customer_id || cooks_and_waiter_ids.values().contains(controller_id) by {
                if controller_id == cook_controllers::<S, I>().len() as int + 1 {
                    assert(controller_id == customer_id);
                } else {
                    assert(cooks_and_waiter_ids.dom().contains(controller_id) && cooks_and_waiter_ids[controller_id] == controller_id);
                }
            }
            assert(!cluster.controllers.remove(customer_id).remove_keys(cooks_and_waiter_ids.values()).contains_key(good_citizen_id));
        }
    }

    compose_consumer_incrementally::<S, I, IncrementalCompositionProof<S, I>>(spec, cluster, customer::<S, I>(), cooks_and_waiter, customer_id, cooks_and_waiter_ids);
}

pub spec fn cook_property<S>(i: int) -> TempPred<S>;
pub spec fn waiter_property<S>() -> TempPred<S>;
pub spec fn customer_property<S>() -> TempPred<S>;

pub spec fn cook_not_interfered_by<S>(i: int) -> spec_fn(good_citizen_id: int) -> StatePred<S>;
pub spec fn waiter_not_interfered_by<S>() -> spec_fn(good_citizen_id: int) -> StatePred<S>;
pub spec fn customer_not_interfered_by<S>() -> spec_fn(good_citizen_id: int) -> StatePred<S>;

}
