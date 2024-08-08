// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// Problem: how to do proof in a compositional way when one controller depends on
// other controllers to be correct?
//
// This abstract state machine example is used to illustrate how to do compositional
// liveness proof for controllers. There are two controllers: producer and consumer.
// To make the proof conclusion general, the producer and consumer remain abstract
// in this example (spec functions without body).
//
// The producer realizes its desired state without relying on any other controller.
// The consumer relies on the producer to realize its desired state. For example,
// during the consumer's state reconciliation, it might create a desired state
// description of the producer, wait for the producer to realize the producer's
// desired state, and then continue to work based on the producer's desired state.
//
// One concrete example could be:
// A consumer desired state description is created -> the consumer gets triggered
// and then creates a producer desired state description -> the producer gets triggered
// and then creates a pod (which realizes the producer's desired state) -> the consumer
// waits until the pod is successfully created, and then takes the next step
//
// Note that this example differs from the classic producer-consumer model where the
// consumer does not generate anything as the producer's input.
//
// Our end goal is to prove the correctness (ESR) of both the producer and consumer
// controller in a compositional way. That is, to first prove the correctness of the
// producer (without the consumer involved), and then prove the correctness of the
// consumer using the previous correctness conclusion, while minimizing the effort
// to reason about the interactions between the two controllers.
//
// The key of the proof is to reason about:
// (1) how the consumer uses the producer to realize its own desired state, and
// (2) how the consumer and producer do NOT interfere with each other.

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(I)]
pub struct Controller<S, I> {
    pub init: StatePred<S>,
    pub next: spec_fn(I) -> ActionPred<S>,
}

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(I)]
pub struct Cluster<S, I> {
    pub target_controller: Controller<S, I>,
    pub another_controller: Controller<S, I>,
}

// The methods below define the initial state and next transitions of the state machine.
impl<S, I> Cluster<S, I> {
    pub open spec fn init(self) -> StatePred<S> {
        |s| {
            &&& (self.target_controller.init)(s)
            &&& (self.another_controller.init)(s)
            &&& other_init()(s)
        }
    }

    pub open spec fn target_controller_next(self, input: I) -> ActionPred<S> {
        (self.target_controller.next)(input)
    }

    // In a more complex example, there could be an array of "another controller"s.
    pub open spec fn another_controller_next(self, input: I) -> ActionPred<S> {
        (self.another_controller.next)(input)
    }

    pub open spec fn other_components_next(self, input: I) -> ActionPred<S> {
        other_components_next(input)
    }

    pub open spec fn stutter(self) -> ActionPred<S> {
        |s, s_prime: S| s == s_prime
    }

    pub open spec fn next(self) -> ActionPred<S> {
        |s, s_prime: S| exists |step: Step<I>| #[trigger] self.next_step(s, s_prime, step)
    }

    pub open spec fn next_step(self, s: S, s_prime: S, step: Step<I>) -> bool {
        match step {
            Step::TargetControllerStep(input) => self.target_controller_next(input)(s, s_prime),
            Step::AnotherControllerStep(input) => self.another_controller_next(input)(s, s_prime),
            Step::OtherComponentsStep(input) => self.other_components_next(input)(s, s_prime),
            Step::StutterStep() => self.stutter()(s, s_prime),
        }
    }
}

pub spec fn other_init<S>() -> StatePred<S>;

pub spec fn other_components_next<S, I>(input: I) -> ActionPred<S>;

pub enum Step<I> {
    OtherComponentsStep(I),
    TargetControllerStep(I),
    AnotherControllerStep(I),
    StutterStep(),
}

pub spec fn producer<S, I>() -> Controller<S, I>;

pub spec fn consumer<S, I>() -> Controller<S, I>;

pub spec fn producer_fairness<S, I>() -> TempPred<S>;

pub spec fn consumer_fairness<S, I>() -> TempPred<S>;

pub open spec fn consumer_and_producer<S, I>() -> Cluster<S, I> {
    Cluster {
        target_controller: consumer::<S, I>(),
        another_controller: producer::<S, I>(),
    }
}

pub open spec fn producer_and_any<S, I>(any: Controller<S, I>) -> Cluster<S, I> {
    Cluster {
        target_controller: producer::<S, I>(),
        another_controller: any,
    }
}

}
