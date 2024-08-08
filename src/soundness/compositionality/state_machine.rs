// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

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

// A helper trait that allows us to plug any controller logic into the state machine
pub trait Controller<S, I> {
    spec fn reconcile(input: I) -> ActionPred<S>;
}

// We define a struct for the abstract state machine. The dummy variables are not
// used anywhere but just to shut up checks on unused generic types.
pub struct Cluster<S, I, TargetController, AnotherController>
where TargetController: Controller<S, I>, AnotherController: Controller<S, I>
{
    dummy_s: std::marker::PhantomData<S>,
    dummy_i: std::marker::PhantomData<I>,
    dummy_tc: std::marker::PhantomData<TargetController>,
    dummy_ac: std::marker::PhantomData<AnotherController>,
}

// The methods below define the initial state and next transitions of the state machine.
impl<S, I, TargetController, AnotherController> Cluster<S, I, TargetController, AnotherController>
where TargetController: Controller<S, I>, AnotherController: Controller<S, I>
{
    pub open spec fn init() -> StatePred<S> {
        init()
    }

    pub open spec fn target_controller_next(input: I) -> ActionPred<S> {
        TargetController::reconcile(input)
    }

    pub open spec fn another_controller_next(input: I) -> ActionPred<S> {
        AnotherController::reconcile(input)
    }

    pub open spec fn other_components_next(input: I) -> ActionPred<S> {
        other_components_next(input)
    }

    pub open spec fn stutter() -> ActionPred<S> {
        |s, s_prime: S| s == s_prime
    }

    pub open spec fn next() -> ActionPred<S> {
        |s, s_prime: S| exists |step: Step<I>| #[trigger] Self::next_step(s, s_prime, step)
    }

    pub open spec fn next_step(s: S, s_prime: S, step: Step<I>) -> bool {
        match step {
            Step::TargetControllerStep(input) => Self::target_controller_next(input)(s, s_prime),
            Step::AnotherControllerStep(input) => Self::another_controller_next(input)(s, s_prime),
            Step::OtherComponentsStep(input) => Self::other_components_next(input)(s, s_prime),
            Step::StutterStep() => Self::stutter()(s, s_prime),
        }
    }
}

pub spec fn init<S>() -> StatePred<S>;

pub spec fn other_components_next<S, I>(input: I) -> ActionPred<S>;

pub enum Step<I> {
    OtherComponentsStep(I),
    TargetControllerStep(I),
    AnotherControllerStep(I),
    StutterStep(),
}

// The controller logic of the producer controller.
pub struct ProducerController {}

impl<S, I> Controller<S, I> for ProducerController {
    spec fn reconcile(input: I) -> ActionPred<S>;
}

// The controller logic of the consumer controller.
pub struct ConsumerController {}

impl<S, I> Controller<S, I> for ConsumerController {
    spec fn reconcile(input: I) -> ActionPred<S>;
}

// The controller logic of the shape shifter. The shape shifter is not any
// concrete controller. It's used to represent *any* possible controller
// that will interact with the target controller.
// If we write down the body of the reconcile, it will be:
// randomly choose a state object to create, update or delete.
pub struct ShapeShifter {}

impl<S, I> Controller<S, I> for ShapeShifter {
    spec fn reconcile(input: I) -> ActionPred<S>;
}

// Here is an example: the shape shifter can simulate the behavior of the
// consumer. For any possible transition taken by the consumer, the shape
// shifter can take the same transition.
#[verifier(external_body)]
pub proof fn consumer_does_nothing_beyond_what_shape_shifter_does<S, I>(input: I) -> (ss_input: I)
    ensures forall |s, s_prime: S| #[trigger] ConsumerController::reconcile(input)(s, s_prime)
            ==> ShapeShifter::reconcile(ss_input)(s, s_prime)
{
    arbitrary()
}

// Fairness conditions used for proving liveness
pub spec fn producer_fairness<S, I>() -> TempPred<S>;

pub spec fn consumer_fairness<S, I>() -> TempPred<S>;

// We "instantiate" the Cluster by plugging different controller logics into different positions.
pub type ConsumerAndProducer<S, I> = Cluster<S, I, ConsumerController, ProducerController>;

pub type ConsumerAndShapeShifter<S, I> = Cluster<S, I, ConsumerController, ShapeShifter>;

pub type ProducerAndShapeShifter<S, I> = Cluster<S, I, ProducerController, ShapeShifter>;

}
