// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

pub trait Controller<S, I> {
    spec fn reconcile(input: I) -> ActionPred<S>;
}

pub struct Cluster<S, I, TargetController, AnotherController>
where TargetController: Controller<S, I>, AnotherController: Controller<S, I>
{
    dummy_s: std::marker::PhantomData<S>,
    dummy_i: std::marker::PhantomData<I>,
    dummy_tc: std::marker::PhantomData<TargetController>,
    dummy_ac: std::marker::PhantomData<AnotherController>,
}

pub enum Step<I> {
    OtherComponentsStep(I),
    TargetControllerStep(I),
    AnotherControllerStep(I),
    StutterStep(),
}

pub spec fn init<S>() -> StatePred<S>;

pub spec fn other_components_next<S, I>(input: I) -> ActionPred<S>;

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

pub struct ProducerController {}

impl<S, I> Controller<S, I> for ProducerController {
    spec fn reconcile(input: I) -> ActionPred<S>;
}

pub struct ConsumerController {}

impl<S, I> Controller<S, I> for ConsumerController {
    spec fn reconcile(input: I) -> ActionPred<S>;
}

pub struct ShapeShifter {}

impl<S, I> Controller<S, I> for ShapeShifter {
    spec fn reconcile(input: I) -> ActionPred<S>;
}

pub spec fn producer_fairness<S, I>() -> TempPred<S>;

pub spec fn consumer_fairness<S, I>() -> TempPred<S>;

pub type ConsumerAndProducer<S, I> = Cluster<S, I, ConsumerController, ProducerController>;

pub type ConsumerAndShapeShifter<S, I> = Cluster<S, I, ConsumerController, ShapeShifter>;

pub type ProducerAndShapeShifter<S, I> = Cluster<S, I, ProducerController, ShapeShifter>;

}
