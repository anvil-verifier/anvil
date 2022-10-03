// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#![allow(unused_imports)]
use crate::apis::*;
use crate::common::*;
use crate::controller;
use crate::custom_controller_logic::*;
use crate::custom_controller_workload;
use crate::kubernetes;
use crate::network;
use crate::pervasive::seq::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct DSConstants {
    pub kubernetes_constants: kubernetes::KubernetesConstants,
    pub controller_constants: controller::ControllerConstants,
    pub workload_constants: custom_controller_workload::WorkloadConstants,
    pub network_constants: network::NetworkConstants,
    pub clock_upper_bound: int,
}

impl DSConstants {
    pub closed spec fn well_formed(&self) -> bool {
        // self.group_constants.well_formed()
        self.kubernetes_constants.well_formed()
        && self.controller_constants.well_formed()
        && self.workload_constants.well_formed()
        && self.clock_upper_bound === distributed_system_step_limit_spec()
    }
}

pub struct DSVariables {
    pub kubernetes_variables: kubernetes::KubernetesVariables,
    pub controller_variables: controller::ControllerVariables,
    pub workload_variables: custom_controller_workload::WorkloadVariables,
    pub network_variables: network::NetworkVariables,
    pub clock: int,
}

impl DSVariables {
    pub closed spec fn well_formed(&self, c: DSConstants) -> bool {
        // self.group_variables.well_formed(c.group_constants)
        self.kubernetes_variables.well_formed(c.kubernetes_constants)
        && self.controller_variables.well_formed(c.controller_constants)
        && self.workload_variables.well_formed(c.workload_constants)
        && self.clock <= c.clock_upper_bound
    }
}

pub open spec fn init(c: DSConstants, v: DSVariables) -> bool {
    c.well_formed()
    && v.well_formed(c)
    // && group::init(c.group_constants, v.group_variables)
    && kubernetes::init(c.kubernetes_constants, v.kubernetes_variables)
    && controller::init(c.controller_constants, v.controller_variables)
    && custom_controller_workload::init(c.workload_constants, v.workload_variables)
    && network::init(c.network_constants, v.network_variables)
    && v.clock === distributed_system_step_limit_spec()
}

pub open spec fn all_well_formed(c: DSConstants, v: DSVariables, v_prime: DSVariables, network_ops: NetworkOps) -> bool {
    c.well_formed()
    && v.well_formed(c)
    && v_prime.well_formed(c)
    && network_ops.well_formed()
}

pub open spec fn kubernetes_action(c: DSConstants, v: DSVariables, v_prime: DSVariables, network_ops:NetworkOps) -> bool {
    all_well_formed(c, v, v_prime, network_ops)
    && v.clock > 0
    && v_prime.clock === v.clock - 1
    && v.controller_variables === v_prime.controller_variables
    && v.workload_variables === v_prime.workload_variables
    && kubernetes::next(c.kubernetes_constants, v.kubernetes_variables, v_prime.kubernetes_variables, network_ops)
}

pub open spec fn controller_action(c: DSConstants, v: DSVariables, v_prime: DSVariables, network_ops:NetworkOps) -> bool {
    all_well_formed(c, v, v_prime, network_ops)
    && v.clock > 0
    && v_prime.clock === v.clock - 1
    && v.kubernetes_variables === v_prime.kubernetes_variables
    && v.workload_variables === v_prime.workload_variables
    && controller::next(c.controller_constants, v.controller_variables, v_prime.controller_variables, network_ops)
}

pub open spec fn workload_action(c: DSConstants, v: DSVariables, v_prime: DSVariables, network_ops:NetworkOps) -> bool {
    all_well_formed(c, v, v_prime, network_ops)
    && v.clock > 0
    && v_prime.clock === v.clock - 1
    && v.kubernetes_variables === v_prime.kubernetes_variables
    && v.controller_variables === v_prime.controller_variables
    && custom_controller_workload::next(c.workload_constants, v.workload_variables, v_prime.workload_variables, network_ops)
}

pub enum DSStep {
    KubernetesActionStep(NetworkOps),
    ControllerActionStep(NetworkOps),
    WorkloadActionStep(NetworkOps),
}

pub open spec fn next_step(c: DSConstants, v: DSVariables, v_prime: DSVariables, step: DSStep) -> bool {
    match step {
        DSStep::KubernetesActionStep(network_ops) =>
            kubernetes_action(c, v, v_prime, network_ops)
            && network::next(c.network_constants, v.network_variables, v_prime.network_variables, network_ops),
        DSStep::ControllerActionStep(network_ops) =>
            controller_action(c, v, v_prime, network_ops)
            && network::next(c.network_constants, v.network_variables, v_prime.network_variables, network_ops),
        DSStep::WorkloadActionStep(network_ops) =>
            workload_action(c, v, v_prime, network_ops)
            && network::next(c.network_constants, v.network_variables, v_prime.network_variables, network_ops),
    }
}

pub open spec fn next(c: DSConstants, v: DSVariables, v_prime: DSVariables) -> bool {
    exists(|step: DSStep| next_step(c, v, v_prime, step))
}

#[verifier(inline)] // XXX: without the inlining, this file won't verify. Likely a bug.
pub open spec fn is_sent(v: DSVariables, m: Message) -> bool {
    v.network_variables.sent_messages.contains(m)
}

}
