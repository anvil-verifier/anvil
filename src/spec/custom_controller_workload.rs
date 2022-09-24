// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::{exists, requires, ensures, equal};
#[allow(unused_imports)]
use crate::pervasive::{*, option::Option};
#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use crate::apis::*;
#[allow(unused_imports)]
use crate::custom_controller_var::*;

verus! {

pub struct WorkloadConstants {
}

impl WorkloadConstants {
    pub open spec fn well_formed(&self) -> bool {
        true
    }
}

pub struct WorkloadVariables {
    pub submitted: bool,
}

impl WorkloadVariables {
    pub open spec fn well_formed(&self, c:WorkloadConstants) -> bool {
        true
    }
}

pub enum WorkloadStep {
    CreateConfigMapGenerator(ConfigMapGeneratorL),
    ReceiveAPIOpResponseStep,
}

pub open spec fn init(c: WorkloadConstants, v: WorkloadVariables) -> bool {
    c.well_formed()
    && v.well_formed(c)
    && !v.submitted
}

pub open spec fn all_well_formed(c: WorkloadConstants, v: WorkloadVariables, v_prime: WorkloadVariables, network_ops: NetworkOps) -> bool {
    c.well_formed()
    && v.well_formed(c)
    && v_prime.well_formed(c)
    && network_ops.well_formed()
}

pub open spec fn create_configmap_generator(c: WorkloadConstants, v: WorkloadVariables, v_prime: WorkloadVariables, configmap_generator: ConfigMapGeneratorL, network_ops: NetworkOps) -> bool {
    all_well_formed(c, v, v_prime, network_ops)
    && !v.submitted
    && v_prime.submitted
    && equal(configmap_generator.name, StringL::MyConfigMapGenerator)
    && equal(configmap_generator.namespace, StringL::Default)
    && network_ops.recv.is_None()
    && network_ops.send.is_Some()
    && network_ops.send.get_Some_0().src === HostId::CustomClient
    && network_ops.send.get_Some_0().dst === HostId::KubernetesAPI
    && match network_ops.send.get_Some_0().message {
        Message::APIOpRequest(api_op_request) => equal(api_op_request.api_op, APIOp::Create{
            object_key: configmap_generator.key(),
            object: KubernetesObject::CustomResourceObject(
                CustomResourceObject::ConfigMapGenerator(configmap_generator)
            ),
        }),
        _ => false,
    }
}

pub open spec fn receive_api_op_response(c: WorkloadConstants, v: WorkloadVariables, v_prime: WorkloadVariables, network_ops: NetworkOps) -> bool {
    all_well_formed(c, v, v_prime, network_ops)
    && v.submitted
    && v_prime.submitted
    && network_ops.send.is_None()
    && network_ops.recv.is_Some()
    && network_ops.recv.get_Some_0().src === HostId::KubernetesAPI
    && network_ops.recv.get_Some_0().dst === HostId::CustomClient
    && match network_ops.recv.get_Some_0().message {
        Message::APIOpResponse(api_op_response) => true,
        _ => false,
    }
}

pub open spec fn next_step(c: WorkloadConstants, v: WorkloadVariables, v_prime: WorkloadVariables, network_ops: NetworkOps, step: WorkloadStep) -> bool {
    match step {
        WorkloadStep::CreateConfigMapGenerator(configmap_generator) => create_configmap_generator(c, v, v_prime, configmap_generator, network_ops),
        WorkloadStep::ReceiveAPIOpResponseStep => receive_api_op_response(c, v, v_prime, network_ops),
    }
}

// Maybe we can start from hardcoding a CR to make it simple
pub open spec fn next(c: WorkloadConstants, v: WorkloadVariables, v_prime: WorkloadVariables, network_ops: NetworkOps) -> bool {
    exists(|step: WorkloadStep| next_step(c, v, v_prime, network_ops, step))
}

}
