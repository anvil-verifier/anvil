// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

#[allow(unused_imports)]
use crate::pervasive::{*, option::Option};
#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use crate::apis::*;
#[allow(unused_imports)]
use crate::distributed_system::*;
#[allow(unused_imports)]
use crate::custom_controller_logic::*;
#[allow(unused_imports)]
use crate::custom_controller_var::*;


#[allow(unused_imports)]
use crate::kubernetes;
#[allow(unused_imports)]
use crate::controller;
#[allow(unused_imports)]
use crate::custom_controller_workload;

verus! {
spec fn controller_clock_never_larger_than_10(c: DSConstants, v: DSVariables) -> bool {
    v.controller_variables.controller_clock <= controller_step_limit_spec()
}

spec fn controller_initialized_at_c10(c: DSConstants, v: DSVariables) -> bool {
    v.controller_variables.controller_clock == 10 ==> {
        &&& v.controller_variables.state_cache.empty()
        &&& equal(v.controller_variables.reconcile_step, ReconcileStep::Init)
        &&& (forall|message:Message| is_sent(v, message) ==> !matches!(message, Message::APIOpRequest(_)))
        &&& (forall|message:Message| is_sent(v, message) ==> !matches!(message, Message::APIOpResponse(_)))
        &&& equal(v.controller_variables.last_api_op_response, Option::Some(APIOpResponse{success:true, api_op:APIOp::Noop, object:KubernetesObject::None}))
    }
}

spec fn controller_sends_get_cr_at_c9(c: DSConstants, v: DSVariables) -> bool {
    v.controller_variables.controller_clock == 9 ==> {
        &&& equal(v.controller_variables.reconcile_step, ReconcileStep::CustomReconcileStep(CustomReconcileStep::CheckIfCMGExists))
        &&& v.controller_variables.triggering_key.is_Some()
        &&& is_sent(v, Message::APIOpRequest(APIOpRequest{
            api_op: APIOp::Get{
                object_key: v.controller_variables.triggering_key.get_Some_0()
            }
        }))
    }
}

#[verifier(external_body)]
proof fn assume_controller_gets_cr(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        v.controller_variables.controller_clock == 9,
        v_prime.controller_variables.controller_clock == 8,
        next(c, v, v_prime)
    ensures
        v.controller_variables.last_api_op_response.is_Some(),
        v.controller_variables.last_api_op_response.get_Some_0().success,
        v.controller_variables.triggering_key.is_Some(),
        v.controller_variables.state_cache.contains(v.controller_variables.triggering_key.get_Some_0()),
{
}

spec fn controller_sends_get_cm1_at_c8(c: DSConstants, v: DSVariables) -> bool {
    v.controller_variables.controller_clock == 8 ==> {
        &&& equal(v.controller_variables.reconcile_step, ReconcileStep::CustomReconcileStep(CustomReconcileStep::CheckIfCMExists))
        &&& is_sent(v, Message::APIOpRequest(APIOpRequest{
            api_op: APIOp::Get{
                object_key: configmap_1_key()
            }
        }))
    }
}

#[verifier(external_body)]
proof fn assume_controller_not_get_cm1(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        v.controller_variables.controller_clock == 8,
        v_prime.controller_variables.controller_clock == 7,
        next(c, v, v_prime)
    ensures
        v.controller_variables.last_api_op_response.is_Some(),
        !v.controller_variables.last_api_op_response.get_Some_0().success,
        v.controller_variables.triggering_key.is_Some(),
        v.controller_variables.state_cache.contains(v.controller_variables.triggering_key.get_Some_0()),
        !v.controller_variables.state_cache.contains(configmap_1_key()),
{
}

spec fn controller_sends_create_cm1_at_c7(c: DSConstants, v: DSVariables) -> bool {
    v.controller_variables.controller_clock == 7 ==> {
        &&& equal(v.controller_variables.reconcile_step, ReconcileStep::CustomReconcileStep(CustomReconcileStep::CreateCM1))
        &&& v.controller_variables.triggering_key.is_Some()
        &&& is_sent(v, Message::APIOpRequest(APIOpRequest{
            api_op: APIOp::Create{
                object_key: configmap_1_key(),
                object:KubernetesObject::ConfigMap(ConfigMapL{
                    name: StringL::ConfigMap1,
                    namespace: StringL::Default,
                    owner_key: v.controller_variables.triggering_key.get_Some_0(),
                }),
            }
        }))
    }
}

#[verifier(external_body)]
proof fn assume_controller_creates_cm1(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        v.controller_variables.controller_clock == 7,
        v_prime.controller_variables.controller_clock == 6,
        next(c, v, v_prime)
    ensures
        v.controller_variables.last_api_op_response.is_Some(),
        v.controller_variables.last_api_op_response.get_Some_0().success,
        v.controller_variables.triggering_key.is_Some(),
        v.controller_variables.state_cache.contains(v.controller_variables.triggering_key.get_Some_0()),
        v.controller_variables.state_cache.contains(configmap_1_key()),
{
}

spec fn controller_sends_create_cm2_at_c6(c: DSConstants, v: DSVariables) -> bool {
    v.controller_variables.controller_clock == 6 ==> {
        &&& equal(v.controller_variables.reconcile_step, ReconcileStep::CustomReconcileStep(CustomReconcileStep::CreateCM2))
        &&& v.controller_variables.triggering_key.is_Some()
        &&& is_sent(v, Message::APIOpRequest(APIOpRequest{
            api_op: APIOp::Create{
                object_key: configmap_2_key(),
                object:KubernetesObject::ConfigMap(ConfigMapL{
                    name: StringL::ConfigMap2,
                    namespace: StringL::Default,
                    owner_key: v.controller_variables.triggering_key.get_Some_0(),
                }),
            }
        }))
    }
}

spec fn inv(c: DSConstants, v: DSVariables) -> bool {
    &&& c.well_formed()
    &&& v.well_formed(c)
    &&& controller_clock_never_larger_than_10(c, v) // i0
    &&& controller_initialized_at_c10(c, v) // i1
    &&& controller_sends_get_cr_at_c9(c, v) // i2
    &&& controller_sends_get_cm1_at_c8(c, v) // i3
    &&& controller_sends_create_cm1_at_c7(c, v) // i4
    &&& controller_sends_create_cm2_at_c6(c, v) // i5
}

proof fn init_implies_i0(c: DSConstants, v: DSVariables)
    requires
        init(c, v)
    ensures
        controller_clock_never_larger_than_10(c, v)
{
}

proof fn inv_preserves_i0(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v),
        next(c, v, v_prime)
    ensures
        controller_clock_never_larger_than_10(c, v_prime)
{
}

proof fn init_implies_i1(c: DSConstants, v: DSVariables)
    requires
        init(c, v)
    ensures
        controller_initialized_at_c10(c, v)
{
}

proof fn inv_preserves_i1(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v),
        next(c, v, v_prime)
    ensures
        controller_initialized_at_c10(c, v_prime)
{
}

proof fn init_implies_i2(c: DSConstants, v: DSVariables)
    requires
        init(c, v)
    ensures
        controller_sends_get_cr_at_c9(c, v)
{
}

proof fn inv_preserves_i2(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v),
        next(c, v, v_prime)
    ensures
        controller_sends_get_cr_at_c9(c, v_prime)
{
}

proof fn init_implies_i3(c: DSConstants, v: DSVariables)
    requires
        init(c, v)
    ensures
        controller_sends_get_cm1_at_c8(c, v)
{
}

proof fn inv_preserves_i3(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v),
        next(c, v, v_prime)
    ensures
        controller_sends_get_cm1_at_c8(c, v_prime)
{
    let step = choose|step: DSStep| next_step(c, v, v_prime, step);
    match step {
        DSStep::ControllerActionStep(network_ops) => {
            let controller_step = choose|controller_step: controller::ControllerStep| controller::next_step(c.controller_constants, v.controller_variables, v_prime.controller_variables, network_ops, controller_step);
            match controller_step {
                controller::ControllerStep::ContinueReconcileStep => {
                    if v.controller_variables.controller_clock == 9 {
                        assume_controller_gets_cr(c, v, v_prime);
                    }
                },
                _ => {
                },
            }
        },
        _ => {
        },
    }
}

proof fn init_implies_i4(c: DSConstants, v: DSVariables)
    requires
        init(c, v)
    ensures
        controller_sends_create_cm1_at_c7(c, v)
{
}

proof fn inv_preserves_i4(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v),
        next(c, v, v_prime)
    ensures
        controller_sends_create_cm1_at_c7(c, v_prime)
{
    let step = choose|step: DSStep| next_step(c, v, v_prime, step);
    match step {
        DSStep::ControllerActionStep(network_ops) => {
            let controller_step = choose|controller_step: controller::ControllerStep| controller::next_step(c.controller_constants, v.controller_variables, v_prime.controller_variables, network_ops, controller_step);
            match controller_step {
                controller::ControllerStep::ContinueReconcileStep => {
                    if v.controller_variables.controller_clock == 8 {
                        assume_controller_not_get_cm1(c, v, v_prime);
                    }
                },
                _ => {
                },
            }
        },
        _ => {
        },
    }
}

proof fn init_implies_i5(c: DSConstants, v: DSVariables)
    requires
        init(c, v)
    ensures
        controller_sends_create_cm2_at_c6(c, v)
{
}

proof fn inv_preserves_i5(c: DSConstants, v: DSVariables, v_prime: DSVariables)
    requires
        inv(c, v),
        next(c, v, v_prime)
    ensures
        controller_sends_create_cm2_at_c6(c, v_prime)
{
    let step = choose|step: DSStep| next_step(c, v, v_prime, step);
    match step {
        DSStep::ControllerActionStep(network_ops) => {
            let controller_step = choose|controller_step: controller::ControllerStep| controller::next_step(c.controller_constants, v.controller_variables, v_prime.controller_variables, network_ops, controller_step);
            match controller_step {
                controller::ControllerStep::ContinueReconcileStep => {
                    if v.controller_variables.controller_clock == 7 {
                        assume_controller_creates_cm1(c, v, v_prime);
                    }
                },
                _ => {
                },
            }
        },
        _ => {
        },
    }
}
}
