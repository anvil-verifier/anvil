// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{common::*, distributed_system::*, reconciler::Reconciler};
use crate::pervasive::seq::*;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn added_event_msg_to_controller(res: ResourceObj) -> Message {
    form_msg(HostId::KubernetesAPI, HostId::CustomController, added_event_msg(res))
}

pub proof fn always_res_exists_implies_added_in_flight_or_reconcile_ongoing_or_reconcile_scheduled<T>(reconciler: Reconciler<T>, res: ResourceObj)
    requires
        (reconciler.reconcile_trigger)(added_event_msg_to_controller(res)).is_Some(),
    ensures
        sm_spec(reconciler).entails(
            always(
                lift_state(|s: State<T>| s.resource_obj_exists(res)).implies(lift_state(|s: State<T>| {
                    ||| s.message_in_flight(added_event_msg_to_controller(res))
                    ||| s.reconcile_state_contains((reconciler.reconcile_trigger)(added_event_msg_to_controller(res)).get_Some_0())
                    ||| s.reconcile_scheduled_for((reconciler.reconcile_trigger)(added_event_msg_to_controller(res)).get_Some_0())
                }))
            )
        ),
{
    let invariant = |s: State<T>| {
        s.resource_obj_exists(res)
        ==> s.message_in_flight(added_event_msg_to_controller(res))
            || s.reconcile_state_contains((reconciler.reconcile_trigger)(added_event_msg_to_controller(res)).get_Some_0())
            || s.reconcile_scheduled_for((reconciler.reconcile_trigger)(added_event_msg_to_controller(res)).get_Some_0())
    };
    init_invariant::<State<T>>(sm_spec(reconciler), init(reconciler), next(reconciler), invariant);
    let invariant_temp_pred = lift_state(|s: State<T>| s.resource_obj_exists(res)).implies(lift_state(|s: State<T>| {
        ||| s.message_in_flight(added_event_msg_to_controller(res))
        ||| s.reconcile_state_contains((reconciler.reconcile_trigger)(added_event_msg_to_controller(res)).get_Some_0())
        ||| s.reconcile_scheduled_for((reconciler.reconcile_trigger)(added_event_msg_to_controller(res)).get_Some_0())
    }));
    temp_pred_equality::<State<T>>(lift_state(invariant), invariant_temp_pred);
}

}
