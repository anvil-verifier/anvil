// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use crate::apis::*;
#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use crate::custom_controller_logic::*;
#[allow(unused_imports)]
use crate::distributed_system::*;

#[allow(unused_imports)]
use crate::pervasive::seq::*;

verus! {

// The following code does not compile as Verus reports many errors
// including not support returning closure type,
// DSConstants not implementing Copy/Clone traits and so on.

pub open spec fn configmapgenerator_exists_in_etcd(c: DSConstants, v: DSVariables) -> bool {
    exists |object_key:ObjectKey|
        object_key.object_type === StringL::ConfigMapGenerator
        && #[trigger] v.kubernetes_variables.cluster_state.contains(object_key)
}

pub open spec fn two_configmaps_exist_in_etcd(c: DSConstants, v: DSVariables) -> bool {
    v.kubernetes_variables.cluster_state.contains(configmap_1_key())
    && v.kubernetes_variables.cluster_state.contains(configmap_2_key())
}

type ClosureType = Box<Fn(i32) -> i32>;

pub open spec fn lift_state
(state_pred: impl Fn(DSConstants, DSVariables) -> bool) -> impl Fn(DSConstants, Seq<DSVariables>) -> bool {
    move |c: DSConstants, behavior: Seq<DSVariables>| state_pred(c, behavior[0])
}

pub open spec fn temp_not
(temp_pred: impl Fn(DSConstants, Seq<DSVariables>) -> bool) -> impl Fn(DSConstants, Seq<DSVariables>) -> bool {
    move |c: DSConstants, behavior: Seq<DSVariables>| !temp_pred(c, behavior)
}

pub open spec fn temp_and
(temp_pred_a: impl Fn(DSConstants, Seq<DSVariables>) -> bool, temp_pred_b: impl Fn(DSConstants, Seq<DSVariables>) -> bool) -> impl Fn(DSConstants, Seq<DSVariables>) -> bool {
    move |c: DSConstants, behavior: Seq<DSVariables>| {
        temp_pred_a(c, behavior) && temp_pred_b(c, behavior)
    }
}

pub open spec fn temp_or
(temp_pred_a: impl Fn(DSConstants, Seq<DSVariables>) -> bool, temp_pred_b: impl Fn(DSConstants, Seq<DSVariables>) -> bool) -> impl Fn(DSConstants, Seq<DSVariables>) -> bool {
    move |c: DSConstants, behavior: Seq<DSVariables>| temp_not(temp_and(temp_not(temp_pred_a(c, behavior)), temp_not(temp_pred_b(c, behavior))))
}

pub open spec fn temp_implies
(temp_pred_a: impl Fn(DSConstants, Seq<DSVariables>) -> bool, temp_pred_b: impl Fn(DSConstants, Seq<DSVariables>) -> bool) -> impl Fn(DSConstants, Seq<DSVariables>) -> bool {
    move |c: DSConstants, behavior: Seq<DSVariables>| temp_or(temp_not(temp_pred_a(c, behavior)), temp_pred_b(c, behavior))
}

pub open spec fn temp_always
(temp_pred: impl Fn(DSConstants, Seq<DSVariables>) -> bool) -> impl Fn(DSConstants, Seq<DSVariables>) -> bool {
    move |c: DSConstants, behavior: Seq<DSVariables>| {
        let len = behavior.clone().len(); // Verus complains that behavior does not implement Clone/Copy
        return forall |i:int| i<len && temp_pred(c, behavior.subrange(i, len))
    }
}

pub open spec fn temp_eventually
(temp_pred: impl Fn(DSConstants, Seq<DSVariables>) -> bool) -> impl Fn(DSConstants, Seq<DSVariables>) -> bool {
    move |c: DSConstants, behavior: Seq<DSVariables>| temp_not(temp_always(temp_not(temp_pred(c, behavior))))
}

pub open spec fn leads_to
(temp_pred_a: impl Fn(DSConstants, Seq<DSVariables>) -> bool, temp_pred_b: impl Fn(DSConstants, Seq<DSVariables>) -> bool) -> impl Fn(DSConstants, Seq<DSVariables>) -> bool {
    move |c: DSConstants, behavior: Seq<DSVariables>| temp_implies(temp_pred_a(c, behavior), temp_eventually(temp_pred_b(c, behavior)))
}

// temp_always(temp_leads(temp_always(configmapgenerator_exists_in_etcd()), two_configmaps_exist_in_etcd()))


}
