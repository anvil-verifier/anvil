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
#[allow(unused_imports)]
use crate::pervasive::set::*;

verus! {

pub open spec fn configmapgenerator_exists_in_etcd(c: DSConstants, v: DSVariables) -> bool {
    exists |object_key:ObjectKey|
        object_key.object_type === StringL::ConfigMapGenerator
        && #[trigger] v.kubernetes_variables.cluster_state.contains(object_key)
}

pub open spec fn two_configmaps_exist_in_etcd(c: DSConstants, v: DSVariables) -> bool {
    v.kubernetes_variables.cluster_state.contains(configmap_1_key())
    && v.kubernetes_variables.cluster_state.contains(configmap_2_key())
}

pub struct Execution {
    pub constants: DSConstants,
    pub variables_seq: Seq<DSVariables>, // Pretend it is infinite
}

type TempPred = Set<Execution>;

pub open spec fn lift_state(state_pred: impl Fn(DSConstants, DSVariables) -> bool) -> TempPred {
    Set::new(|ex: Execution| state_pred(ex.constants, ex.variables_seq[0]))
}

pub open spec fn lift_action(action_pred: impl Fn(DSConstants, DSVariables, DSVariables) -> bool) -> TempPred {
    Set::new(|ex: Execution| action_pred(ex.constants, ex.variables_seq[0], ex.variables_seq[1]))
}

pub open spec fn drop(ex: Execution, idx: nat) -> Execution {
    Execution {
        constants: ex.constants,
        variables_seq: ex.variables_seq.subrange(idx as int, ex.variables_seq.len() as int)
    }
}

pub open spec fn temp_always(temp_pred: TempPred) -> TempPred {
    Set::new(|ex:Execution| forall |i:nat| i<ex.variables_seq.len() && #[trigger] temp_pred.contains(drop(ex, i)))
}

pub open spec fn temp_not(temp_pred: TempPred) -> TempPred {
    // Set::new(|ex:Execution| !temp_pred.contains(ex))
    temp_pred.complement()
}

pub open spec fn temp_and(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    temp_pred_a.intersect(temp_pred_b)
}

pub open spec fn temp_or(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    temp_pred_a.union(temp_pred_b)
}

pub open spec fn temp_eventually(temp_pred: TempPred) -> TempPred {
    temp_not(temp_always(temp_not(temp_pred)))
    // Set::new(|ex:Execution| exists |i:nat| i<ex.variables_seq.len() && #[trigger] temp_pred.contains(drop(ex, i)))
}

pub open spec fn temp_implies(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    temp_or(temp_not(temp_pred_a), temp_pred_b)
}

pub open spec fn temp_leads_to(temp_pred_a: TempPred, temp_pred_b: TempPred) -> TempPred {
    temp_always(temp_implies(temp_pred_a, temp_eventually(temp_pred_b)))
}

// Verus will report the following error for the exists in enabled
// error: Could not automatically infer triggers for this quantifer.  Use #[trigger] annotations to manually mark trigger terms instead.
// And if we set action as trigger, it reports another error
// error: trigger must be a function call, a field access, or a bitwise operator
spec fn enabled(action: impl Fn(DSConstants, DSVariables, DSVariables) -> bool) -> TempPred {
    lift_state(|constants: DSConstants, variables: DSVariables|
        exists |new_variables: DSVariables| action(constants, variables, new_variables)
    )
}

spec fn weak_fairness(action: impl Fn(DSConstants, DSVariables, DSVariables) -> bool) -> TempPred {
    temp_leads_to(temp_always(enabled(action)), lift_action(action))
    // temp_always(temp_implies(temp_always(enabled(action)), temp_eventually(lift_action(action))))
}


// Same error as enabled
spec fn enabled2(action: impl Fn(DSConstants, DSVariables, DSVariables) -> bool, constants: DSConstants, variables: DSVariables) -> bool {
    exists |new_variables: DSVariables| action(constants, variables, new_variables)
}

spec fn weak_fairness2(action: impl Fn(DSConstants, DSVariables, DSVariables) -> bool) -> TempPred {
    temp_leads_to(temp_always(lift_state(|constants: DSConstants, variables: DSVariables| enabled2(action, constants, variables))),
        lift_action(action))
}

}
