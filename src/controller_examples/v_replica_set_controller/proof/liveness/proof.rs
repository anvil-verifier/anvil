// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{map_lib::*, string_view::*};
use crate::v_replica_set_controller::{
    model::{reconciler::*},
    proof::{
        helper_invariants,
        liveness::{
            spec::*,
            terminate,
        },
        predicate::*,
    },
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use vstd::{prelude::*, string::*};

verus! {

// We prove init /\ []next /\ []wf |= []VReplicaSet::desired_state_is(vrs) ~> []current_state_matches(vrs) holds for each vrs.
proof fn liveness_proof_forall_vrs()
   ensures liveness_theorem(),
{	
    assert forall |vrs: VReplicaSetView| #[trigger] cluster_spec().entails(liveness(vrs)) by {
        liveness_proof(vrs);
    };
    spec_entails_tla_forall(cluster_spec(), |vrs: VReplicaSetView| liveness(vrs));
}

proof fn liveness_proof(vrs: VReplicaSetView)
    ensures cluster_spec().entails(liveness(vrs)),
{
    assumption_and_invariants_of_all_phases_is_stable(vrs);
    lemma_true_leads_to_always_current_state_matches(vrs);
    reveal_with_fuel(spec_before_phase_n, 8);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(7, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(6, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(5, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(4, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(3, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(2, vrs);
    spec_before_phase_n_entails_true_leads_to_current_state_matches(1, vrs);

    let assumption = always(lift_state(VRSCluster::desired_state_is(vrs)));
    unpack_conditions_from_spec(invariants(vrs), assumption, true_pred(), always(lift_state(current_state_matches(vrs))));
    temp_pred_equality(true_pred().and(assumption), assumption);

    valid_implies_trans(
        cluster_spec().and(derived_invariants_since_beginning(vrs)), invariants(vrs),
        always(lift_state(VRSCluster::desired_state_is(vrs))).leads_to(always(lift_state(current_state_matches(vrs))))
    );
    sm_spec_entails_all_invariants(vrs);
    simplify_predicate(cluster_spec(), derived_invariants_since_beginning(vrs));
}

proof fn spec_before_phase_n_entails_true_leads_to_current_state_matches(i: nat, vrs: VReplicaSetView)
    requires
        1 <= i <= 7,
        valid(stable(spec_before_phase_n(i, vrs))),
        spec_before_phase_n(i + 1, vrs).entails(true_pred().leads_to(always(lift_state(current_state_matches(vrs)))))
    ensures spec_before_phase_n(i, vrs).entails(true_pred().leads_to(always(lift_state(current_state_matches(vrs))))),
{
    assume(false);
}

proof fn lemma_true_leads_to_always_current_state_matches(vrs: VReplicaSetView)
    ensures assumption_and_invariants_of_all_phases(vrs).entails(true_pred().leads_to(always(lift_state(current_state_matches(vrs))))),
{
    let spec = assumption_and_invariants_of_all_phases(vrs);

    assert forall |k : usize| #![auto] spec.entails(always(lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterCreatePod(k)))))) by {
        always_tla_forall_apply(spec, |k: usize| lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterCreatePod(k)))), k);
    }
    assert forall |k : usize| #![auto] spec.entails(always(lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterDeletePod(k)))))) by {
        always_tla_forall_apply(spec, |k: usize| lift_state(VRSCluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(vrs.object_ref(), at_step_closure(VReplicaSetReconcileStep::AfterDeletePod(k)))), k);
    }
    
    // The use of termination property ensures spec |= true ~> reconcile_idle.
    terminate::reconcile_eventually_terminates(spec, vrs);
    // Then we can continue to show that spec |= reconcile_idle ~> []current_state_matches(vrs).

    assume(false);
}

}
