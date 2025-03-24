use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vreplicaset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*},
    proof::{helper_invariants, helper_lemmas, liveness::{api_actions::*}, predicate::*},
};
use vstd::{map::*, map_lib::*, math::*, prelude::*};

verus! {

pub open spec fn assumption_and_invariants_of_all_phases(vrs: VReplicaSetView) -> TempPred<ClusterState> {
    invariants(vrs)
    .and(always(lift_state(desired_state_is(vrs))))
    .and(invariants_since_phase_i(vrs))
    .and(invariants_since_phase_ii(vrs))
    .and(invariants_since_phase_iii(vrs))
    .and(invariants_since_phase_iv(vrs))
    .and(invariants_since_phase_v(vrs))
    .and(invariants_since_phase_vi(vrs))
    .and(invariants_since_phase_vii(vrs))
}

pub open spec fn invariants_since_phase_n(n: nat, vrs: VReplicaSetView) -> TempPred<ClusterState> {
    if n == 0 {
        invariants(vrs).and(always(lift_state(desired_state_is(vrs))))
    } else if n == 1 {
        invariants_since_phase_i(vrs)
    } else if n == 2 {
        invariants_since_phase_ii(vrs)
    } else if n == 3 {
        invariants_since_phase_iii(vrs)
    } else if n == 4 {
        invariants_since_phase_iv(vrs)
    } else if n == 5 {
        invariants_since_phase_v(vrs)
    } else if n == 6 {
        invariants_since_phase_vi(vrs)
    } else if n == 7 {
        invariants_since_phase_vii(vrs)
    } else {
        true_pred()
    }
}

pub open spec fn spec_before_phase_n(n: nat, vrs: VReplicaSetView) -> TempPred<ClusterState>
    decreases n,
{
    if n == 1 {
        invariants(vrs).and(always(lift_state(desired_state_is(vrs))))
    } else if 2 <= n <= 8 {
        spec_before_phase_n((n-1) as nat, vrs).and(invariants_since_phase_n((n-1) as nat, vrs))
    } else {
        true_pred()
    }
}

#[verifier(external_body)]
pub proof fn spec_of_previous_phases_entails_eventually_new_invariants(i: nat, vrs: VReplicaSetView)
    requires 1 <= i <= 7,
    ensures spec_before_phase_n(i, vrs).entails(true_pred().leads_to(invariants_since_phase_n(i, vrs))),
{
    let spec = spec_before_phase_n(i, vrs);
    reveal_with_fuel(spec_before_phase_n, 8);
    entails_preserved_by_always(lift_state(desired_state_is(vrs)), lift_state(ClusterState::desired_state_is(vrs)));
    entails_trans(spec, always(lift_state(desired_state_is(vrs))), always(lift_state(ClusterState::desired_state_is(vrs))));
    if i == 1 {
        ClusterState::lemma_true_leads_to_crash_always_disabled(spec);
        ClusterState::lemma_true_leads_to_req_drop_always_disabled(spec);
        ClusterState::lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as(spec, vrs);
        leads_to_always_combine_n!(
            spec,
            true_pred(),
            lift_state(Cluster::crash_disabled()),
            lift_state(Cluster::req_drop_disabled()),
            lift_state(Cluster::pod_monkey_disabled())
        );
    } else {
    }
}

}