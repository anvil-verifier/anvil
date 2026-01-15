#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::{
    spec::{api_server::{state_machine::*, types::*}, cluster::*, controller::types::*, message::*, esr::*,},
    proof::{controller_runtime_liveness::*, network::*},
};

use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    trusted::{liveness_theorem::*, rely::*, spec_types::*, step::*, step::VStatefulSetReconcileStepView::*},
    proof::{predicate::*, liveness::{spec::*, terminate}},
};
use crate::reconciler::spec::io::*;
use vstd::{map::*, map_lib::*, math::*, prelude::*};

verus! {

pub proof fn spec_entails_always_cluster_invariants_since_reconciliation_holds_pre_cr(spec: TempPred<ClusterState>, vsts: VStatefulSetView, controller_id: int, cluster: Cluster)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        spec.entails(next_with_wf(cluster, controller_id)),
        // The vsts type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        // The vsts controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
        // No other controllers interfere with the vsts controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vsts_rely(other_id, cluster.installed_types)))),
    ensures
        spec.entails(always(lift_state(Cluster::desired_state_is(vsts))).leads_to(vsts_cluster_invariants(spec, vsts, cluster, controller_id))),
{
    // TODO: Complete the proof
    assume(false);
}

}
