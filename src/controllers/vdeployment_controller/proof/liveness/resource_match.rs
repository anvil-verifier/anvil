use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::{
    trusted::{spec_types::*, step::*, util::*},
    model::{install::*, reconciler::*},
    proof::predicate::*,
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use vstd::prelude::*;

verus !{

pub proof fn lemma_from_init_step_to_send_list_pods_req(
    vd: VDeploymentView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    spec.entails(invariants_since_phase_n(cluster, controller_id, vd, 0)),
ensures
    spec.entails(lift_state(at_vd_step_with_vd(vd, controller_id, at_step_or![Init])).and(lift_state(|s| Cluster::no_pending_req_msg(controller_id, s, vd.object_ref())))
       .leads_to(lift_state(pending_req_in_flight_and(vd, controller_id, is_list_req())))),
{
    assume(false);
}
}