use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    api_server::{types::*, state_machine::*},
    cluster::*, 
    message::*
};
use crate::vstatefulset_controller::{
    trusted::{spec_types::*, step::*, util::*, liveness_theorem::*, rely::*},
    model::{install::*, reconciler::*},
    proof::{predicate::*, liveness::api_actions::*, guarantee::*, shield_lemma::*},
};
use crate::vstatefulset_controller::trusted::step::VStatefulSetReconcileStepView::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{seq_lib::*, set_lib::*};
use vstd::{seq_lib::*, map_lib::*, multiset::*};
use vstd::prelude::*;

verus! {

pub proof fn lemma_from_init_to_current_state_matches(
    vsts: VStatefulSetView, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
requires
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(always(lift_state(cluster_invariants_since_reconciliation(cluster, vsts, controller_id)))),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(always(lifted_vsts_internal_guarantee(controller_id))),
    spec.entails(always(lifted_vsts_rely(cluster, controller_id))),
ensures
    spec.entails(lift_state(and!(
            at_vsts_step(vsts.object_ref(), controller_id, at_step![Init]),
            no_pending_req_in_cluster(vsts, controller_id)
        ))
       .leads_to(lift_state(and!(
            at_vsts_step(vsts.object_ref(), controller_id, at_step![Done]),
            no_pending_req_in_cluster(vsts, controller_id),
            current_state_matches(vsts)
        )))),
{}
}