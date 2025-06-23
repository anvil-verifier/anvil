use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::{
    trusted::{spec_types::*, step::*, util::*, liveness_theorem::*},
    model::{install::*, reconciler::*},
    proof::predicate::*,
};
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub proof fn lemma_api_request_other_than_pending_req_msg_maintains_filter_old_and_new_vrs(
    s: ClusterState, s_prime: ClusterState, vd: VDeploymentView, cluster: Cluster, controller_id: int, 
    msg: Message,
)
requires
    cluster_invariants_since_reconciliation(cluster, vd, controller_id)(s),
    !Cluster::pending_req_msg_is(controller_id, s, vd.object_ref(), msg),
ensures
    filter_old_and_new_vrs_on_etcd(vd, s.resources()) == filter_old_and_new_vrs_on_etcd(vd, s_prime.resources()){}

}