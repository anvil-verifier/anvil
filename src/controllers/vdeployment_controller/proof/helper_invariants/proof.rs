#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::InstalledTypes}, 
    cluster::*, 
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    trusted::{
        liveness_theorem::*, 
        rely_guarantee::*, 
        spec_types::*, 
        step::*
    },
    proof::{predicate::*, helper_invariants::predicate::*},
};
use crate::vreplicaset_controller::{
    trusted::{
        spec_types::*,
    }
};
use vstd::prelude::*;

verus! {

// unverified stub to complete guarantee proof.
#[verifier(external_body)]
pub proof fn lemma_always_vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    ensures spec.entails(always(lift_state(vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id)))),
{}

}
