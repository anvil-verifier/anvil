use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::InstalledTypes}, 
    cluster::*, 
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    trusted::{
        liveness_theorem::*, 
        rely::*, 
        spec_types::*, 
        step::*
    },
    proof::{
        predicate::*,
        guarantee::*
    },
};
use vstd::prelude::*;

verus! {

pub open spec fn pod_name_collision_is_impossible(vsts: VStatefulSetView, pod: PodView) -> bool {
    true
}
}