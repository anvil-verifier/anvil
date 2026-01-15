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
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// name collision prevention invariant, eventually holds
// In the corner case when one vsts was created and then deleted, just before
// another vsts with the same name comes, GC will delete pods owned by the previous vsts
pub open spec fn all_pods_in_etcd_matching_vsts_have_correct_owner_ref_and_labels(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |pod_key: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(pod_key)
            &&& pod_key.kind == Kind::PodKind
            &&& pod_key.namespace == vsts.metadata.namespace->0
            &&& vsts.metadata.name is Some
            &&& vsts.metadata.namespace is Some
            &&& pod_name_matches_vsts(vsts.metadata.name->0, pod_key.name)
        } ==> {
            let pod_obj = s.resources()[pod_key];
            &&& pod_obj.metadata.owner_references_contains(vsts.controller_owner_ref())
            &&& vsts.spec.selector.matches(pod_obj.metadata.labels.unwrap_or(Map::empty()))
        }
    }
}

// Helper spec to check if a pod name matches a vsts naming pattern
pub open spec fn pod_name_matches_vsts(parent_name: StringView, compared_pod_name: StringView) -> bool {
    exists |ord: nat| compared_pod_name == pod_name(parent_name, ord)
}
}
