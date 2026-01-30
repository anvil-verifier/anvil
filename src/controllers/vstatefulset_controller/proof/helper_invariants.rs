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
            &&& pod_name_match(pod_key.name, vsts.metadata.name->0)
        } ==> {
            let obj = s.resources()[pod_key];
            let pod = PodView::unmarshal(obj)->Ok_0;
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
            &&& PodView::unmarshal(s.resources()[pod_key]) is Ok
            // &&& pod_spec_matches(vsts, pod)
        }
    }
}

// similar to above, but for PVCs
// rely conditions already prevent other controllers from creating or updating PVCs
// and VSTS controller's internal guarantee says all pvcs it creates have no owner refs
pub open spec fn all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |pvc_key: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(pvc_key)
            &&& pvc_key.kind == Kind::PersistentVolumeClaimKind
            &&& pvc_key.namespace == vsts.metadata.namespace->0
            &&& exists |vsts_name| pvc_name_match(pvc_key.name, vsts_name)
        } ==> {
            let pvc_obj = s.resources()[pvc_key];
            &&& pvc_obj.metadata.owner_references is None
        }
    }
}

pub proof fn lemma_always_there_is_no_request_msg_to_external_from_controller(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
{
    let inv = Cluster::there_is_no_request_msg_to_external_from_controller(controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);

    VStatefulSetReconcileState::marshal_preserves_integrity();
    VStatefulSetView::marshal_preserves_integrity();

    assert forall|s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime)
        implies inv(s_prime) by {
        let new_msgs = s_prime.in_flight().sub(s.in_flight());

        assert forall |msg: Message|
            inv(s)
            && #[trigger] s_prime.in_flight().contains(msg)
            && msg.src.is_controller_id(controller_id)
            implies msg.dst != HostId::External(controller_id) by {
            if s.in_flight().contains(msg) {
                // Empty if statement required to trigger quantifiers.
            }
            if new_msgs.contains(msg) {
                // Empty if statement required to trigger quantifiers.
            }
        }
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

}
