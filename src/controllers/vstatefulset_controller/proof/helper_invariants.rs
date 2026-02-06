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
pub open spec fn all_pods_in_etcd_matching_vsts_have_correct_owner_ref_labels_and_no_deletion_timestamp(vsts: VStatefulSetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |pod_key: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(pod_key)
            &&& pod_key.kind == Kind::PodKind
            &&& pod_key.namespace == vsts.metadata.namespace->0
            &&& pod_name_match(pod_key.name, vsts.metadata.name->0)
        } ==> {
            let obj = s.resources()[pod_key];
            let pod = PodView::unmarshal(obj)->Ok_0;
            &&& obj.metadata.owner_references_contains(vsts.controller_owner_ref())
            &&& obj.metadata.deletion_timestamp is None
            &&& obj.metadata.finalizers is None
            &&& PodView::unmarshal(s.resources()[pod_key]) is Ok
            &&& vsts.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
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
            &&& pvc_name_match(pvc_key.name, vsts.metadata.name->0)
        } ==> {
            let pvc_obj = s.resources()[pvc_key];
            &&& pvc_obj.metadata.owner_references is None
        }
    }
}

pub proof fn lemma_always_all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(vsts_rely_conditions(cluster, controller_id)))),
    spec.entails(always(lift_state(vsts_rely_conditions_pod_monkey(cluster.installed_types)))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(always(lift_state(all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(vsts)))),
{
    let inv = all_pvcs_in_etcd_matching_vsts_have_no_owner_ref(vsts);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& vsts_rely_conditions(cluster, controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);

    VStatefulSetReconcileState::marshal_preserves_integrity();
    VStatefulSetView::marshal_preserves_integrity();

    assert forall|s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime)
        implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                assume(false);
            },
            _ => {}
        }
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(vsts_rely_conditions(cluster, controller_id))
    );
    init_invariant(spec, cluster.init(), stronger_next, inv);
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

// we don't need to talk about ongoing_reconcile as it's covered by at_vsts_step
pub open spec fn vsts_in_schedule_does_not_have_deletion_timestamp(vsts: VStatefulSetView, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| s.scheduled_reconciles(controller_id).contains_key(vsts.object_ref()) ==> {
        &&& s.scheduled_reconciles(controller_id)[vsts.object_ref()].metadata.deletion_timestamp is None
        &&& VStatefulSetView::unmarshal(s.scheduled_reconciles(controller_id)[vsts.object_ref()]).unwrap().metadata().deletion_timestamp is None
    }
}

// similar to lemma_eventually_always_vrs_in_schedule_does_not_have_deletion_timestamp
pub proof fn lemma_eventually_always_vsts_in_schedule_does_not_have_deletion_timestamp(
    spec: TempPred<ClusterState>, vsts: VStatefulSetView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vsts)))),
    spec.entails(cluster.schedule_controller_reconcile().weak_fairness((controller_id, vsts.object_ref()))),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vsts_in_schedule_does_not_have_deletion_timestamp(vsts, controller_id))))),
{
    let p_prime = |s: ClusterState| Cluster::desired_state_is(vsts)(s);
    let q = vsts_in_schedule_does_not_have_deletion_timestamp(vsts, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::desired_state_is(vsts)(s)
        &&& Cluster::desired_state_is(vsts)(s_prime)
    };
    always_to_always_later(spec, lift_state(Cluster::desired_state_is(vsts)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::desired_state_is(vsts)),
        later(lift_state(Cluster::desired_state_is(vsts)))
    );

    cluster.schedule_controller_reconcile().wf1(
        (controller_id, vsts.object_ref()), spec, stronger_next, p_prime, q
    );
    leads_to_stable(spec, lift_action(stronger_next), lift_state(p_prime), lift_state(q));

    temp_pred_equality(
        true_pred().and(lift_state(p_prime)),
        lift_state(p_prime)
    );
    pack_conditions_to_spec(spec, lift_state(p_prime), true_pred(), always(lift_state(q)));
    temp_pred_equality(
        lift_state(p_prime),
        lift_state(Cluster::desired_state_is(vsts))
    );
    simplify_predicate(spec, always(lift_state(p_prime)));
}

}
