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
    proof::{
        predicate::*, 
        helper_invariants::predicate::*,
        helper_lemmas
    },
};
use crate::vreplicaset_controller::{
    trusted::{
        spec_types::*,
    }
};
use vstd::prelude::*;

verus! {

pub proof fn lemma_eventually_always_no_pending_mutation_request_not_from_controller_on_vrs_objects(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] vd_rely(other_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects())))),
{
    let requirements = |msg: Message, s: ClusterState| {
        ({
            &&& !(msg.src.is_Controller() || msg.src.is_BuiltinController())
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        })
        ==>
        ({
            &&& msg.content.is_create_request() ==> msg.content.get_create_request().key().kind != VReplicaSetView::kind()
            &&& msg.content.is_update_request() ==> msg.content.get_update_request().key().kind != VReplicaSetView::kind()
            // too radical, loosen it later to allow updates on pod status.
            &&& msg.content.is_update_status_request() ==> msg.content.get_update_status_request().key().kind != VReplicaSetView::kind()
            &&& msg.content.is_delete_request() ==> msg.content.get_delete_request().key.kind != VReplicaSetView::kind()
            &&& msg.content.is_get_then_delete_request() ==> msg.content.get_get_then_delete_request().key.kind != VReplicaSetView::kind()
            &&& msg.content.is_get_then_update_request() ==> msg.content.get_get_then_update_request().key().kind != VReplicaSetView::kind()
        })
    };

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_builtin_object_in_etcd_is_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s)
        &&& forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
                ==> #[trigger] vd_rely(other_id)(s_prime)
    };

    helper_lemmas::vd_rely_condition_equivalent_to_lifted_vd_rely_condition_action(
        spec, cluster, controller_id
    );
    invariant_n!(
        spec, lift_action(stronger_next),
        lift_action(Cluster::every_new_req_msg_if_in_flight_then_satisfies(requirements)),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pod_monkey_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VDeploymentView>()),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lifted_vd_rely_condition_action(cluster, controller_id)
    );

    cluster.lemma_true_leads_to_always_every_in_flight_req_msg_satisfies(spec, requirements);
    temp_pred_equality(
        lift_state(no_pending_mutation_request_not_from_controller_on_vrs_objects()),
        lift_state(Cluster::every_in_flight_req_msg_satisfies(requirements))
    );
}

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

pub proof fn lemma_always_every_msg_from_vd_controller_carries_vd_key(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VDeploymentView>(),
        cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
    ensures
        spec.entails(always(lift_state(every_msg_from_vd_controller_carries_vd_key(controller_id)))),
{
    let inv = every_msg_from_vd_controller_carries_vd_key(controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(
        spec, controller_id
    );

    VDeploymentReconcileState::marshal_preserves_integrity();
    VDeploymentView::marshal_preserves_integrity();

    assert forall|s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime)
        implies inv(s_prime) by {
        let new_msgs = s_prime.in_flight().sub(s.in_flight());

        assert forall |msg: Message|
            inv(s)
            && #[trigger] s_prime.in_flight().contains(msg)
            && msg.src.is_Controller()
            && msg.src.get_Controller_0() == controller_id
            implies msg.src.get_Controller_1().kind == VDeploymentView::kind() by {
            if new_msgs.contains(msg) {
            } else {
                if s.in_flight().contains(msg) {
                    // Empty if statement required to trigger quantifiers.
                }
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

pub proof fn lemma_eventually_always_vd_in_schedule_does_not_have_deletion_timestamp(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(Cluster::desired_state_is(vd)))),
    spec.entails(cluster.schedule_controller_reconcile().weak_fairness((controller_id, vd.object_ref()))),
    cluster.controller_models.contains_key(controller_id),
    cluster.controller_models[controller_id].reconcile_model.kind == VDeploymentView::kind(),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id))))),
{
    let p_prime = |s: ClusterState| Cluster::desired_state_is(vd)(s);
    let q = vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::desired_state_is(vd)(s)
        &&& Cluster::desired_state_is(vd)(s_prime)
    };
    always_to_always_later(spec, lift_state(Cluster::desired_state_is(vd)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::desired_state_is(vd)),
        later(lift_state(Cluster::desired_state_is(vd)))
    );

    cluster.schedule_controller_reconcile().wf1(
        (controller_id, vd.object_ref()),
        spec,
        stronger_next,
        p_prime,
        q
    );
    leads_to_stable(spec, lift_action(stronger_next), lift_state(p_prime), lift_state(q));

    temp_pred_equality(
        true_pred().and(lift_state(p_prime)),
        lift_state(p_prime)
    );
    pack_conditions_to_spec(spec, lift_state(p_prime), true_pred(), always(lift_state(q)));
    temp_pred_equality(
        lift_state(p_prime),
        lift_state(Cluster::desired_state_is(vd))
    );
    simplify_predicate(spec, always(lift_state(p_prime)));
}

pub proof fn lemma_eventually_always_vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(
    spec: TempPred<ClusterState>, vd: VDeploymentView, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id)))),
    spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref())))),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
ensures
    spec.entails(true_pred().leads_to(always(lift_state(vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id))))),
{
    let reconcile_idle = |s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vd.object_ref());
    let q = vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(vd, controller_id);

    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(vd_in_schedule_does_not_have_deletion_timestamp(vd, controller_id))
    );

    leads_to_weaken(
        spec,
        true_pred(), lift_state(reconcile_idle),
        true_pred(), lift_state(q)
    );
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(q));
}

pub proof fn lemma_always_there_is_no_request_msg_to_external_from_controller(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int,
)
requires
    spec.entails(lift_state(cluster.init())),
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VDeploymentView>(),
    cluster.controller_models.contains_pair(controller_id, vd_controller_model()),
ensures
    spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
{
    let inv = Cluster::there_is_no_request_msg_to_external_from_controller(controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(
        spec, controller_id
    );

    VDeploymentReconcileState::marshal_preserves_integrity();
    VDeploymentView::marshal_preserves_integrity();

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
