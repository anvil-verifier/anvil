use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    trusted::{spec_types::*, step::VStatefulSetReconcileStepView::*},
    proof::predicate::*,
};
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub proof fn reconcile_eventually_terminates_on_vss_object(
    spec: TempPred<ClusterState>, vsts_key: ObjectRef, cluster: Cluster, controller_id: int
)
requires
    spec.entails(always(lift_action(cluster.next()))),
    cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
    cluster.controller_models.contains_pair(controller_id, vsts_controller_model()),
    spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
    spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.builtin_controllers_next().weak_fairness(i))),
    spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
    spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
    spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
    spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
    spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
    spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
    spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
    spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
    spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
    spec.entails(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()))),
    spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VStatefulSetView>()))),
    spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VStatefulSetView>(controller_id)))),
    spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vsts_key)))),
    // no sent request at certain steps
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts_key, lift_step(Init))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts_key, lift_step(GetPVC))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts_key, lift_step(CreatePVC))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts_key, lift_step(SkipPVC))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts_key, lift_step(CreateNeeded))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts_key, lift_step(UpdateNeeded))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts_key, lift_step(DeleteCondemned))))),
    spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vsts_key, lift_step(DeleteOutdated))))),
    // there is always sent request/pending response at certain steps for vsts to transit to next state
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts_key, lift_step(AfterListPod))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts_key, lift_step(AfterGetPVC))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts_key, lift_step(AfterCreatePVC))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts_key, lift_step(AfterCreateNeeded))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts_key, lift_step(AfterUpdateNeeded))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts_key, lift_step(AfterDeleteCondemned))))),
    spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vsts_key, lift_step(AfterDeleteOutdated))))),
ensures
    spec.entails(true_pred().leads_to(lift_state(|s: ClusterState| !s.ongoing_reconciles(controller_id).contains_key(vsts_key)))),
{}

}