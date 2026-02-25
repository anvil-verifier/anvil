// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::rabbitmq_controller::model::reconciler::RabbitmqMaker;
use crate::rabbitmq_controller::trusted::{maker::*, spec_types::*, step::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::int_to_string_view;
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::vstatefulset_controller::trusted::liveness_theorem as vsts_liveness_theorem;

use vstd::prelude::*;

use super::rely_guarantee::rmq_rely;
use super::spec_types::RabbitmqClusterView;

verus! {

pub proof fn rmq_esr_holds_per_cr(spec: TempPred<ClusterState>, rmq: RabbitmqClusterView, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        // The cluster always takes an action, and the relevant actions satisfy weak fairness.
        spec.entails(next_with_wf(cluster, controller_id)),
        // The vd type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        // The vrs type is installed in the cluster.
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        // The vd controller runs in the cluster.
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
        // No other controllers interfere with the vd controller.
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] rmq_rely(other_id)))),
    ensures
        spec.entails(rmq_eventually_stable_reconciliation_per_cr(rmq)),
        exists |rv: ResourceVersion| rmq_eventually_stable_cm_rv(spec, rmq, rv)
{
    assume(false);
}

pub open spec fn rmq_composed_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vrs| composed_current_state_matches::<RabbitmqMaker>(vrs))
}

pub open spec fn rmq_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vrs| current_state_matches::<RabbitmqMaker>(vrs))
}

pub open spec fn rmq_eventually_stable_reconciliation_per_cr(rmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation_per_cr(rmq, |rmq| current_state_matches::<RabbitmqMaker>(rmq))
}

pub open spec fn current_state_matches<M: Maker>(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |sub_resource: SubResource| #[trigger] resource_state_matches::<M>(sub_resource, rabbitmq, s)
    }
}

pub open spec fn composed_current_state_matches<M: Maker>(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |sub_resource: SubResource| #[trigger] resource_state_matches::<M>(sub_resource, rabbitmq, s)
        &&& composed_vsts_match::<RabbitmqMaker>(rabbitmq)(s)
    }
}

pub open spec fn resource_state_matches<M: Maker>(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, state: ClusterState) -> bool {
    let resources = state.resources();
    match sub_resource {
        SubResource::HeadlessService => {
            let key = M::make_headless_service_key(rabbitmq);
            let obj = resources[key];
            let made_spec = M::make_headless_service(rabbitmq).spec->0;
            let spec = ServiceView::unmarshal(obj)->Ok_0.spec->0;
            &&& resources.contains_key(key)
            &&& ServiceView::unmarshal(obj) is Ok
            &&& ServiceView::unmarshal(obj)->Ok_0.spec is Some
            &&& made_spec == ServiceSpecView {
                cluster_ip: made_spec.cluster_ip,
                ..spec
            }
            &&& obj.metadata.labels == M::make_headless_service(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == M::make_headless_service(rabbitmq).metadata.annotations
        },
        SubResource::Service => {
            let key = M::make_main_service_key(rabbitmq);
            let obj = resources[key];
            let made_spec = M::make_main_service(rabbitmq).spec->0;
            let spec = ServiceView::unmarshal(obj)->Ok_0.spec->0;
            &&& resources.contains_key(key)
            &&& ServiceView::unmarshal(obj) is Ok
            &&& ServiceView::unmarshal(obj)->Ok_0.spec is Some
            &&& made_spec == ServiceSpecView {
                cluster_ip: made_spec.cluster_ip,
                ..spec
            }
            &&& obj.metadata.labels == M::make_main_service(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == M::make_main_service(rabbitmq).metadata.annotations
        },
        SubResource::ErlangCookieSecret => {
            let key = M::make_erlang_secret_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& SecretView::unmarshal(obj) is Ok
            &&& SecretView::unmarshal(obj)->Ok_0.data == M::make_erlang_secret(rabbitmq).data
            &&& obj.metadata.labels == M::make_erlang_secret(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == M::make_erlang_secret(rabbitmq).metadata.annotations
        },
        SubResource::DefaultUserSecret => {
            let key = M::make_default_user_secret_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& SecretView::unmarshal(obj) is Ok
            &&& SecretView::unmarshal(obj)->Ok_0.data == M::make_default_user_secret(rabbitmq).data
            &&& obj.metadata.labels == M::make_default_user_secret(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == M::make_default_user_secret(rabbitmq).metadata.annotations
        },
        SubResource::PluginsConfigMap => {
            let key = M::make_plugins_config_map_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& ConfigMapView::unmarshal(obj) is Ok
            &&& ConfigMapView::unmarshal(obj)->Ok_0.data == M::make_plugins_config_map(rabbitmq).data
            &&& obj.metadata.labels == M::make_plugins_config_map(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == M::make_plugins_config_map(rabbitmq).metadata.annotations
        },
        SubResource::ServerConfigMap => {
            let key = M::make_server_config_map_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& ConfigMapView::unmarshal(obj) is Ok
            &&& ConfigMapView::unmarshal(obj)->Ok_0.data == M::make_server_config_map(rabbitmq).data
            &&& obj.spec == ConfigMapView::marshal_spec(M::make_server_config_map(rabbitmq).data)
            &&& obj.metadata.labels == M::make_server_config_map(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == M::make_server_config_map(rabbitmq).metadata.annotations
        },
        SubResource::ServiceAccount => {
            let key = M::make_service_account_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& ServiceAccountView::unmarshal(obj) is Ok
            &&& ServiceAccountView::unmarshal(obj)->Ok_0.automount_service_account_token == M::make_service_account(rabbitmq).automount_service_account_token
            &&& obj.metadata.labels == M::make_service_account(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == M::make_service_account(rabbitmq).metadata.annotations
        },
        SubResource::Role => {
            let key = M::make_role_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& RoleView::unmarshal(obj) is Ok
            &&& RoleView::unmarshal(obj)->Ok_0.policy_rules == M::make_role(rabbitmq).policy_rules
            &&& obj.metadata.labels == M::make_role(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == M::make_role(rabbitmq).metadata.annotations
        },
        SubResource::RoleBinding => {
            let key = M::make_role_binding_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& RoleBindingView::unmarshal(obj) is Ok
            &&& RoleBindingView::unmarshal(obj)->Ok_0.role_ref == M::make_role_binding(rabbitmq).role_ref
            &&& RoleBindingView::unmarshal(obj)->Ok_0.subjects == M::make_role_binding(rabbitmq).subjects
            &&& obj.metadata.labels == M::make_role_binding(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == M::make_role_binding(rabbitmq).metadata.annotations
        },
        SubResource::StatefulSet => {
            let key = M::make_stateful_set_key(rabbitmq);
            let obj = resources[key];
            let cm_key = M::make_server_config_map_key(rabbitmq);
            let cm_obj = resources[cm_key];
            let made_sts = M::make_stateful_set(rabbitmq, int_to_string_view(cm_obj.metadata.resource_version->0));
            // hack 
            &&& resources.contains_key(key)
            &&& resources.contains_key(cm_key)
            &&& cm_obj.metadata.resource_version is Some
            &&& VStatefulSetView::unmarshal(obj) is Ok
            &&& obj.metadata.labels == made_sts.metadata.labels
            &&& obj.metadata.annotations == made_sts.metadata.annotations
            &&& Cluster::desired_state_is(made_sts)(state)
        },
    }
}

pub open spec fn rmq_eventually_stable_cm_rv(spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, rv: ResourceVersion) -> bool {
    spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(
        always(lift_state(config_map_rv_match::<RabbitmqMaker>(rabbitmq, rv)))
    ))
}

pub open spec fn config_map_rv_match<M: Maker>(rabbitmq: RabbitmqClusterView, rv: ResourceVersion) -> StatePred<ClusterState> {
    |state: ClusterState| {
        let key = M::make_server_config_map_key(rabbitmq);
        let resources = state.resources();
        let obj = resources[key];
        &&& obj.metadata.resource_version is Some
        &&& obj.metadata.resource_version->0 == rv
    }
}

pub open spec fn composed_vsts_match<M: Maker>(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let resources = s.resources();
        let cm_key = M::make_server_config_map_key(rabbitmq);
        let cm_obj = resources[cm_key];
        let desired_sts = M::make_stateful_set(rabbitmq, int_to_string_view(cm_obj.metadata.resource_version->0));   
        vsts_liveness_theorem::current_state_matches(desired_sts)(s)
    }
}

pub open spec fn next_with_wf(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    always(lift_action(cluster.next()))
    .and(tla_forall(|input| cluster.api_server_next().weak_fairness(input)))
    .and(tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)))
    .and(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))))
    .and(tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))))
    .and(tla_forall(|input| cluster.disable_crash().weak_fairness(input)))
    .and(tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))))
    .and(cluster.disable_crash().weak_fairness(controller_id))
    .and(cluster.disable_req_drop().weak_fairness(()))
    .and(cluster.disable_pod_monkey().weak_fairness(()))
}

}
