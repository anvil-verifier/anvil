// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::rabbitmq_controller::model::{reconciler::*, install::rabbitmq_controller_model, resource::*};
use crate::rabbitmq_controller::trusted::{spec_types::*, step::*};
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
}

pub open spec fn rmq_composed_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vrs| composed_current_state_matches(vrs))
}

pub open spec fn rmq_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vrs| current_state_matches(vrs))
}

pub open spec fn rmq_eventually_stable_reconciliation_per_cr(rmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation_per_cr(rmq, |rmq| current_state_matches(rmq))
}

pub open spec fn current_state_matches(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |sub_resource: SubResource| #[trigger] resource_state_matches(sub_resource, rabbitmq)(s)
    }
}

pub open spec fn composed_current_state_matches(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |sub_resource: SubResource| #[trigger] resource_state_matches(sub_resource, rabbitmq)(s)
        &&& composed_vsts_match(rabbitmq)(s)
    }
}

pub open spec fn resource_state_matches(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |state: ClusterState| {
        let resources = state.resources();
        match sub_resource {
            SubResource::HeadlessService => {
                let key = make_headless_service_key(rabbitmq);
                let obj = resources[key];
                let made_spec = make_headless_service(rabbitmq).spec->0;
                let spec = ServiceView::unmarshal(obj)->Ok_0.spec->0;
                &&& resources.contains_key(key)
                &&& ServiceView::unmarshal(obj) is Ok
                &&& ServiceView::unmarshal(obj)->Ok_0.spec is Some
                &&& made_spec.without_cluster_ip() == spec.without_cluster_ip()
                &&& obj.metadata.labels == make_headless_service(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_headless_service(rabbitmq).metadata.annotations
            },
            SubResource::Service => {
                let key = make_main_service_key(rabbitmq);
                let obj = resources[key];
                let made_spec = make_main_service(rabbitmq).spec->0;
                let spec = ServiceView::unmarshal(obj)->Ok_0.spec->0;
                &&& resources.contains_key(key)
                &&& ServiceView::unmarshal(obj) is Ok
                &&& ServiceView::unmarshal(obj)->Ok_0.spec is Some
                &&& made_spec.without_cluster_ip() == spec.without_cluster_ip()
                &&& obj.metadata.labels == make_main_service(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_main_service(rabbitmq).metadata.annotations
            },
            SubResource::ErlangCookieSecret => {
                let key = make_erlang_secret_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& SecretView::unmarshal(obj) is Ok
                &&& SecretView::unmarshal(obj)->Ok_0.data == make_erlang_secret(rabbitmq).data
                &&& obj.metadata.labels == make_erlang_secret(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_erlang_secret(rabbitmq).metadata.annotations
            },
            SubResource::DefaultUserSecret => {
                let key = make_default_user_secret_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& SecretView::unmarshal(obj) is Ok
                &&& SecretView::unmarshal(obj)->Ok_0.data == make_default_user_secret(rabbitmq).data
                &&& obj.metadata.labels == make_default_user_secret(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_default_user_secret(rabbitmq).metadata.annotations
            },
            SubResource::PluginsConfigMap => {
                let key = make_plugins_config_map_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& ConfigMapView::unmarshal(obj) is Ok
                &&& ConfigMapView::unmarshal(obj)->Ok_0.data == make_plugins_config_map(rabbitmq).data
                &&& obj.metadata.labels == make_plugins_config_map(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_plugins_config_map(rabbitmq).metadata.annotations
            },
            SubResource::ServerConfigMap => {
                let key = make_server_config_map_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& ConfigMapView::unmarshal(obj) is Ok
                &&& ConfigMapView::unmarshal(obj)->Ok_0.data == make_server_config_map(rabbitmq).data
                &&& obj.metadata.labels == make_server_config_map(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_server_config_map(rabbitmq).metadata.annotations
            },
            SubResource::ServiceAccount => {
                let key = make_service_account_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& ServiceAccountView::unmarshal(obj) is Ok
                &&& ServiceAccountView::unmarshal(obj)->Ok_0.automount_service_account_token == make_service_account(rabbitmq).automount_service_account_token
                &&& obj.metadata.labels == make_service_account(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_service_account(rabbitmq).metadata.annotations
            },
            SubResource::Role => {
                let key = make_role_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& RoleView::unmarshal(obj) is Ok
                &&& RoleView::unmarshal(obj)->Ok_0.policy_rules == make_role(rabbitmq).policy_rules
                &&& obj.metadata.labels == make_role(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_role(rabbitmq).metadata.annotations
            },
            SubResource::RoleBinding => {
                let key = make_role_binding_key(rabbitmq);
                let obj = resources[key];
                &&& resources.contains_key(key)
                &&& RoleBindingView::unmarshal(obj) is Ok
                &&& RoleBindingView::unmarshal(obj)->Ok_0.role_ref == make_role_binding(rabbitmq).role_ref
                &&& RoleBindingView::unmarshal(obj)->Ok_0.subjects == make_role_binding(rabbitmq).subjects
                &&& obj.metadata.labels == make_role_binding(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_role_binding(rabbitmq).metadata.annotations
            },
            SubResource::VStatefulSetView => {
                let key = make_stateful_set_key(rabbitmq);
                let obj = resources[key];
                let cm_key = make_server_config_map_key(rabbitmq);
                let cm_obj = resources[cm_key];
                let made_sts = make_stateful_set(rabbitmq, int_to_string_view(cm_obj.metadata.resource_version->0));
                let etcd_sts = VStatefulSetView::unmarshal(obj)->Ok_0;
                &&& resources.contains_key(key)
                &&& resources.contains_key(cm_key)
                &&& cm_obj.metadata.resource_version is Some
                &&& VStatefulSetView::unmarshal(obj) is Ok
                &&& obj.metadata.labels == made_sts.metadata.labels
                &&& obj.metadata.annotations == made_sts.metadata.annotations
                &&& obj.metadata.deletion_timestamp is None
                &&& etcd_sts.spec.replicas == Some(rabbitmq.spec.replicas)
                &&& etcd_sts.spec.template == made_sts.spec.template
                &&& etcd_sts.spec.persistent_volume_claim_retention_policy == rabbitmq.spec.persistent_volume_claim_retention_policy
                &&& Cluster::desired_state_is(etcd_sts)(state)
            },
        }
    }
}

pub open spec fn rmq_eventually_stable_cm_rv(spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView, rv: ResourceVersion) -> bool {
    spec.entails(always(lift_state(Cluster::desired_state_is(rabbitmq))).leads_to(
        always(lift_state(config_map_rv_match(rabbitmq, rv)))
    ))
}

pub open spec fn config_map_rv_match(rabbitmq: RabbitmqClusterView, rv: ResourceVersion) -> StatePred<ClusterState> {
    |state: ClusterState| {
        let key = make_server_config_map_key(rabbitmq);
        let resources = state.resources();
        let obj = resources[key];
        &&& obj.metadata.resource_version is Some
        &&& obj.metadata.resource_version->0 == rv
    }
}

pub open spec fn composed_vsts_match(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let resources = s.resources();
        let cm_key = make_server_config_map_key(rabbitmq);
        let cm_obj = resources[cm_key];
        let desired_sts = make_stateful_set(rabbitmq, int_to_string_view(cm_obj.metadata.resource_version->0));   
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
