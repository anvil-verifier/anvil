// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::{
    container::*, volume::*, resource_requirements::*,
};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::rabbitmq_controller::model::{reconciler::*, install::*, resource::*};
use crate::rabbitmq_controller::trusted::{spec_types::*, step::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::vstatefulset_controller::trusted::liveness_theorem as vsts_liveness_theorem;

use vstd::prelude::*;

use super::rely_guarantee::*;
use super::spec_types::RabbitmqClusterView;

verus! {

pub open spec fn rmq_composed_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vrs| composed_current_state_matches(vrs))
}

pub open spec fn rmq_eventually_stable_reconciliation() -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation(|vrs| current_state_matches(vrs))
}

pub open spec fn rmq_eventually_stable_reconciliation_per_cr(rabbitmq: RabbitmqClusterView) -> TempPred<ClusterState> {
    Cluster::eventually_stable_reconciliation_per_cr(rabbitmq, |rabbitmq| current_state_matches(rabbitmq))
}

pub open spec fn current_state_matches(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |sub_resource: SubResource| #[trigger] resource_state_matches(sub_resource, rabbitmq)(s)
    }
}

pub open spec fn composed_current_state_matches(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |ord: nat| ord < rabbitmq.spec.replicas ==> {
            let key = ObjectRef {
                kind: Kind::PodKind,
                name: #[trigger] vsts_liveness_theorem::pod_name(make_stateful_set_name(rabbitmq), ord),
                namespace: rabbitmq.metadata.namespace->0
            };
            let obj = s.resources()[key];
            &&& s.resources().contains_key(key)
            // spec is updated
            &&& PodView::unmarshal(obj) is Ok
            &&& pod_spec_matches_rmq(rabbitmq, PodView::unmarshal(obj)->Ok_0)
        }
    }
}

pub open spec fn pod_spec_matches_rmq(rabbitmq: RabbitmqClusterView, pod: PodView) -> bool {
    // TODO: define pod spec matching for composed RMQ liveness
    // Needs to compare pod spec against the VSTS template spec derived from rabbitmq
    &&& pod.spec is Some
    &&& pod.spec->0.without_volumes().without_hostname().without_subdomain()
        == make_rabbitmq_pod_spec(rabbitmq).without_volumes().without_hostname().without_subdomain()
}

pub open spec fn resource_state_matches(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let resource_key = match sub_resource {
            SubResource::HeadlessService => make_headless_service_key(rabbitmq),
            SubResource::Service => make_main_service_key(rabbitmq),
            SubResource::ErlangCookieSecret => make_erlang_secret_key(rabbitmq),
            SubResource::DefaultUserSecret => make_default_user_secret_key(rabbitmq),
            SubResource::PluginsConfigMap => make_plugins_config_map_key(rabbitmq),
            SubResource::ServerConfigMap => make_server_config_map_key(rabbitmq),
            SubResource::ServiceAccount => make_service_account_key(rabbitmq),
            SubResource::Role => make_role_key(rabbitmq),
            SubResource::RoleBinding => make_role_binding_key(rabbitmq),
            SubResource::VStatefulSetView => make_stateful_set_key(rabbitmq),
        };
        let obj = s.resources()[resource_key];
        &&& s.resources().contains_key(resource_key)
        &&& obj.metadata.owner_references == Some(make_owner_references(rabbitmq))
        &&& obj.metadata.finalizers is None
        &&& obj.metadata.deletion_timestamp is None
        &&& match sub_resource {
            SubResource::HeadlessService => {
                let made_spec = make_headless_service(rabbitmq).spec->0;
                let spec = ServiceView::unmarshal(obj)->Ok_0.spec->0;
                &&& ServiceView::unmarshal(obj) is Ok
                &&& ServiceView::unmarshal(obj)->Ok_0.spec is Some
                &&& made_spec.without_cluster_ip() == spec.without_cluster_ip()
                &&& obj.metadata.labels == make_headless_service(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_headless_service(rabbitmq).metadata.annotations
            },
            SubResource::Service => {
                let made_spec = make_main_service(rabbitmq).spec->0;
                let spec = ServiceView::unmarshal(obj)->Ok_0.spec->0;
                &&& ServiceView::unmarshal(obj) is Ok
                &&& ServiceView::unmarshal(obj)->Ok_0.spec is Some
                &&& made_spec.without_cluster_ip() == spec.without_cluster_ip()
                &&& obj.metadata.labels == make_main_service(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_main_service(rabbitmq).metadata.annotations
            },
            SubResource::ErlangCookieSecret => {
                &&& SecretView::unmarshal(obj) is Ok
                &&& obj.metadata.labels == make_erlang_secret(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_erlang_secret(rabbitmq).metadata.annotations
            },
            SubResource::DefaultUserSecret => {
                &&& SecretView::unmarshal(obj) is Ok
                &&& SecretView::unmarshal(obj)->Ok_0.data == make_default_user_secret(rabbitmq).data
                &&& obj.metadata.labels == make_default_user_secret(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_default_user_secret(rabbitmq).metadata.annotations
            },
            SubResource::PluginsConfigMap => {
                &&& ConfigMapView::unmarshal(obj) is Ok
                &&& ConfigMapView::unmarshal(obj)->Ok_0.data == make_plugins_config_map(rabbitmq).data
                &&& obj.metadata.labels == make_plugins_config_map(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_plugins_config_map(rabbitmq).metadata.annotations
            },
            SubResource::ServerConfigMap => {
                &&& ConfigMapView::unmarshal(obj) is Ok
                &&& ConfigMapView::unmarshal(obj)->Ok_0.data == make_server_config_map(rabbitmq).data
                &&& obj.spec == ConfigMapView::marshal_spec(make_server_config_map(rabbitmq).data)
                &&& obj.metadata.labels == make_server_config_map(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_server_config_map(rabbitmq).metadata.annotations
            },
            SubResource::ServiceAccount => {
                &&& ServiceAccountView::unmarshal(obj) is Ok
                &&& obj.metadata.labels == make_service_account(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_service_account(rabbitmq).metadata.annotations
            },
            SubResource::Role => {
                &&& RoleView::unmarshal(obj) is Ok
                &&& RoleView::unmarshal(obj)->Ok_0.policy_rules == make_role(rabbitmq).policy_rules
                &&& obj.metadata.labels == make_role(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_role(rabbitmq).metadata.annotations
            },
            SubResource::RoleBinding => {
                &&& RoleBindingView::unmarshal(obj) is Ok
                &&& RoleBindingView::unmarshal(obj)->Ok_0.subjects == make_role_binding(rabbitmq).subjects
                &&& obj.metadata.labels == make_role_binding(rabbitmq).metadata.labels
                &&& obj.metadata.annotations == make_role_binding(rabbitmq).metadata.annotations
            },
            SubResource::VStatefulSetView => {
                let cm_key = make_server_config_map_key(rabbitmq);
                let cm_obj = s.resources()[cm_key];
                let made_sts = make_stateful_set(rabbitmq, int_to_string_view(cm_obj.metadata.resource_version->0));
                let etcd_sts = VStatefulSetView::unmarshal(obj)->Ok_0;
                &&& s.resources().contains_key(cm_key)
                &&& cm_obj.metadata.resource_version is Some
                &&& VStatefulSetView::unmarshal(obj) is Ok
                &&& obj.metadata.labels == made_sts.metadata.labels
                &&& obj.metadata.annotations == made_sts.metadata.annotations
                &&& etcd_sts.spec.replicas == Some(rabbitmq.spec.replicas)
                &&& etcd_sts.spec.template == made_sts.spec.template
                &&& etcd_sts.spec.persistent_volume_claim_retention_policy == rabbitmq.spec.persistent_volume_claim_retention_policy
                &&& Cluster::desired_state_is(etcd_sts)(s)
            },
        }
    }
}

}
