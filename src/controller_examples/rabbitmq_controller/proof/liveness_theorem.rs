// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::prelude::*;
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    spec::{reconciler::*, resource::*, types::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::string_view::int_to_string_view;
use vstd::prelude::*;

verus! {

pub open spec fn liveness_theorem() -> bool {
    forall |rabbitmq: RabbitmqClusterView| #[trigger] cluster_spec().entails(liveness(rabbitmq))
}

pub open spec fn cluster_spec() -> TempPred<RMQCluster> {
    RMQCluster::sm_spec()
}

pub open spec fn liveness(rabbitmq: RabbitmqClusterView) -> TempPred<RMQCluster> {
    always(lift_state(desired_state_is(rabbitmq))).leads_to(always(lift_state(current_state_matches(rabbitmq))))
}

pub open spec fn desired_state_is(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    RMQCluster::desired_state_is(rabbitmq)
}

pub open spec fn current_state_matches(rabbitmq: RabbitmqClusterView) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        forall |sub_resource: SubResource|
            #[trigger] resource_state_matches(sub_resource, rabbitmq, s.resources())
    }
}

pub open spec fn resource_state_matches(sub_resource: SubResource, rabbitmq: RabbitmqClusterView, resources: StoredState) -> bool {
    match sub_resource {
        SubResource::HeadlessService => {
            let key = make_headless_service_key(rabbitmq);
            let obj = resources[key];
            let made_spec = make_headless_service(rabbitmq).spec.get_Some_0();
            let spec = ServiceView::unmarshal(obj).get_Ok_0().spec.get_Some_0();
            &&& resources.contains_key(key)
            &&& ServiceView::unmarshal(obj).is_Ok()
            &&& ServiceView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& made_spec == ServiceSpecView {
                cluster_ip: made_spec.cluster_ip,
                ..spec
            }
            &&& obj.metadata.labels == make_headless_service(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == make_headless_service(rabbitmq).metadata.annotations
        },
        SubResource::Service => {
            let key = make_main_service_key(rabbitmq);
            let obj = resources[key];
            let made_spec = make_main_service(rabbitmq).spec.get_Some_0();
            let spec = ServiceView::unmarshal(obj).get_Ok_0().spec.get_Some_0();
            &&& resources.contains_key(key)
            &&& ServiceView::unmarshal(obj).is_Ok()
            &&& ServiceView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& made_spec == ServiceSpecView {
                cluster_ip: made_spec.cluster_ip,
                ..spec
            }
            &&& obj.metadata.labels == make_main_service(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == make_main_service(rabbitmq).metadata.annotations
        },
        SubResource::ErlangCookieSecret => {
            let key = make_erlang_secret_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& SecretView::unmarshal(obj).is_Ok()
            &&& SecretView::unmarshal(obj).get_Ok_0().data == make_erlang_secret(rabbitmq).data
            &&& obj.metadata.labels == make_erlang_secret(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == make_erlang_secret(rabbitmq).metadata.annotations
        },
        SubResource::DefaultUserSecret => {
            let key = make_default_user_secret_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& SecretView::unmarshal(obj).is_Ok()
            &&& SecretView::unmarshal(obj).get_Ok_0().data == make_default_user_secret(rabbitmq).data
            &&& obj.metadata.labels == make_default_user_secret(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == make_default_user_secret(rabbitmq).metadata.annotations
        },
        SubResource::PluginsConfigMap => {
            let key = make_plugins_config_map_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& ConfigMapView::unmarshal(obj).is_Ok()
            &&& ConfigMapView::unmarshal(obj).get_Ok_0().data == make_plugins_config_map(rabbitmq).data
            &&& obj.metadata.labels == make_plugins_config_map(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == make_plugins_config_map(rabbitmq).metadata.annotations
        },
        SubResource::ServerConfigMap => {
            let key = make_server_config_map_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& ConfigMapView::unmarshal(obj).is_Ok()
            &&& ConfigMapView::unmarshal(obj).get_Ok_0().data == make_server_config_map(rabbitmq).data
            &&& obj.spec == ConfigMapView::marshal_spec((make_server_config_map(rabbitmq).data, ()))
            &&& obj.metadata.labels == make_server_config_map(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == make_server_config_map(rabbitmq).metadata.annotations
        },
        SubResource::ServiceAccount => {
            let key = make_service_account_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& ServiceAccountView::unmarshal(obj).is_Ok()
            &&& ServiceAccountView::unmarshal(obj).get_Ok_0().automount_service_account_token == make_service_account(rabbitmq).automount_service_account_token
            &&& obj.metadata.labels == make_service_account(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == make_service_account(rabbitmq).metadata.annotations
        },
        SubResource::Role => {
            let key = make_role_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& RoleView::unmarshal(obj).is_Ok()
            &&& RoleView::unmarshal(obj).get_Ok_0().policy_rules == make_role(rabbitmq).policy_rules
            &&& obj.metadata.labels == make_role(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == make_role(rabbitmq).metadata.annotations
        },
        SubResource::RoleBinding => {
            let key = make_role_binding_key(rabbitmq);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& RoleBindingView::unmarshal(obj).is_Ok()
            &&& RoleBindingView::unmarshal(obj).get_Ok_0().role_ref == make_role_binding(rabbitmq).role_ref
            &&& RoleBindingView::unmarshal(obj).get_Ok_0().subjects == make_role_binding(rabbitmq).subjects
            &&& obj.metadata.labels == make_role_binding(rabbitmq).metadata.labels
            &&& obj.metadata.annotations == make_role_binding(rabbitmq).metadata.annotations
        },
        SubResource::StatefulSet => {
            let key = make_stateful_set_key(rabbitmq);
            let obj = resources[key];
            let cm_key = make_server_config_map_key(rabbitmq);
            let cm_obj = resources[cm_key];
            let made_sts = make_stateful_set(rabbitmq, int_to_string_view(cm_obj.metadata.resource_version.get_Some_0()));
            &&& resources.contains_key(key)
            &&& resources.contains_key(cm_key)
            &&& cm_obj.metadata.resource_version.is_Some()
            &&& StatefulSetView::unmarshal(obj).is_Ok()
            &&& StatefulSetView::unmarshal(obj).get_Ok_0().spec == made_sts.spec
            &&& obj.metadata.labels == made_sts.metadata.labels
            &&& obj.metadata.annotations == made_sts.metadata.annotations
        },
    }
}

}
