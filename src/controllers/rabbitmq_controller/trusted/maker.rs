// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::rabbitmq_controller::trusted::spec_types::RabbitmqClusterView;
use crate::vstd_ext::{string_map::*, string_view::*};
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

pub trait Maker {
    uninterp spec fn make_headless_service_key(rabbitmq: RabbitmqClusterView) -> ObjectRef;
    uninterp spec fn make_main_service_key(rabbitmq: RabbitmqClusterView) -> ObjectRef;
    uninterp spec fn make_erlang_secret_key(rabbitmq: RabbitmqClusterView) -> ObjectRef;
    uninterp spec fn make_default_user_secret_key(rabbitmq: RabbitmqClusterView) -> ObjectRef;
    uninterp spec fn make_plugins_config_map_key(rabbitmq: RabbitmqClusterView) -> ObjectRef;
    uninterp spec fn make_server_config_map_key(rabbitmq: RabbitmqClusterView) -> ObjectRef;
    uninterp spec fn make_service_account_key(rabbitmq: RabbitmqClusterView) -> ObjectRef;
    uninterp spec fn make_role_key(rabbitmq: RabbitmqClusterView) -> ObjectRef;
    uninterp spec fn make_role_binding_key(rabbitmq: RabbitmqClusterView) -> ObjectRef;
    uninterp spec fn make_stateful_set_key(rabbitmq: RabbitmqClusterView) -> ObjectRef;

    uninterp spec fn make_headless_service(rabbitmq: RabbitmqClusterView) -> ServiceView;
    uninterp spec fn make_main_service(rabbitmq: RabbitmqClusterView) -> ServiceView;
    uninterp spec fn make_erlang_secret(rabbitmq: RabbitmqClusterView) -> SecretView;
    uninterp spec fn make_default_user_secret(rabbitmq: RabbitmqClusterView) -> SecretView;
    uninterp spec fn make_plugins_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView;
    uninterp spec fn make_server_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView;
    uninterp spec fn make_service_account(rabbitmq: RabbitmqClusterView) -> ServiceAccountView;
    uninterp spec fn make_role(rabbitmq: RabbitmqClusterView) -> RoleView;
    uninterp spec fn make_role_binding(rabbitmq: RabbitmqClusterView) -> RoleBindingView;
    uninterp spec fn make_stateful_set(rabbitmq: RabbitmqClusterView, config_map_rv: StringView) -> StatefulSetView;
}

}
