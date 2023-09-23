// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::resource::config_map::ServerConfigMapBuilder;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::reconciler::exec::{io::*, reconciler::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct PluginsConfigMapBuilder {}

impl ResourceBuilder<ConfigMap, spec_resource::PluginsConfigMapBuilder> for PluginsConfigMapBuilder {
    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: ConfigMap::api_resource(),
            name: make_plugins_config_map_name(rabbitmq),
            namespace: rabbitmq.namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, RabbitmqError> {
        Ok(make_plugins_config_map(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, RabbitmqError> {
        let cm = ConfigMap::unmarshal(obj);
        if cm.is_ok() {
            Ok(update_plugins_config_map(rabbitmq, cm.unwrap()).marshal())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    fn state_after_create_or_update(obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
        let cm = ConfigMap::unmarshal(obj);
        if cm.is_ok() {
            Ok(RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, ResourceKind::ServerConfigMap),
                ..state
            })
        } else {
            Err(RabbitmqError::Error)
        }
    }
}

pub fn update_plugins_config_map(rabbitmq: &RabbitmqCluster, found_config_map: ConfigMap) -> (config_map: ConfigMap)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        config_map@ == spec_resource::update_plugins_config_map(rabbitmq@, found_config_map@),
{
    let mut config_map = found_config_map.clone();
    let made_config_map = make_plugins_config_map(rabbitmq);
    config_map.set_data({
        let mut data = if found_config_map.data().is_some() { found_config_map.data().unwrap() } else { StringMap::empty() };
        data.insert(new_strlit("enabled_plugins").to_string(),
                new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management].").to_string());
        data
    });
    config_map.set_metadata({
        let mut metadata = found_config_map.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_config_map.metadata().labels().unwrap());
        metadata.set_annotations(made_config_map.metadata().annotations().unwrap());
        metadata
    });
    config_map
}

pub fn make_plugins_config_map_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        name@ == spec_resource::make_plugins_config_map_name(rabbitmq@),
{
    rabbitmq.name().unwrap().concat(new_strlit("-plugins-conf"))
}

pub fn make_plugins_config_map(rabbitmq: &RabbitmqCluster) -> (config_map: ConfigMap)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        config_map@ == spec_resource::make_plugins_config_map(rabbitmq@),
{
    let mut config_map = ConfigMap::default();
    config_map.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_plugins_config_map_name(rabbitmq));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    let mut data = StringMap::empty();
    data.insert(new_strlit("enabled_plugins").to_string(),
                new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management].").to_string());
    config_map.set_data(data);
    config_map
}

}
