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
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::resource::config_map::ServerConfigMapBuilder;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::rabbitmq_controller::spec::types::RabbitmqClusterView;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct PluginsConfigMapBuilder {}

impl ResourceBuilder<RabbitmqCluster, RabbitmqReconcileState, spec_resource::PluginsConfigMapBuilder> for PluginsConfigMapBuilder {
    open spec fn requirements(rabbitmq: RabbitmqClusterView) -> bool {
        &&& rabbitmq.metadata.name.is_Some()
        &&& rabbitmq.metadata.namespace.is_Some()
    }

    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: ConfigMap::api_resource(),
            name: make_plugins_config_map_name(rabbitmq),
            namespace: rabbitmq.metadata().namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_plugins_config_map(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let cm = ConfigMap::unmarshal(obj);
        if cm.is_ok() {
            Ok(update_plugins_config_map(rabbitmq, cm.unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn state_after_create_or_update(obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, ()>) {
        let cm = ConfigMap::unmarshal(obj);
        if cm.is_ok() {
            Ok(state)
        } else {
            Err(())
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
    config_map.set_data(made_config_map.data().unwrap());
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
    rabbitmq.metadata().name().unwrap().concat(new_strlit("-plugins-conf"))
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
        metadata.set_namespace(rabbitmq.metadata().namespace().unwrap());
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
