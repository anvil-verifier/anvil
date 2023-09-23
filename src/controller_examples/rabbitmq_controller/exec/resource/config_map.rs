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
use crate::rabbitmq_controller::exec::resource::service_account::*;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::reconciler::exec::{io::*, reconciler::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct ServerConfigMapBuilder {}

impl ResourceBuilder<ConfigMap, spec_resource::ServerConfigMapBuilder> for ServerConfigMapBuilder {
    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: ConfigMap::api_resource(),
            name: make_server_config_map_name(rabbitmq),
            namespace: rabbitmq.namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, RabbitmqError> {
        Ok(make_server_config_map(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, RabbitmqError> {
        let cm = ConfigMap::unmarshal(obj);
        if cm.is_ok() {
            Ok(update_server_config_map(rabbitmq, cm.unwrap()).marshal())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    fn state_after_create_or_update(obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
        let cm = ConfigMap::unmarshal(obj);
        if cm.is_ok() && cm.as_ref().unwrap().metadata().resource_version().is_some() {
            Ok(RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, ResourceKind::ServiceAccount),
                latest_config_map_rv_opt: Some(cm.unwrap().metadata().resource_version().unwrap()),
                ..state
            })
        } else {
            Err(RabbitmqError::Error)
        }
    }
}

pub fn update_server_config_map(rabbitmq: &RabbitmqCluster, found_config_map: ConfigMap) -> (config_map: ConfigMap)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        config_map@ == spec_resource::update_server_config_map(rabbitmq@, found_config_map@),
{
    let mut config_map = found_config_map.clone();
    let made_server_cm = make_server_config_map(rabbitmq);

    config_map.set_data({
        let old_data_opt = found_config_map.data();
        let mut old_data = if old_data_opt.is_some() { old_data_opt.unwrap() } else { StringMap::empty() };
        old_data.extend(made_server_cm.data().unwrap());
        old_data
    });
    config_map.set_metadata({
        let mut metadata = found_config_map.metadata();
        // The reason why we add these two operations is that it makes the proof easier.
        // In this way, we can easily show that what the owner references and finalizers of the object in every update request
        // for stateful set are.
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_server_cm.metadata().labels().unwrap());
        metadata.set_annotations(made_server_cm.metadata().annotations().unwrap());
        metadata
    });
    config_map
}

pub fn make_server_config_map_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        name@ == spec_resource::make_server_config_map_name(rabbitmq@),
{
    rabbitmq.name().unwrap().concat(new_strlit("-server-conf"))
}

pub fn make_server_config_map(rabbitmq: &RabbitmqCluster) -> (config_map: ConfigMap)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        config_map@ == spec_resource::make_server_config_map(rabbitmq@),
{
    let mut config_map = ConfigMap::default();
    config_map.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_server_config_map_name(rabbitmq));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    let mut data = StringMap::empty();
    data.insert(new_strlit("operatorDefaults.conf").to_string(),
                default_rbmq_config(rabbitmq));
    data.insert(new_strlit("userDefinedConfiguration.conf").to_string(), {
        let mut rmq_conf_buff = new_strlit("total_memory_available_override_value = 1717986919\n").to_string(); // default value
        if rabbitmq.spec().rabbitmq_config().is_some() {
            // check if there are rabbitmq-related customized configurations
            let rabbitmq_config = rabbitmq.spec().rabbitmq_config().unwrap();
            if rabbitmq_config.additional_config().is_some(){
                rmq_conf_buff.append(rabbitmq_config.additional_config().unwrap().as_str());
            }
        }
        rmq_conf_buff
    });
    if rabbitmq.spec().rabbitmq_config().is_some() && rabbitmq.spec().rabbitmq_config().unwrap().advanced_config().is_some()
    && !rabbitmq.spec().rabbitmq_config().unwrap().advanced_config().unwrap().eq(&new_strlit("").to_string()) {
        data.insert(new_strlit("advanced.config").to_string(), rabbitmq.spec().rabbitmq_config().unwrap().advanced_config().unwrap());
    }
    if rabbitmq.spec().rabbitmq_config().is_some() && rabbitmq.spec().rabbitmq_config().unwrap().env_config().is_some()
    && !rabbitmq.spec().rabbitmq_config().unwrap().env_config().unwrap().eq(&new_strlit("").to_string()) {
        data.insert(new_strlit("rabbitmq-env.conf").to_string(), rabbitmq.spec().rabbitmq_config().unwrap().env_config().unwrap());
    }
    config_map.set_data(data);
    config_map
}

pub fn default_rbmq_config(rabbitmq: &RabbitmqCluster) -> (s: String)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        s@ == spec_resource::default_rbmq_config(rabbitmq@),
{
    new_strlit(
        "queue_master_locator = min-masters\n\
        disk_free_limit.absolute = 2GB\n\
        cluster_partition_handling = pause_minority\n\
        cluster_formation.peer_discovery_backend = rabbit_peer_discovery_k8s\n\
        cluster_formation.k8s.host = kubernetes.default\n\
        cluster_formation.k8s.address_type = hostname\n"
    ).to_string()
    .concat(new_strlit("cluster_formation.target_cluster_size_hint = "))
    .concat(i32_to_string(rabbitmq.spec().replicas()).as_str())
    .concat(new_strlit("\n"))
    .concat(new_strlit("cluster_name = "))
    .concat(rabbitmq.name().unwrap().as_str())
    .concat(new_strlit("\n"))
}

}
