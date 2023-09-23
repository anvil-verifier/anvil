// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::resource::ServiceAccountBuilder;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ServerConfigMapBuilder {}

impl ResourceBuilder<ConfigMapView> for ServerConfigMapBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_server_config_map_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, RabbitmqError> {
        Ok(make_server_config_map(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, found_resource: ConfigMapView) -> Result<DynamicObjectView, RabbitmqError> {
        Ok(update_server_config_map(rabbitmq, found_resource).marshal())
    }

    open spec fn get_result_check(obj: DynamicObjectView) -> Result<ConfigMapView, RabbitmqError> {
        let sts = ConfigMapView::unmarshal(obj);
        if sts.is_ok() {
            Ok(sts.get_Ok_0())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    open spec fn state_after_create_or_update(obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, RabbitmqError>) {
        let cm = ConfigMapView::unmarshal(obj);
        if cm.is_ok() && cm.get_Ok_0().metadata.resource_version.is_Some() {
            Ok(RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, ResourceKind::ServiceAccount),
                latest_config_map_rv_opt: Some(int_to_string_view(cm.get_Ok_0().metadata.resource_version.get_Some_0())),
                ..state
            })
        } else {
            Err(RabbitmqError::Error)
        }
    }
}

pub open spec fn update_server_config_map(rabbitmq: RabbitmqClusterView, found_config_map: ConfigMapView) -> ConfigMapView {
    ConfigMapView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: make_server_config_map(rabbitmq).metadata.labels,
            annotations: make_server_config_map(rabbitmq).metadata.annotations,
            ..found_config_map.metadata
        },
        data: Some({
            let old_data = if found_config_map.data.is_Some() { found_config_map.data.get_Some_0() } else { Map::empty() };
            old_data.union_prefer_right(make_server_config_map(rabbitmq).data.get_Some_0())
        }),
        ..found_config_map
    }
}

pub open spec fn make_server_config_map_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-server-conf")@
}

pub open spec fn make_server_config_map_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: ConfigMapView::kind(),
        name: make_server_config_map_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn make_server_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ConfigMapView {
        metadata: ObjectMetaView {
            name: Some(make_server_config_map_name(rabbitmq)),
            namespace: rabbitmq.metadata.namespace,
            owner_references: Some(make_owner_references(rabbitmq)),
            labels: Some(make_labels(rabbitmq)),
            annotations: Some(rabbitmq.spec.annotations),
            ..ObjectMetaView::default()
        },
        data: Some({
            let data = Map::empty()
                        .insert(new_strlit("operatorDefaults.conf")@, default_rbmq_config(rabbitmq))
                        .insert(new_strlit("userDefinedConfiguration.conf")@,
                        {
                            if rabbitmq.spec.rabbitmq_config.is_Some()
                            && rabbitmq.spec.rabbitmq_config.get_Some_0().additional_config.is_Some()
                            {   // check if there are rabbitmq-related customized configurations
                                new_strlit("total_memory_available_override_value = 1717986919\n")@ + rabbitmq.spec.rabbitmq_config.get_Some_0().additional_config.get_Some_0()
                            } else {
                                new_strlit("total_memory_available_override_value = 1717986919\n")@
                            }
                        });
            if rabbitmq.spec.rabbitmq_config.is_Some() && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.is_Some()
            && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.get_Some_0() != new_strlit("")@
            && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.is_Some()
            && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.get_Some_0() != new_strlit("")@ {
                data.insert(new_strlit("advanced.config")@, rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.get_Some_0())
                    .insert(new_strlit("rabbitmq-env.conf")@, rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.get_Some_0())
            } else if rabbitmq.spec.rabbitmq_config.is_Some() && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.is_Some()
            && rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.get_Some_0() != new_strlit("")@ {
                data.insert(new_strlit("advanced.config")@, rabbitmq.spec.rabbitmq_config.get_Some_0().advanced_config.get_Some_0())
            } else if rabbitmq.spec.rabbitmq_config.is_Some() && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.is_Some()
            && rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.get_Some_0() != new_strlit("")@ {
                data.insert(new_strlit("rabbitmq-env.conf")@, rabbitmq.spec.rabbitmq_config.get_Some_0().env_config.get_Some_0())
            } else {
                data
            }
        }),
        ..ConfigMapView::default()
    }
}

pub open spec fn default_rbmq_config(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let name = rabbitmq.metadata.name.get_Some_0();

    new_strlit(
        "queue_master_locator = min-masters\n\
        disk_free_limit.absolute = 2GB\n\
        cluster_partition_handling = pause_minority\n\
        cluster_formation.peer_discovery_backend = rabbit_peer_discovery_k8s\n\
        cluster_formation.k8s.host = kubernetes.default\n\
        cluster_formation.k8s.address_type = hostname\n"
    )@ + new_strlit("cluster_formation.target_cluster_size_hint = ")@ + int_to_string_view(rabbitmq.spec.replicas) + new_strlit("\n")@
    + new_strlit("cluster_name = ")@ + name + new_strlit("\n")@
}

}
