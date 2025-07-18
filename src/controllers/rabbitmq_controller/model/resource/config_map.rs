// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::model::resource::ServiceAccountBuilder;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::{map_lib::*, string_view::*};
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ServerConfigMapBuilder {}

impl ResourceBuilder<RabbitmqClusterView, RabbitmqReconcileState> for ServerConfigMapBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_server_config_map_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_server_config_map(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let cm = ConfigMapView::unmarshal(obj);
        if cm.is_ok() {
            Ok(update_server_config_map(rabbitmq, cm->Ok_0).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let cm = ConfigMapView::unmarshal(obj);
        if cm.is_ok() && cm->Ok_0.metadata.resource_version is Some {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ServiceAccount),
                latest_config_map_rv_opt: Some(int_to_string_view(cm->Ok_0.metadata.resource_version->0)),
                ..state
            };
            let req = APIRequest::GetRequest(ServiceAccountBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let cm = ConfigMapView::unmarshal(obj);
        if cm.is_ok() && cm->Ok_0.metadata.resource_version is Some {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ServiceAccount),
                latest_config_map_rv_opt: Some(int_to_string_view(cm->Ok_0.metadata.resource_version->0)),
                ..state
            };
            let req = APIRequest::GetRequest(ServiceAccountBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
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
        data: make_server_config_map(rabbitmq).data,
        ..found_config_map
    }
}

pub open spec fn make_server_config_map_name(rabbitmq: RabbitmqClusterView) -> StringView { rabbitmq.metadata.name->0 + "-server-conf"@ }

pub open spec fn make_server_config_map_key(rabbitmq: RabbitmqClusterView) -> ObjectRef {
    ObjectRef {
        kind: ConfigMapView::kind(),
        name: make_server_config_map_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace->0,
    }
}

pub open spec fn make_server_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView {
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
                        .insert("operatorDefaults.conf"@, default_rbmq_config(rabbitmq))
                        .insert("userDefinedConfiguration.conf"@,
                        {
                            if rabbitmq.spec.rabbitmq_config is Some
                            && rabbitmq.spec.rabbitmq_config->0.additional_config is Some
                            {   // check if there are rabbitmq-related customized configurations
                                "total_memory_available_override_value = 1717986919\n"@ + rabbitmq.spec.rabbitmq_config->0.additional_config->0
                            } else {
                                "total_memory_available_override_value = 1717986919\n"@
                            }
                        });
            if rabbitmq.spec.rabbitmq_config is Some && rabbitmq.spec.rabbitmq_config->0.advanced_config is Some
            && rabbitmq.spec.rabbitmq_config->0.advanced_config->0 != ""@
            && rabbitmq.spec.rabbitmq_config->0.env_config is Some
            && rabbitmq.spec.rabbitmq_config->0.env_config->0 != ""@ {
                data.insert("advanced.config"@, rabbitmq.spec.rabbitmq_config->0.advanced_config->0)
                    .insert("rabbitmq-env.conf"@, rabbitmq.spec.rabbitmq_config->0.env_config->0)
            } else if rabbitmq.spec.rabbitmq_config is Some && rabbitmq.spec.rabbitmq_config->0.advanced_config is Some
            && rabbitmq.spec.rabbitmq_config->0.advanced_config->0 != ""@ {
                data.insert("advanced.config"@, rabbitmq.spec.rabbitmq_config->0.advanced_config->0)
            } else if rabbitmq.spec.rabbitmq_config is Some && rabbitmq.spec.rabbitmq_config->0.env_config is Some
            && rabbitmq.spec.rabbitmq_config->0.env_config->0 != ""@ {
                data.insert("rabbitmq-env.conf"@, rabbitmq.spec.rabbitmq_config->0.env_config->0)
            } else {
                data
            }
        }),
        ..ConfigMapView::default()
    }
}

pub open spec fn default_rbmq_config(rabbitmq: RabbitmqClusterView) -> StringView {
    let name = rabbitmq.metadata.name->0;

    "queue_master_locator = min-masters\n\
    disk_free_limit.absolute = 2GB\n\
    cluster_partition_handling = pause_minority\n\
    cluster_formation.peer_discovery_backend = rabbit_peer_discovery_k8s\n\
    cluster_formation.k8s.host = kubernetes.default\n\
    cluster_formation.k8s.address_type = hostname\n"@
    + "cluster_formation.target_cluster_size_hint = "@ + int_to_string_view(rabbitmq.spec.replicas) + "\n"@
    + "cluster_name = "@ + name + "\n"@
}

}
