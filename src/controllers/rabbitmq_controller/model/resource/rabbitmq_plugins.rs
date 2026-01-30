// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::model::resource::config_map::ServerConfigMapBuilder;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct PluginsConfigMapBuilder {}

impl ResourceBuilder<RabbitmqClusterView, RabbitmqReconcileState> for PluginsConfigMapBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_plugins_config_map_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_plugins_config_map(rabbitmq).marshal())
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let cm = ConfigMapView::unmarshal(obj);
        if cm is Ok {
            Ok(update_plugins_config_map(rabbitmq, cm->Ok_0).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let cm = ConfigMapView::unmarshal(obj);
        if cm is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ServerConfigMap),
                ..state
            };
            let req = APIRequest::GetRequest(ServerConfigMapBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let cm = ConfigMapView::unmarshal(obj);
        if cm is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::ServerConfigMap),
                ..state
            };
            let req = APIRequest::GetRequest(ServerConfigMapBuilder::get_request(rabbitmq));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_plugins_config_map_name(rabbitmq: RabbitmqClusterView) -> StringView { rabbitmq.metadata.name->0 + "-plugins-conf"@ }

pub open spec fn make_plugins_config_map_key(rabbitmq: RabbitmqClusterView) -> ObjectRef {
    ObjectRef {
        kind: ConfigMapView::kind(),
        name: make_plugins_config_map_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace->0,
    }
}

pub open spec fn update_plugins_config_map(rabbitmq: RabbitmqClusterView, found_config_map: ConfigMapView) -> ConfigMapView {
    let made_config_map = make_plugins_config_map(rabbitmq);
    ConfigMapView {
        data: made_config_map.data,
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_config_map.metadata.labels,
            annotations: made_config_map.metadata.annotations,
            ..found_config_map.metadata
        },
        ..found_config_map
    }
}

pub open spec fn make_plugins_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView {
    ConfigMapView::default()
        .with_metadata(ObjectMetaView::default()
            .with_name(make_plugins_config_map_name(rabbitmq))
            .with_namespace(rabbitmq.metadata.namespace->0)
            .with_owner_references(make_owner_references(rabbitmq))
            .with_labels(make_labels(rabbitmq))
            .with_annotations(rabbitmq.spec.annotations)
        )
        .with_data(Map::empty()
            .insert("enabled_plugins"@, "[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management]."@)
        )
}

}
