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
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::resource::config_map::ServerConfigMapBuilder;
use crate::rabbitmq_controller::spec::types::*;
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
        if cm.is_Ok() {
            Ok(update_plugins_config_map(rabbitmq, cm.get_Ok_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let cm = ConfigMapView::unmarshal(obj);
        if cm.is_Ok() {
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
        if cm.is_Ok() {
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

    open spec fn resource_state_matches(rabbitmq: RabbitmqClusterView, resources: StoredState) -> bool {
        let key = make_plugins_config_map_key(rabbitmq);
        let obj = resources[key];
        &&& resources.contains_key(key)
        &&& ConfigMapView::unmarshal(obj).is_Ok()
        &&& ConfigMapView::unmarshal(obj).get_Ok_0().data == make_plugins_config_map(rabbitmq).data
        &&& obj.metadata.labels == make_plugins_config_map(rabbitmq).metadata.labels
        &&& obj.metadata.annotations == make_plugins_config_map(rabbitmq).metadata.annotations
    }

    open spec fn unchangeable(object: DynamicObjectView, rabbitmq: RabbitmqClusterView) -> bool {
        true
    }
}

pub open spec fn make_plugins_config_map_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-plugins-conf")@
}

pub open spec fn make_plugins_config_map_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: ConfigMapView::kind(),
        name: make_plugins_config_map_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_plugins_config_map(rabbitmq: RabbitmqClusterView, found_config_map: ConfigMapView) -> ConfigMapView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
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

pub open spec fn make_plugins_config_map(rabbitmq: RabbitmqClusterView) -> ConfigMapView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ConfigMapView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_plugins_config_map_name(rabbitmq))
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_owner_references(make_owner_references(rabbitmq))
            .set_labels(make_labels(rabbitmq))
            .set_annotations(rabbitmq.spec.annotations)
        )
        .set_data(Map::empty()
            .insert(new_strlit("enabled_plugins")@, new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management].")@)
        )
}

}
