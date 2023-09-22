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
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

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
        data: Some({
            if found_config_map.data.is_Some() {
                found_config_map.data.get_Some_0()
                    .insert(new_strlit("enabled_plugins")@, new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management].")@)
            } else {
                Map::empty().insert(
                    new_strlit("enabled_plugins")@,
                    new_strlit("[rabbitmq_peer_discovery_k8s,rabbitmq_prometheus,rabbitmq_management].")@
                )
            }
        }),
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