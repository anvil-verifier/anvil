// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, cluster_state_machine::Step, message::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::string_view::int_to_string_view;
use crate::zookeeper_controller::{
    common::*,
    spec::{reconciler::*, resource::*, types::*},
};
use vstd::prelude::*;

verus! {

pub open spec fn liveness_theorem() -> bool {
    cluster_spec().entails(tla_forall(|zookeeper: ZookeeperClusterView| liveness(zookeeper)))
}

pub open spec fn cluster_spec() -> TempPred<ZKCluster> {
    ZKCluster::sm_spec()
}

pub open spec fn liveness(zookeeper: ZookeeperClusterView) -> TempPred<ZKCluster> {
    always(lift_state(desired_state_is(zookeeper))).leads_to(always(lift_state(current_state_matches(zookeeper))))
}

pub open spec fn desired_state_is(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    ZKCluster::desired_state_is(zookeeper)
}

pub open spec fn current_state_matches(zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    |s: ZKCluster| {
        forall |sub_resource: SubResource|
            #[trigger] resource_state_matches(sub_resource, zookeeper, s.resources())
    }
}

pub open spec fn resource_state_matches(sub_resource: SubResource, zookeeper: ZookeeperClusterView, resources: StoredState) -> bool {
    match sub_resource {
        SubResource::HeadlessService => {
            let key = make_headless_service_key(zookeeper);
            let obj = resources[key];
            let made_spec = make_headless_service(zookeeper).spec.get_Some_0();
            let spec = ServiceView::unmarshal(obj).get_Ok_0().spec.get_Some_0();
            &&& resources.contains_key(key)
            &&& ServiceView::unmarshal(obj).is_Ok()
            &&& ServiceView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& made_spec == ServiceSpecView {
                cluster_ip: made_spec.cluster_ip,
                ..spec
            }
            &&& obj.metadata.labels == make_headless_service(zookeeper).metadata.labels
            &&& obj.metadata.annotations == make_headless_service(zookeeper).metadata.annotations
        },
        SubResource::ClientService => {
            let key = make_client_service_key(zookeeper);
            let obj = resources[key];
            let made_spec = make_client_service(zookeeper).spec.get_Some_0();
            let spec = ServiceView::unmarshal(obj).get_Ok_0().spec.get_Some_0();
            &&& resources.contains_key(key)
            &&& ServiceView::unmarshal(obj).is_Ok()
            &&& ServiceView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& made_spec == ServiceSpecView {
                cluster_ip: made_spec.cluster_ip,
                ..spec
            }
            &&& obj.metadata.labels == make_client_service(zookeeper).metadata.labels
            &&& obj.metadata.annotations == make_client_service(zookeeper).metadata.annotations
        },
        SubResource::AdminServerService => {
            let key = make_admin_server_service_key(zookeeper);
            let obj = resources[key];
            let made_spec = make_admin_server_service(zookeeper).spec.get_Some_0();
            let spec = ServiceView::unmarshal(obj).get_Ok_0().spec.get_Some_0();
            &&& resources.contains_key(key)
            &&& ServiceView::unmarshal(obj).is_Ok()
            &&& ServiceView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& made_spec == ServiceSpecView {
                cluster_ip: made_spec.cluster_ip,
                ..spec
            }
            &&& obj.metadata.labels == make_admin_server_service(zookeeper).metadata.labels
            &&& obj.metadata.annotations == make_admin_server_service(zookeeper).metadata.annotations
        },
        SubResource::ConfigMap => {
            let key = make_config_map_key(zookeeper);
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& ConfigMapView::unmarshal(obj).is_Ok()
            &&& ConfigMapView::unmarshal(obj).get_Ok_0().data == make_config_map(zookeeper).data
            &&& obj.spec == ConfigMapView::marshal_spec((make_config_map(zookeeper).data, ()))
            &&& obj.metadata.labels == make_config_map(zookeeper).metadata.labels
            &&& obj.metadata.annotations == make_config_map(zookeeper).metadata.annotations
        },
        SubResource::StatefulSet => {
            let key = make_stateful_set_key(zookeeper);
            let obj = resources[key];
            let cm_key = make_config_map_key(zookeeper);
            let cm_obj = resources[cm_key];
            let made_sts = make_stateful_set(zookeeper, int_to_string_view(cm_obj.metadata.resource_version.get_Some_0()));
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
