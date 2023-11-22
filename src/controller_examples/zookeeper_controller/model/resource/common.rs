// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use crate::zookeeper_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub open spec fn make_base_labels(zk: ZookeeperClusterView) -> Map<StringView, StringView> { map![new_strlit("app")@ => zk.metadata.name.get_Some_0()] }

pub open spec fn make_labels(zk: ZookeeperClusterView) -> Map<StringView, StringView> { zk.spec.labels.union_prefer_right(make_base_labels(zk)) }

pub open spec fn make_owner_references(zk: ZookeeperClusterView) -> Seq<OwnerReferenceView> { seq![zk.controller_owner_ref()] }

pub open spec fn make_service(zk: ZookeeperClusterView, name: StringView, ports: Seq<ServicePortView>, cluster_ip: bool) -> ServiceView {
    ServiceView {
        metadata: ObjectMetaView {
            name: Some(name),
            labels: Some(make_labels(zk)),
            annotations: Some(zk.spec.annotations),
            owner_references: Some(make_owner_references(zk)),
            ..ObjectMetaView::default()
        },
        spec: Some(ServiceSpecView {
            ports: Some(ports),
            selector: Some(make_base_labels(zk)),
            cluster_ip: if !cluster_ip { Some(new_strlit("None")@) } else { None },
            ..ServiceSpecView::default()
        }),
        ..ServiceView::default()
    }
}

}
