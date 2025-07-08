// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub open spec fn make_labels(rabbitmq: RabbitmqClusterView) -> Map<StringView, StringView> { rabbitmq.spec.labels.insert("app"@, rabbitmq.metadata.name->0) }

pub open spec fn make_owner_references(rabbitmq: RabbitmqClusterView) -> Seq<OwnerReferenceView> { seq![rabbitmq.controller_owner_ref()] }

pub open spec fn make_secret(rabbitmq: RabbitmqClusterView, name: StringView, data: Map<StringView, StringView>) -> SecretView {
    SecretView::default()
        .with_metadata(ObjectMetaView::default()
            .with_name(name)
            .with_namespace(rabbitmq.metadata.namespace->0)
            .with_owner_references(make_owner_references(rabbitmq))
            .with_labels(make_labels(rabbitmq))
            .with_annotations(rabbitmq.spec.annotations)
        ).with_data(data)
}

pub open spec fn make_service(rabbitmq: RabbitmqClusterView, name: StringView, ports: Seq<ServicePortView>, cluster_ip: bool) -> ServiceView {
    ServiceView::default()
        .with_metadata(ObjectMetaView::default()
            .with_name(name)
            .with_namespace(rabbitmq.metadata.namespace->0)
            .with_owner_references(make_owner_references(rabbitmq))
            .with_labels(make_labels(rabbitmq))
            .with_annotations(rabbitmq.spec.annotations)
        ).with_spec({
            let spec = ServiceSpecView::default()
                .with_ports(ports)
                .with_selector(Map::empty()
                    .insert("app"@, rabbitmq.metadata.name->0)
                ).with_publish_not_ready_addresses(true);
            if !cluster_ip {
                spec.with_cluster_ip("None"@)
            } else {
                spec
            }
        })
}

}
