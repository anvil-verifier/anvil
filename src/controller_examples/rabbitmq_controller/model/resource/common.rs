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

pub open spec fn make_labels(rabbitmq: RabbitmqClusterView) -> Map<StringView, StringView> { rabbitmq.spec.labels.insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0()) }

pub open spec fn make_owner_references(rabbitmq: RabbitmqClusterView) -> Seq<OwnerReferenceView> { seq![rabbitmq.controller_owner_ref()] }

pub open spec fn make_secret(rabbitmq: RabbitmqClusterView, name: StringView, data: Map<StringView, StringView>) -> SecretView {
    SecretView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(name)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_owner_references(make_owner_references(rabbitmq))
            .set_labels(make_labels(rabbitmq))
            .set_annotations(rabbitmq.spec.annotations)
        ).set_data(data)
}

pub open spec fn make_service(rabbitmq: RabbitmqClusterView, name: StringView, ports: Seq<ServicePortView>, cluster_ip: bool) -> ServiceView {
    ServiceView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(name)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_owner_references(make_owner_references(rabbitmq))
            .set_labels(make_labels(rabbitmq))
            .set_annotations(rabbitmq.spec.annotations)
        ).set_spec({
            let spec = ServiceSpecView::default()
                .set_ports(ports)
                .set_selector(Map::empty()
                    .insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0())
                ).set_publish_not_ready_addresses(true);
            if !cluster_ip {
                spec.set_cluster_ip(new_strlit("None")@)
            } else {
                spec
            }
        })
}

}
