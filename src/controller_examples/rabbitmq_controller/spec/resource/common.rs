// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub trait ResourceBuilder {
    spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest;

    spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, RabbitmqError>;

    spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, RabbitmqError>;

    spec fn state_after_create_or_update(obj: DynamicObjectView, state: RabbitmqReconcileState) -> Result<RabbitmqReconcileState, RabbitmqError>;

    /// Describes how can the created/updated object satisfies the desired state.
    spec fn requirements(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, resources: StoredState) -> bool;

    /// resource_state_matches takes the cr and an object that stores all resources, then it will check whether the resource pool
    /// reaches the desired state in the view of the object that it builds.
    spec fn resource_state_matches(rabbitmq: RabbitmqClusterView, resources: StoredState) -> bool;

    proof fn created_or_updated_obj_matches_desired_state(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, resources: StoredState)
        requires
            rabbitmq.metadata.name.is_Some(),
            rabbitmq.metadata.namespace.is_Some(),
        ensures
            Self::requirements(rabbitmq, state, resources) ==> {
                let resource_key = Self::get_request(rabbitmq).key;
                let made_obj = Self::make(rabbitmq, state);
                let updated_obj = Self::update(rabbitmq, state, resources[resource_key]);
                forall |metadata: ObjectMetaView| #![auto] {
                    &&& (made_obj.is_Ok() ==> Self::resource_state_matches(rabbitmq, resources.insert(resource_key, made_obj.get_Ok_0().set_metadata(metadata))))
                    &&& (
                        resources.contains_key(resource_key) && Self::resource_state_matches(rabbitmq, resources) && updated_obj.is_Ok() 
                        ==> Self::resource_state_matches(rabbitmq, resources.insert(resource_key, updated_obj.get_Ok_0().set_metadata(metadata)))
                    )
                }
                    
            };
}

pub open spec fn make_labels(rabbitmq: RabbitmqClusterView) -> Map<StringView, StringView>
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.spec.labels.insert(new_strlit("app")@, rabbitmq.metadata.name.get_Some_0())
}

pub open spec fn make_owner_references(rabbitmq: RabbitmqClusterView) -> Seq<OwnerReferenceView> {
    seq![rabbitmq.controller_owner_ref()]
}

pub open spec fn make_secret(
    rabbitmq: RabbitmqClusterView, name: StringView, data: Map<StringView, StringView>
) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    SecretView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(name)
            .set_namespace(rabbitmq.metadata.namespace.get_Some_0())
            .set_owner_references(make_owner_references(rabbitmq))
            .set_labels(make_labels(rabbitmq))
            .set_annotations(rabbitmq.spec.annotations)
        ).set_data(data)
}

pub open spec fn make_service(
    rabbitmq: RabbitmqClusterView, name: StringView, ports: Seq<ServicePortView>, cluster_ip: bool
) -> ServiceView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
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
