// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::resource::role::RoleBuilder;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::rabbitmq_controller::spec::types::RabbitmqClusterView;
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct ServiceAccountBuilder {}

impl ResourceBuilder<RabbitmqCluster, RabbitmqReconcileState, spec_resource::ServiceAccountBuilder> for ServiceAccountBuilder {
    open spec fn requirements(rabbitmq: RabbitmqClusterView) -> bool {
        &&& rabbitmq.metadata.name.is_Some()
        &&& rabbitmq.metadata.namespace.is_Some()
    }

    fn get_request(rabbitmq: &RabbitmqCluster) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: ServiceAccount::api_resource(),
            name: make_service_account_name(rabbitmq),
            namespace: rabbitmq.namespace().unwrap(),
        }
    }

    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_service_account(rabbitmq).marshal())
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let sa = ServiceAccount::unmarshal(obj);
        if sa.is_ok() {
            Ok(update_service_account(rabbitmq, sa.unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn state_after_create_or_update(obj: DynamicObject, state: RabbitmqReconcileState) -> (res: Result<RabbitmqReconcileState, ()>) {
        let sa = ServiceAccount::unmarshal(obj);
        if sa.is_ok() {
            Ok(state)
        } else {
            Err(())
        }
    }
}

pub fn update_service_account(rabbitmq: &RabbitmqCluster, found_service_account: ServiceAccount) -> (service_account: ServiceAccount)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service_account@ == spec_resource::update_service_account(rabbitmq@, found_service_account@),
{
    let mut service_account = found_service_account.clone();
    let made_service_account = make_service_account(rabbitmq);
    service_account.set_metadata({
        let mut metadata = found_service_account.metadata();
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_service_account.metadata().labels().unwrap());
        metadata.set_annotations(made_service_account.metadata().annotations().unwrap());
        metadata
    });
    service_account
}

pub fn make_service_account_name(rabbitmq: &RabbitmqCluster) -> (name: String)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        name@ == spec_resource::make_service_account_name(rabbitmq@),
{
    rabbitmq.name().unwrap().concat(new_strlit("-server"))
}

pub fn make_service_account(rabbitmq: &RabbitmqCluster) -> (service_account: ServiceAccount)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        service_account@ == spec_resource::make_service_account(rabbitmq@),
{
    let mut service_account = ServiceAccount::default();
    service_account.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_service_account_name(rabbitmq));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    service_account
}

}
