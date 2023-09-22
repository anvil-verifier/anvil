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
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::reconciler::exec::{io::*, reconciler::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct ServiceAccountBuilder {}

impl ResourceBuilder<ServiceAccount, spec_resource::ServiceAccountBuilder> for ServiceAccountBuilder {
    fn make(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState) -> Result<ServiceAccount, RabbitmqError> {
        Ok(make_service_account(rabbitmq))
    }

    fn update(rabbitmq: &RabbitmqCluster, state: &RabbitmqReconcileState, found_resource: ServiceAccount) -> Result<ServiceAccount, RabbitmqError> {
        Ok(update_service_account(rabbitmq, found_resource))
    }

    fn get_result_check(obj: DynamicObject) -> Result<ServiceAccount, RabbitmqError> {
        let sts = ServiceAccount::unmarshal(obj);
        if sts.is_ok() {
            Ok(sts.unwrap())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    fn create_result_check(obj: DynamicObject) -> Result<ServiceAccount, RabbitmqError> {
        let sts = ServiceAccount::unmarshal(obj);
        if sts.is_ok() {
            Ok(sts.unwrap())
        } else {
            Err(RabbitmqError::Error)
        }
    }

    fn update_result_check(obj: DynamicObject) -> Result<ServiceAccount, RabbitmqError> {
        let sts = ServiceAccount::unmarshal(obj);
        if sts.is_ok() {
            Ok(sts.unwrap())
        } else {
            Err(RabbitmqError::Error)
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
        metadata.set_name(rabbitmq.name().unwrap().concat(new_strlit("-server")));
        metadata.set_namespace(rabbitmq.namespace().unwrap());
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.set_labels(make_labels(rabbitmq));
        metadata.set_annotations(rabbitmq.spec().annotations());
        metadata
    });
    service_account
}

}
