// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum RabbitmqReconcileStep {
    Init,
    AfterGetHeadlessService,
    AfterCreateHeadlessService,
    AfterUpdateHeadlessService,
    AfterGetService,
    AfterCreateService,
    AfterUpdateService,
    AfterGetErlangCookieSecret,
    AfterCreateErlangCookieSecret,
    AfterUpdateErlangCookieSecret,
    AfterGetDefaultUserSecret,
    AfterCreateDefaultUserSecret,
    AfterUpdateDefaultUserSecret,
    AfterGetPluginsConfigMap,
    AfterCreatePluginsConfigMap,
    AfterUpdatePluginsConfigMap,
    AfterGetServerConfigMap,
    AfterCreateServerConfigMap,
    AfterUpdateServerConfigMap,
    AfterGetServiceAccount,
    AfterCreateServiceAccount,
    AfterUpdateServiceAccount,
    AfterGetRole,
    AfterCreateRole,
    AfterUpdateRole,
    AfterGetRoleBinding,
    AfterCreateRoleBinding,
    AfterUpdateRoleBinding,
    AfterGetStatefulSet,
    AfterCreateStatefulSet,
    AfterUpdateStatefulSet,
    // AfterKRequestStep(ActionKind, ResourceKind, ResourceKind),
    Done,
    Error,
}

pub enum ResourceKind {
    HeadlessService,
    MainService,
    ErlangCookieSecret,
    DefaultUserSecret,
    PluginsConfigMap,
    ServerConfigMap,
    ServiceAccount,
    Role,
    RoleBinding,
    StatefulSet,
}

pub enum ActionKind {
    Get,
    Create,
    Update,
}

pub enum RabbitmqError {
    CreateError,
    UpdateError,
}

pub open spec fn resource_res_to_view<T: View>(res: Result<T, RabbitmqError>) -> Result<T::V, RabbitmqError> {
    match res {
        Ok(resource) => Ok(resource@),
        Err(err) => Err(err),
    }
}

}
