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
    Done,
    Error,
}

}
