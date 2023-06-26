// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum RabbitmqReconcileStep {
    Init,
    AfterCreateHeadlessService,
    AfterCreateService,
    AfterCreateErlangCookieSecret,
    AfterCreateDefaultUserSecret,
    AfterCreatePluginsConfigMap,
    AfterGetServerConfigMap,
    AfterCreateServerConfigMap,
    AfterUpdateServerConfigMap,
    AfterCreateServiceAccount,
    AfterCreateRole,
    AfterCreateRoleBinding,
    AfterGetStatefulSet,
    AfterCreateStatefulSet,
    AfterUpdateStatefulSet,
    Done,
    Error,
}

}
