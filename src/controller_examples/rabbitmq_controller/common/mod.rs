// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

#[is_variant]
pub enum RabbitmqReconcileStep {
    Init,
    AfterCreateHeadlessService,
    AfterCreateService,
    AfterCreateErlangCookieSecret,
    AfterCreateDefaultUserSecret,
    AfterCreatePluginsConfigMap,
    AfterCreateServerConfigMap,
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
