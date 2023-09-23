// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

#[is_variant]
pub enum FluentBitReconcileStep {
    Init,
    AfterGetSecret,
    AfterGetRole,
    AfterCreateRole,
    AfterUpdateRole,
    AfterGetServiceAccount,
    AfterCreateServiceAccount,
    AfterUpdateServiceAccount,
    AfterGetRoleBinding,
    AfterCreateRoleBinding,
    AfterUpdateRoleBinding,
    AfterGetDaemonSet,
    AfterCreateDaemonSet,
    AfterUpdateDaemonSet,
    Done,
    Error,
}

}
