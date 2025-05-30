// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::fluent_controller::fluentbit::trusted::spec_types::FluentBitView;
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vstd_ext::{string_map::*, string_view::*};
use deps_hack::kube::Resource;
use vstd::prelude::*;

verus! {

pub trait Maker {
    uninterp spec fn make_service_account_key(fb: FluentBitView) -> ObjectRef;
    uninterp spec fn make_role_key(fb: FluentBitView) -> ObjectRef;
    uninterp spec fn make_role_binding_key(fb: FluentBitView) -> ObjectRef;
    uninterp spec fn make_service_key(fb: FluentBitView) -> ObjectRef;
    uninterp spec fn make_daemon_set_key(fb: FluentBitView) -> ObjectRef;

    uninterp spec fn make_service_account(fb: FluentBitView) -> ServiceAccountView;
    uninterp spec fn make_role(fb: FluentBitView) -> RoleView;
    uninterp spec fn make_role_binding(fb: FluentBitView) -> RoleBindingView;
    uninterp spec fn make_service(fb: FluentBitView) -> ServiceView;
    uninterp spec fn make_daemon_set(fb: FluentBitView) -> DaemonSetView;
}

}
