// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::api_resource::*;
use vstd::prelude::*;

verus! {

// ApiResource is used for creating API handles for DynamicObject.
//
// This definition is a wrapper of ApiResource defined at
// https://github.com/kube-rs/kube/blob/main/kube-core/src/discovery.rs.
// It is supposed to be used in exec controller code.

#[verifier(external_body)]
pub struct ApiResource {
    inner: deps_hack::kube::api::ApiResource,
}

implement_view_trait!(ApiResource, ApiResourceView);
implement_deep_view_trait!(ApiResource, ApiResourceView);
implement_resource_wrapper_trait!(ApiResource, deps_hack::kube::api::ApiResource);

}
