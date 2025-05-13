// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{resource::*, service_account::*};
use vstd::prelude::*;

// A service account is a type of non-human account that, in Kubernetes, provides a distinct identity in a Kubernetes cluster.
// Application Pods, system components, and entities inside and outside the cluster can use a specific ServiceAccount's credentials to identify as that ServiceAccount.
// This identity is useful in various situations, including authenticating to the API server or implementing identity-based security policies.
//
// This definition is a wrapper of ServiceAccount defined at
// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/service_account.rs.
// It is supposed to be used in exec controller code.
//
// More detailed information: https://kubernetes.io/docs/concepts/security/service-accounts/.

implement_object_wrapper_type!(
    ServiceAccount,
    deps_hack::k8s_openapi::api::core::v1::ServiceAccount,
    ServiceAccountView
);
