// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
pub mod cluster;
pub mod cluster_safety;
pub mod controller_runtime;
pub mod controller_runtime_eventual_safety;
pub mod controller_runtime_liveness;
pub mod controller_runtime_safety;
pub mod kubernetes_api_liveness;
pub mod kubernetes_api_safety;
pub mod wf1_assistant;

use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::resource::ResourceView;
use crate::reconciler::spec::reconciler::Reconciler;
use std::marker::PhantomData;

struct Cluster<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> {
    _marker1: PhantomData<K>,
    _marker2: PhantomData<E>,
    _marker3: PhantomData<R>,
}
