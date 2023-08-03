// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
pub mod proof;
pub mod spec;

use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::resource::ResourceView;
use crate::reconciler::spec::reconciler::Reconciler;
use std::marker::PhantomData;

pub struct Cluster<K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> {
    _marker1: PhantomData<K>,
    _marker2: PhantomData<E>,
    _marker3: PhantomData<R>,
}
