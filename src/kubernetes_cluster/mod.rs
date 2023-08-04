// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
pub mod proof;
pub mod spec;

use std::marker::PhantomData;

pub struct Cluster<K, E, R> {
    _marker1: PhantomData<K>,
    _marker2: PhantomData<E>,
    _marker3: PhantomData<R>,
}
