// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
pub mod proof;
pub mod spec;

use std::marker::PhantomData;

/// The Cluster struct is a container for all the specifications and lemmas regarding the Kubernetes cluster, including
/// those seperate state machines and the compound state machine. It take three generics, which should be essentially one:
/// R is the type of Reconciler and K and E are the two generics fed to R. We don't bound K, E or R here but will do that
/// when implementing methods for it.
/// 
/// By using such a struct, we don't have to let all the functions carry the generics; and therefore we don't need to
/// specify the generics whenever calling those spec or proof functions.
/// 
/// Three markers (PhantomData) are used here to make the three generics not "unused". Unused generics will trigger
/// compilation errors.
pub struct Cluster<K, E, R> {
    _marker1: PhantomData<K>,
    _marker2: PhantomData<E>,
    _marker3: PhantomData<R>,
}
