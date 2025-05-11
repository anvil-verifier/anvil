// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::prelude::*;

pub trait ResourceWrapper<T>: Sized {
    fn from_kube(inner: T) -> Self;

    fn into_kube(self) -> T;

    fn as_kube_ref(&self) -> &T;

    fn as_kube_mut_ref(&mut self) -> &mut T;
}

#[macro_export]
macro_rules! implement_resource_wrapper_trait {
    ($t:ty, $it:ty) => {
        impl ResourceWrapper<$it> for $t {
            fn from_kube(inner: $it) -> $t {
                Self { inner: inner }
            }

            fn into_kube(self) -> $it {
                self.inner
            }

            fn as_kube_ref(&self) -> &$it {
                &self.inner
            }

            fn as_kube_mut_ref(&mut self) -> &mut $it {
                &mut self.inner
            }
        }
    };
}

pub use implement_resource_wrapper_trait;
