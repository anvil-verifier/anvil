// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::prelude::*;

#[macro_export]
macro_rules! implement_field_wrapper_type {
    ($t:ident, $it:ty, $vt:ty) => {
        verus! {

        #[verifier(external_body)]
        pub struct $t {
            inner: $it,
        }

        }

        implement_view_trait!($t, $vt);
        implement_deep_view_trait!($t, $vt);
        implement_default_trait!($t, $it, $vt);
        implement_clone_trait!($t);
    };
}

pub use implement_field_wrapper_type;

#[macro_export]
macro_rules! implement_object_wrapper_type {
    ($t:ident, $it:ty, $vt:ty) => {
        implement_field_wrapper_type!($t, $it, $vt);

        verus! {

        impl $t {
            #[verifier(external_body)]
            pub fn metadata(&self) -> (metadata: ObjectMeta)
                ensures metadata@ == self@.metadata,
            {
                ObjectMeta::from_kube(self.inner.metadata.clone())
            }

            #[verifier(external_body)]
            pub fn set_metadata(&mut self, metadata: ObjectMeta)
                ensures self@ == old(self)@.with_metadata(metadata@),
            {
                self.inner.metadata = metadata.into_kube();
            }

            #[verifier(external_body)]
            pub fn api_resource() -> (res: ApiResource)
                ensures res@.kind == $vt::kind(),
            {
                ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<$it>(&()))
            }

            #[verifier(external_body)]
            pub fn marshal(self) -> (obj: DynamicObject)
                ensures obj@ == self@.marshal(),
            {
                DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
            }

            #[verifier(external_body)]
            pub fn unmarshal(obj: DynamicObject) -> (res: Result<$t, UnmarshalError>)
                ensures
                    res.is_Ok() == $vt::unmarshal(obj@).is_Ok(),
                    res.is_Ok() ==> res.get_Ok_0()@ == $vt::unmarshal(obj@).get_Ok_0(),
            {
                let parse_result = obj.into_kube().try_parse::<$it>();
                if parse_result.is_ok() {
                    let res = Self { inner: parse_result.unwrap() };
                    Ok(res)
                } else {
                    Err(())
                }
            }
        }

        }
    };
}

pub use implement_object_wrapper_type;

#[macro_export]
macro_rules! implement_custom_object_wrapper_type {
    ($t:ident, $it:ty, $vt:ty) => {
        implement_object_wrapper_type!($t, $it, $vt);

        verus! {

        impl $t {
            #[verifier(external_body)]
            pub fn controller_owner_ref(&self) -> (owner_reference: OwnerReference)
                ensures owner_reference@ == self@.controller_owner_ref(),
            {
                OwnerReference::from_kube(self.inner.controller_owner_ref(&()).unwrap())
            }
        }

        }
    };
}

pub use implement_custom_object_wrapper_type;

#[macro_export]
macro_rules! implement_view_trait {
    ($t:ty, $vt:ty) => {
        verus! {

        impl View for $t {
            type V = $vt;

            spec fn view(&self) -> $vt;
        }

        }
    };
}

pub use implement_view_trait;

#[macro_export]
macro_rules! implement_deep_view_trait {
    ($t:ty, $vt:ty) => {
        verus! {

        impl DeepView for $t {
            type V = $vt;

            open spec fn deep_view(&self) -> $vt {
                self@
            }
        }

        }
    };
}

pub use implement_deep_view_trait;

#[macro_export]
macro_rules! implement_default_trait {
    ($t:ty, $it:ty, $vt:ty) => {
        verus! {

        impl std::default::Default for $t {
            #[verifier(external_body)]
            fn default() -> (res: $t)
                ensures res@ == $vt::default(),
            {
                Self { inner: $it::default() }
            }
        }

        }
    };
}

pub use implement_default_trait;

#[macro_export]
macro_rules! implement_clone_trait {
    ($t:ty) => {
        verus! {

        impl std::clone::Clone for $t {
            #[verifier(external_body)]
            fn clone(&self) -> (res: $t)
                ensures res@ == self@
            {
                Self { inner: self.inner.clone() }
            }
        }

        }
    };
}

pub use implement_clone_trait;

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
