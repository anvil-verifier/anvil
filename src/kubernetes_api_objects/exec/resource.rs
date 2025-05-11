// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use vstd::prelude::*;
#[macro_export]
macro_rules! implement_wrapper_type {
    ($t:ident, $it:ty, $vt:ty) => {
        verus! {
        #[verifier(external_body)]
        pub struct $t {
            inner: $it,
        }

        impl View for $t {
            type V = $vt;

            spec fn view(&self) -> $vt;
        }

        impl $t {
            #[verifier(external_body)]
            pub fn default() -> (res: $t)
                ensures res@ == $vt::default(),
            {
                Self { inner: $it::default() }
            }

            #[verifier(external_body)]
            pub fn clone(&self) -> (res: Self)
                ensures res@ == self@,
            {
                Self { inner: self.inner.clone() }
            }

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

pub use implement_wrapper_type;

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
