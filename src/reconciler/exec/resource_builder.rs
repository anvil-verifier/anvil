// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::{api_method::*, dynamic::*, resource::*};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::resource_builder;
use crate::vstd_ext::{string_map::StringMap, string_view::*, to_view::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub trait ResourceBuilder<K: View, T: View, SpecBuilder: resource_builder::ResourceBuilder<K::V, T::V>>
{
    spec fn requirements(cr: K::V) -> bool;
    
    fn get_request(cr: &K) -> (req: KubeGetRequest)
        requires
            Self::requirements(cr@),
        ensures
            req.to_view() == SpecBuilder::get_request(cr@);

    fn make(cr: &K, state: &T) -> (res: Result<DynamicObject, ()>)
        requires
            Self::requirements(cr@),
        ensures
            resource_res_to_view(res) == SpecBuilder::make(cr@, state@);

    fn update(cr: &K, state: &T, obj: DynamicObject) -> (res: Result<DynamicObject, ()>)
        requires
            Self::requirements(cr@),
        ensures
            resource_res_to_view(res) == SpecBuilder::update(cr@, state@, obj@);

    /// state_after_create_or_update describes how a successfully created/updated object influences the reconcile state except
    /// the part concerning control flow, i.e., what the next step is. The next step will be decided by the reconciler. Such design
    /// leads to lower coupling and fewer mistakes (e.g. next step and get request mismatch).
    fn state_after_create_or_update(obj: DynamicObject, state: T) -> (res: Result<T, ()>)
        ensures
            resource_res_to_view(res) == SpecBuilder::state_after_create_or_update(obj@, state@);
}

pub open spec fn resource_res_to_view<T: View>(res: Result<T, ()>) -> Result<T::V, ()> {
    match res {
        Ok(resource) => Ok(resource@),
        Err(err) => Err(err),
    }
}

}
