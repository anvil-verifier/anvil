// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::{api_method::*, dynamic::*, resource::*};
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::resource_builder;
use crate::vstd_ext::{string_map::StringMap, string_view::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub trait ResourceBuilder<K: View, T: View, SpecBuilder: resource_builder::ResourceBuilder<K::V, T::V>>
{
    spec fn requirements(cr: K::V) -> bool;

    fn get_request(cr: &K) -> (req: KubeGetRequest)
        requires Self::requirements(cr@),
        ensures req@ == SpecBuilder::get_request(cr@);

    fn make(cr: &K, state: &T) -> (res: Result<DynamicObject, ()>)
        requires Self::requirements(cr@),
        ensures resource_res_to_view(res) == SpecBuilder::make(cr@, state@);

    fn update(cr: &K, state: &T, obj: DynamicObject) -> (res: Result<DynamicObject, ()>)
        requires Self::requirements(cr@),
        ensures resource_res_to_view(res) == SpecBuilder::update(cr@, state@, obj@);

    fn state_after_create(cr: &K, obj: DynamicObject, state: T) -> (res: Result<(T, Option<KubeAPIRequest>), ()>)
        requires Self::requirements(cr@),
        ensures
            res.is_Ok() == SpecBuilder::state_after_create(cr@, obj@, state@).is_Ok(),
            res.is_Ok() ==> (res.get_Ok_0().0@, opt_req_to_view(&res.get_Ok_0().1)) == SpecBuilder::state_after_create(cr@, obj@, state@).get_Ok_0();

    fn state_after_update(cr: &K, obj: DynamicObject, state: T) -> (res: Result<(T, Option<KubeAPIRequest>), ()>)
        requires Self::requirements(cr@),
        ensures
            res.is_Ok() == SpecBuilder::state_after_update(cr@, obj@, state@).is_Ok(),
            res.is_Ok() ==> (res.get_Ok_0().0@, opt_req_to_view(&res.get_Ok_0().1)) == SpecBuilder::state_after_update(cr@, obj@, state@).get_Ok_0();
}

pub open spec fn resource_res_to_view<T: View>(res: Result<T, ()>) -> Result<T::V, ()> {
    match res {
        Ok(resource) => Ok(resource@),
        Err(err) => Err(err),
    }
}

}
