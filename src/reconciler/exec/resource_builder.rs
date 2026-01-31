use crate::kubernetes_api_objects::exec::{api_method::*, dynamic::*};
use crate::reconciler::spec::resource_builder;
use vstd::prelude::*;

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
            res is Ok == SpecBuilder::state_after_create(cr@, obj@, state@) is Ok,
            res is Ok ==> (res->Ok_0.0@, res->Ok_0.1.deep_view()) == SpecBuilder::state_after_create(cr@, obj@, state@)->Ok_0;

    fn state_after_update(cr: &K, obj: DynamicObject, state: T) -> (res: Result<(T, Option<KubeAPIRequest>), ()>)
        requires Self::requirements(cr@),
        ensures
            res is Ok == SpecBuilder::state_after_update(cr@, obj@, state@) is Ok,
            res is Ok ==> (res->Ok_0.0@, res->Ok_0.1.deep_view()) == SpecBuilder::state_after_update(cr@, obj@, state@)->Ok_0;
}

pub open spec fn resource_res_to_view<T: View>(res: Result<T, ()>) -> Result<T::V, ()> {
    match res {
        Ok(resource) => Ok(resource@),
        Err(err) => Err(err),
    }
}

}
