use crate::kubernetes_api_objects::spec::prelude::*;
use vstd::prelude::*;

verus! {

pub trait ResourceBuilder<K, T> {
    spec fn get_request(cr: K) -> GetRequest;

    spec fn make(cr: K, state: T) -> Result<DynamicObjectView, ()>;

    spec fn update(cr: K, state: T, obj: DynamicObjectView) -> Result<DynamicObjectView, ()>;

    spec fn state_after_create(cr: K, obj: DynamicObjectView, state: T) -> Result<(T, Option<APIRequest>), ()>;

    spec fn state_after_update(cr: K, obj: DynamicObjectView, state: T) -> Result<(T, Option<APIRequest>), ()>;
}

}
