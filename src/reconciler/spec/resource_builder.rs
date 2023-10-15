// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub trait ResourceBuilder<K, T> {
    spec fn get_request(cr: K) -> GetRequest;

    spec fn make(cr: K, state: T) -> Result<DynamicObjectView, ()>;

    spec fn update(cr: K, state: T, obj: DynamicObjectView) -> Result<DynamicObjectView, ()>;

    spec fn state_after_create(cr: K, obj: DynamicObjectView, state: T) -> Result<(T, Option<APIRequest>), ()>;

    spec fn state_after_update(cr: K, obj: DynamicObjectView, state: T) -> Result<(T, Option<APIRequest>), ()>;

    /// resource_state_matches takes the cr and an object that stores all resources, then it will check whether the resource pool
    /// reaches the desired state in the view of the object that it builds.
    spec fn resource_state_matches(cr: K, resources: StoredState) -> bool;

    spec fn unchangeable(object: DynamicObjectView, cr: K) -> bool;
}

}
