// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::v2::kubernetes_cluster::spec::{api_server::types::*, controller::types::*};
use vstd::prelude::*;

verus! {

pub struct InstallTypeHelper<T: CustomResourceView> {
    dummy: core::marker::PhantomData<T>,
}

impl<T: CustomResourceView> InstallTypeHelper<T> {
    pub open spec fn unmarshal_spec(v: Value) -> bool {
        T::unmarshal_spec(v).is_Ok()
    }

    pub open spec fn unmarshal_status(v: Value) -> bool {
        T::unmarshal_status(v).is_Ok()
    }

    pub open spec fn valid_object(obj: DynamicObjectView) -> bool {
        T::unmarshal(obj).get_Ok_0().state_validation()
    }

    pub open spec fn valid_transition(obj: DynamicObjectView, old_obj: DynamicObjectView) -> bool {
        T::unmarshal(obj).get_Ok_0().transition_validation(T::unmarshal(old_obj).get_Ok_0())
    }

    pub open spec fn marshalled_default_status() -> Value {
        T::marshal_status(T::default().status())
    }
}

}
