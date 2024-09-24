// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct Opaque {
    content: StringView,
}

pub trait Marshallable: Sized {
    spec fn marshal(self) -> Opaque;

    spec fn unmarshal(o: Opaque) -> Result<Self, UnmarshalError>;

    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()).is_Ok() && o == Self::unmarshal(o.marshal()).get_Ok_0();
}

}
