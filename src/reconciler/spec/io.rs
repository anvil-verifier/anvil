use crate::kubernetes_api_objects::{
    error::UnmarshalError,
    spec::{api_method::*, resource::*},
};
use vstd::prelude::*;

verus! {

pub struct VoidEReqView {}

pub struct VoidERespView {}

impl Marshallable for VoidEReqView {
    uninterp spec fn marshal(self) -> Value;

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()).is_Ok() && o == Self::unmarshal(o.marshal()).get_Ok_0()
    {}
}

impl Marshallable for VoidERespView {
    uninterp spec fn marshal(self) -> Value;

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()).is_Ok() && o == Self::unmarshal(o.marshal()).get_Ok_0()
    {}
}

#[is_variant]
pub enum RequestView<T> {
    KRequest(APIRequest),
    ExternalRequest(T),
}

impl<T> RequestView<T> {
    pub open spec fn is_k_update_request(self) -> bool {
        &&& self.is_KRequest()
        &&& self.get_KRequest_0().is_UpdateRequest()
    }

    pub open spec fn get_k_update_request(self) -> UpdateRequest {
        self.get_KRequest_0().get_UpdateRequest_0()
    }
}

#[is_variant]
pub enum ResponseView<T> {
    KResponse(APIResponse),
    ExternalResponse(T),
}

impl<T> ResponseView<T> {
    pub open spec fn is_k_get_response(self) -> bool {
        &&& self.is_KResponse()
        &&& self.get_KResponse_0().is_GetResponse()
    }

    pub open spec fn get_k_get_response(self) -> GetResponse {
        self.get_KResponse_0().get_GetResponse_0()
    }
}

#[macro_export]
macro_rules! is_some_k_get_resp_view {
    ($r:expr) => {
        $r.is_Some() && $r.get_Some_0().is_KResponse()
        && $r.get_Some_0().get_KResponse_0().is_GetResponse()
    };
}

#[macro_export]
macro_rules! is_some_k_create_resp_view {
    ($r:expr) => {
        $r.is_Some() && $r.get_Some_0().is_KResponse()
        && $r.get_Some_0().get_KResponse_0().is_CreateResponse()
    };
}

#[macro_export]
macro_rules! is_some_k_update_resp_view {
    ($r:expr) => {
        $r.is_Some() && $r.get_Some_0().is_KResponse()
        && $r.get_Some_0().get_KResponse_0().is_UpdateResponse()
    };
}

#[macro_export]
macro_rules! is_some_k_list_resp_view {
    ($r:expr) => {
        $r.is_Some() && $r.get_Some_0().is_KResponse()
        && $r.get_Some_0().get_KResponse_0().is_ListResponse()
    };
}

#[macro_export]
macro_rules! is_some_k_delete_resp_view {
    ($r:expr) => {
        $r.is_Some() && $r.get_Some_0().is_KResponse()
        && $r.get_Some_0().get_KResponse_0().is_DeleteResponse()
    };
}

#[macro_export]
macro_rules! is_some_k_get_then_update_resp_view {
    ($r:expr) => {
        $r.is_Some() && $r.get_Some_0().is_KResponse()
        && $r.get_Some_0().get_KResponse_0().is_GetThenUpdateResponse()
    };
}

#[macro_export]
macro_rules! is_some_k_get_then_delete_resp_view {
    ($r:expr) => {
        $r.is_Some() && $r.get_Some_0().is_KResponse()
        && $r.get_Some_0().get_KResponse_0().is_GetThenDeleteResponse()
    };
}

#[macro_export]
macro_rules! extract_some_k_get_resp_view {
    ($r:expr) => {
        $r.get_Some_0().get_KResponse_0().get_GetResponse_0().res
    };
}

#[macro_export]
macro_rules! extract_some_k_create_resp_view {
    ($r:expr) => {
        $r.get_Some_0().get_KResponse_0().get_CreateResponse_0().res
    };
}

#[macro_export]
macro_rules! extract_some_k_update_resp_view {
    ($r:expr) => {
        $r.get_Some_0().get_KResponse_0().get_UpdateResponse_0().res
    };
}

#[macro_export]
macro_rules! extract_some_k_list_resp_view {
    ($r:expr) => {
        $r.get_Some_0().get_KResponse_0().get_ListResponse_0().res
    };
}

#[macro_export]
macro_rules! extract_some_k_delete_resp_view {
    ($r:expr) => {
        $r.get_Some_0().get_KResponse_0().get_DeleteResponse_0().res
    };
}

#[macro_export]
macro_rules! extract_some_k_get_then_update_resp_view {
    ($r:expr) => {
        $r.get_Some_0().get_KResponse_0().get_GetThenUpdateResponse_0().res
    };
}

#[macro_export]
macro_rules! extract_some_k_get_then_delete_resp_view {
    ($r:expr) => {
        $r.get_Some_0().get_KResponse_0().get_GetThenDeleteResponse_0().res
    };
}

pub use is_some_k_get_resp_view;
pub use is_some_k_create_resp_view;
pub use is_some_k_update_resp_view;
pub use is_some_k_list_resp_view;
pub use is_some_k_delete_resp_view;
pub use is_some_k_get_then_update_resp_view;
pub use is_some_k_get_then_delete_resp_view;
pub use extract_some_k_get_resp_view;
pub use extract_some_k_create_resp_view;
pub use extract_some_k_update_resp_view;
pub use extract_some_k_list_resp_view;
pub use extract_some_k_delete_resp_view;
pub use extract_some_k_get_then_update_resp_view;
pub use extract_some_k_get_then_delete_resp_view;

}
