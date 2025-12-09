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
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()) is Ok && o == Self::unmarshal(o.marshal())->Ok_0
    {}
}

impl Marshallable for VoidERespView {
    uninterp spec fn marshal(self) -> Value;

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()) is Ok && o == Self::unmarshal(o.marshal())->Ok_0
    {}
}

pub enum RequestView<T> {
    KRequest(APIRequest),
    ExternalRequest(T),
}

pub type DefaultResp = Option<ResponseView<VoidERespView>>;
pub type DefaultReq = Option<RequestView<VoidEReqView>>;

impl<T> RequestView<T> {
    pub open spec fn is_k_update_request(self) -> bool {
        &&& self is KRequest
        &&& self->KRequest_0 is UpdateRequest
    }

    pub open spec fn get_k_update_request(self) -> UpdateRequest {
        self->KRequest_0->UpdateRequest_0
    }
}

pub enum ResponseView<T> {
    KResponse(APIResponse),
    ExternalResponse(T),
}

impl<T> ResponseView<T> {
    pub open spec fn is_k_get_response(self) -> bool {
        &&& self is KResponse
        &&& self->KResponse_0 is GetResponse
    }

    pub open spec fn get_k_get_response(self) -> GetResponse {
        self->KResponse_0->GetResponse_0
    }
}

#[macro_export]
macro_rules! is_some_k_get_resp_view {
    ($r:expr) => {
        if let Some(resp) = $r {
            resp is KResponse && resp->KResponse_0 is GetResponse
        } else {
            false
        }
    };
}

#[macro_export]
macro_rules! is_some_k_create_resp_view {
    ($r:expr) => {
        if let Some(resp) = $r {
            resp is KResponse && resp->KResponse_0 is CreateResponse
        } else {
            false
        }
    };
}

#[macro_export]
macro_rules! is_some_k_update_resp_view {
    ($r:expr) => {
        if let Some(resp) = $r {
            resp is KResponse && resp->KResponse_0 is UpdateResponse
        } else {
            false
        }
    };
}

#[macro_export]
macro_rules! is_some_k_list_resp_view {
    ($r:expr) => {
        if let Some(resp) = $r {
            resp is KResponse && resp->KResponse_0 is ListResponse
        } else {
            false
        }
    };
}

#[macro_export]
macro_rules! is_some_k_delete_resp_view {
    ($r:expr) => {
        if let Some(resp) = $r {
            resp is KResponse && resp->KResponse_0 is DeleteResponse
        } else {
            false
        }
    };
}

#[macro_export]
macro_rules! is_some_k_get_then_update_resp_view {
    ($r:expr) => {
        if let Some(resp) = $r {
            resp is KResponse && resp->KResponse_0 is GetThenUpdateResponse
        } else {
            false
        }
    };
}

#[macro_export]
macro_rules! is_some_k_get_then_delete_resp_view {
    ($r:expr) => {
        if let Some(resp) = $r {
            resp is KResponse && resp->KResponse_0 is GetThenDeleteResponse
        } else {
            false
        }
    };
}

#[macro_export]
macro_rules! extract_some_k_get_resp_view {
    ($r:expr) => {
        $r.unwrap()->KResponse_0->GetResponse_0.res
    };
}

#[macro_export]
macro_rules! extract_some_k_create_resp_view {
    ($r:expr) => {
        $r.unwrap()->KResponse_0->CreateResponse_0.res
    };
}

#[macro_export]
macro_rules! extract_some_k_update_resp_view {
    ($r:expr) => {
        $r.unwrap()->KResponse_0->UpdateResponse_0.res
    };
}

#[macro_export]
macro_rules! extract_some_k_list_resp_view {
    ($r:expr) => {
        $r.unwrap()->KResponse_0->ListResponse_0.res
    };
}

#[macro_export]
macro_rules! extract_some_k_delete_resp_view {
    ($r:expr) => {
        $r.unwrap()->KResponse_0->DeleteResponse_0.res
    };
}

#[macro_export]
macro_rules! extract_some_k_get_then_update_resp_view {
    ($r:expr) => {
        $r.unwrap()->KResponse_0->GetThenUpdateResponse_0.res
    };
}

#[macro_export]
macro_rules! extract_some_k_get_then_delete_resp_view {
    ($r:expr) => {
        $r.unwrap()->KResponse_0->GetThenDeleteResponse_0.res
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
