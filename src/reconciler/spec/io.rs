use crate::kubernetes_api_objects::{
    error::{UnmarshalError, APIError},
    spec::{api_method::*, resource::*, prelude::*},
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

pub enum ResponseView<T> {
    KResponse(APIResponse),
    ExternalResponse(T),
}

pub type DefaultResp = Option<ResponseView<VoidERespView>>;
pub type DefaultReq = Option<RequestView<VoidEReqView>>;

// because is X and get_X_0 works poorly with macros, we provide these helper functions

#[verifier(inline)]
pub open spec fn is_some_k_get_resp_view(resp_o: DefaultResp) -> bool {
    resp_o is Some && resp_o->0 is KResponse && resp_o->0->KResponse_0 is GetResponse
}

#[verifier(inline)]
pub open spec fn is_some_k_create_resp_view(resp_o: DefaultResp) -> bool {
    resp_o is Some && resp_o->0 is KResponse && resp_o->0->KResponse_0 is CreateResponse
}

#[verifier(inline)]
pub open spec fn is_some_k_update_resp_view(resp_o: DefaultResp) -> bool {
    resp_o is Some && resp_o->0 is KResponse && resp_o->0->KResponse_0 is UpdateResponse
}

#[verifier(inline)]
pub open spec fn is_some_k_list_resp_view(resp_o: DefaultResp) -> bool {
    resp_o is Some && resp_o->0 is KResponse && resp_o->0->KResponse_0 is ListResponse
}

#[verifier(inline)]
pub open spec fn is_some_k_delete_resp_view(resp_o: DefaultResp) -> bool {
    resp_o is Some && resp_o->0 is KResponse && resp_o->0->KResponse_0 is DeleteResponse
}

#[verifier(inline)]
pub open spec fn is_some_k_get_then_update_resp_view(resp_o: DefaultResp) -> bool {
    resp_o is Some && resp_o->0 is KResponse && resp_o->0->KResponse_0 is GetThenUpdateResponse
}

#[verifier(inline)]
pub open spec fn is_some_k_update_status_resp_view(resp_o: DefaultResp) -> bool {
    resp_o is Some && resp_o->0 is KResponse && resp_o->0->KResponse_0 is UpdateStatusResponse
}

#[verifier(inline)]
pub open spec fn is_some_k_get_then_delete_resp_view(resp_o: DefaultResp) -> bool {
    resp_o is Some && resp_o->0 is KResponse && resp_o->0->KResponse_0 is GetThenDeleteResponse
}

// should be called only when is_some_k_get_resp_view holds
#[verifier(inline)]
pub open spec fn extract_some_k_get_resp_view(resp_o: DefaultResp) -> Result<DynamicObjectView, APIError> {
    resp_o->0->KResponse_0->GetResponse_0.res
}

// should be called only when is_some_k_create_resp_view holds
#[verifier(inline)]
pub open spec fn extract_some_k_create_resp_view(resp_o: DefaultResp) -> Result<DynamicObjectView, APIError> {
    resp_o->0->KResponse_0->CreateResponse_0.res
}

// should be called only when is_some_k_update_resp_view holds
#[verifier(inline)]
pub open spec fn extract_some_k_update_resp_view(resp_o: DefaultResp) -> Result<DynamicObjectView, APIError> {
    resp_o->0->KResponse_0->UpdateResponse_0.res
}

// should be called only when is_some_k_update_status_resp_view holds
#[verifier(inline)]
pub open spec fn extract_some_k_update_status_resp_view(resp_o: DefaultResp) -> Result<DynamicObjectView, APIError> {
    resp_o->0->KResponse_0->UpdateStatusResponse_0.res
}

// should be called only when is_some_k_list_resp_view holds
#[verifier(inline)]
pub open spec fn extract_some_k_list_resp_view(resp_o: DefaultResp) -> Result<Seq<DynamicObjectView>, APIError> {
    resp_o->0->KResponse_0->ListResponse_0.res
}

// should be called only when is_some_k_delete_resp_view holds
#[verifier(inline)]
pub open spec fn extract_some_k_delete_resp_view(resp_o: DefaultResp) -> Result<(), APIError> {
    resp_o->0->KResponse_0->DeleteResponse_0.res
}

// should be called only when is_some_k_get_then_update_resp_view holds
#[verifier(inline)]
pub open spec fn extract_some_k_get_then_update_resp_view(resp_o: DefaultResp) -> Result<DynamicObjectView, APIError> {
    resp_o->0->KResponse_0->GetThenUpdateResponse_0.res
}

// should be called only when is_some_k_get_then_delete_resp_view holds
#[verifier(inline)]
pub open spec fn extract_some_k_get_then_delete_resp_view(resp_o: DefaultResp) -> Result<(), APIError> {
    resp_o->0->KResponse_0->GetThenDeleteResponse_0.res
}

}
