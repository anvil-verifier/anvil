// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::exec::api_method::*;
use crate::reconciler::spec::io::*;
use vstd::{prelude::*, view::*};

use vstd::pervasive::unreached;

verus! {

// Third-party libraries can also receive requests from reconciler.
// T: The input type of the third-party library of the reconciler which should also be defined by the developer.
// Typically, T can be an enum type, which lists all the possible supporting handlings the developer need support from the
// third-party library on.
// Then in the process method of the library, th developers can do pattern matching to generate desired output which will
// then be sent to the reconciler in the next-round reconcile loop.
// In reconcile_core, if the reconciler want kubernetes to process the request, it should return a Request::KRequest;
// if it want the third-party library to deal with the request, it should return a Request::ExternalRequest.
pub enum Request<T: View> {
    KRequest(KubeAPIRequest),
    ExternalRequest(T),
}

// The response type should be consistent with the Request type.
// T: the output type of the third-party library of the reconciler which should be defined by the developer.
// A safe and common way is to have an enum type which has the corresponding types of the input type in the Request.
// Anyway, the process method in the ExternalAPI, the input type in Request, output type in Response and the handling
// of external response in reconcile_core are correlative.
// Developers have the freedom to define them in their own preferred way as long as they make them work well.
#[is_variant]
pub enum Response<T: View> {
    KResponse(KubeAPIResponse),
    ExternalResponse(T),
}

impl <T: View> View for Response<T> {
    type V = ResponseView<T::V>;

    open spec fn view(&self) -> ResponseView<T::V> {
        match self {
            Response::KResponse(resp) => ResponseView::KResponse(resp@),
            Response::ExternalResponse(resp) => ResponseView::ExternalResponse(resp@),
        }
    }

}

impl <T: View> Response<T> {
    pub fn is_external_response(&self) -> (res: bool)
        ensures res == self.is_ExternalResponse(),
    {
        match self {
            Response::ExternalResponse(_) => true,
            _ => false,
        }
    }

    pub fn as_external_response_ref(&self) -> (resp: &T)
        requires self.is_ExternalResponse(),
        ensures resp == self.get_ExternalResponse_0(),
    {
        match self {
            Response::ExternalResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn into_external_response(self) -> (resp: T)
        requires self.is_ExternalResponse(),
        ensures resp == self.get_ExternalResponse_0(),
    {
        match self {
            Response::ExternalResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn is_k_response(&self) -> (res: bool)
        ensures res == self.is_KResponse(),
    {
        match self {
            Response::KResponse(_) => true,
            _ => false,
        }
    }

    pub fn as_k_response_ref(&self) -> (resp: &KubeAPIResponse)
        requires self.is_KResponse(),
        ensures resp == self.get_KResponse_0(),
    {
        match self {
            Response::KResponse(resp) => resp,
            _ => unreached(),
        }
    }

    pub fn into_k_response(self) -> (resp: KubeAPIResponse)
        requires self.is_KResponse(),
        ensures resp == self.get_KResponse_0(),
    {
        match self {
            Response::KResponse(resp) => resp,
            _ => unreached(),
        }
    }
}

impl <T: View> View for Request<T> {
    type V = RequestView<T::V>;

    open spec fn view(&self) -> RequestView<T::V> {
        match self {
            Request::KRequest(req) => RequestView::KRequest(req@),
            Request::ExternalRequest(req) => RequestView::ExternalRequest(req@),
        }
    }
}

pub open spec fn opt_response_to_view<T: View>(resp: &Option<Response<T>>) -> Option<ResponseView<T::V>> {
    match resp {
        Some(resp) => Some(resp@),
        None => None,
    }
}

pub open spec fn opt_request_to_view<T: View>(request: &Option<Request<T>>) -> Option<RequestView<T::V>> {
    match request {
        Some(req) => Some(req@),
        None => None,
    }
}

}
