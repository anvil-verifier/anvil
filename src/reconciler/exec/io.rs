// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*};
use crate::reconciler::spec::io::*;
use vstd::{prelude::*, view::*};

verus! {

pub enum Request<T: View> {
    KRequest(KubeAPIRequest),
    // Third-party libraries can also receive requests from reconciler.
    // The developers must define all the possible receivers and
    ExternalRequest(T),
}

#[is_variant]
pub enum Response<T: View> {
    KResponse(KubeAPIResponse),
    ExternalResponse(T),
}

impl <T: View> Response<T> {
    pub open spec fn to_view(&self) -> ResponseView<T::V> {
        match self {
            Response::KResponse(resp) => ResponseView::KResponse(resp.to_view()),
            Response::ExternalResponse(resp) => ResponseView::ExternalResponse(resp.view()),
        }
    }

    pub fn is_k_response(&self) -> (res: bool)
        ensures res <==> self.is_KResponse(),
    {
        match self {
            Response::KResponse(_) => true,
            _ => false,
        }
    }

    pub fn as_k_response_ref(&self) -> (resp: &KubeAPIResponse)
        requires
            self.is_KResponse(),
        ensures
            resp == self.get_KResponse_0(),
    {
        match self {
            Response::KResponse(resp) => resp,
            _ => unreached(),
        }
    }


    pub fn into_k_response(self) -> (resp: KubeAPIResponse)
        requires
            self.is_KResponse(),
        ensures
            resp == self.get_KResponse_0(),
    {
        match self {
            Response::KResponse(resp) => resp,
            _ => unreached(),
        }
    }
}

impl <T: View> Request<T> {
    pub open spec fn to_view(&self) -> RequestView<T::V> {
        match self {
            Request::KRequest(req) => RequestView::KRequest(req.to_view()),
            Request::ExternalRequest(req) => RequestView::ExternalRequest(req.view()),
        }
    }
}

pub open spec fn opt_response_to_view<T: View>(resp: &Option<Response<T>>) -> Option<ResponseView<T::V>> {
    match resp {
        Option::Some(resp) => Option::Some(resp.to_view()),
        Option::None => Option::None,
    }
}

pub open spec fn opt_receiver_to_view<T: View>(receiver: &Option<Request<T>>) -> Option<RequestView<T::V>> {
    match receiver {
        Option::Some(req) => Option::Some(req.to_view()),
        Option::None => Option::None,
    }
}

}
