// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{api_method::*, common::*};
use crate::reconciler::spec::io::*;
use vstd::{prelude::*, view::*};

verus! {

pub enum Receiver<T: View> {
    KubernetesAPI(KubeAPIRequest),
    // Third-party libraries can also receive requests from reconciler.
    // The developers must define all the possible receivers and
    ExternalReceiver(T),
}

#[is_variant]
pub enum Response<T: View> {
    KubernetesAPI(KubeAPIResponse),
    ExternalResponse(T),
}

impl <T: View> Response<T> {
    pub open spec fn to_view(&self) -> ResponseView<T::V> {
        match self {
            Response::KubernetesAPI(resp) => ResponseView::KubernetesAPI(resp.to_view()),
            Response::ExternalResponse(resp) => ResponseView::ExternalResponse(resp.view()),
        }
    }

    pub fn is_kubernetes_api(&self) -> (res: bool)
        ensures res <==> self.is_KubernetesAPI(),
    {
        match self {
            Response::KubernetesAPI(_) => true,
            _ => false,
        }
    }

    pub fn as_kubernetes_api_ref(&self) -> (resp: &KubeAPIResponse)
        requires
            self.is_KubernetesAPI(),
        ensures
            resp == self.get_KubernetesAPI_0(),
    {
        match self {
            Response::KubernetesAPI(resp) => resp,
            _ => unreached(),
        }
    }


    pub fn into_kubernetes_api(self) -> (resp: KubeAPIResponse)
        requires
            self.is_KubernetesAPI(),
        ensures
            resp == self.get_KubernetesAPI_0(),
    {
        match self {
            Response::KubernetesAPI(resp) => resp,
            _ => unreached(),
        }
    }
}

impl <T: View> Receiver<T> {
    pub open spec fn to_view(&self) -> ReceiverView<T::V> {
        match self {
            Receiver::KubernetesAPI(req) => ReceiverView::KubernetesAPI(req.to_view()),
            Receiver::ExternalReceiver(req) => ReceiverView::ExternalReceiver(req.view()),
        }
    }
}

pub open spec fn opt_response_to_view<T: View>(resp: &Option<Response<T>>) -> Option<ResponseView<T::V>> {
    match resp {
        Option::Some(resp) => Option::Some(resp.to_view()),
        Option::None => Option::None,
    }
}

pub open spec fn opt_receiver_to_view<T: View>(receiver: &Option<Receiver<T>>) -> Option<ReceiverView<T::V>> {
    match receiver {
        Option::Some(req) => Option::Some(req.to_view()),
        Option::None => Option::None,
    }
}

}
