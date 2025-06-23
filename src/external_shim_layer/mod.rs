// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::reconciler::exec::io::{VoidEReq, VoidEResp};

// A trait for the external api of a reconciler, whose core is a transition method, and the developer should wrap all
// possible operations they may need in the function.
// Input is the input type of the external api and also the ? of Request<?> of the reconciler, i.e., it completes the
// request type of a reconciler.
// Similarly, Output is the output type of the external api, which composes the Response<?> type of a reconciler.
// Note that we can encapsulate all the required libraries here, so each reconciler only has one ExternalAPI type.
pub trait ExternalShimLayer<EReq, EResp> {
    fn external_call(req: EReq) -> EResp;
}

// An empty library that implements External Library.
// This can be used by those controllers that don't rely on a third-party library.
pub struct VoidExternalShimLayer {}

impl ExternalShimLayer<VoidEReq, VoidEResp> for VoidExternalShimLayer {
    fn external_call(_input: VoidEReq) -> VoidEResp {
        panic!("This should not be visited");
    }
}
