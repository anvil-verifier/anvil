// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::exec::api_method::*;
use crate::reconciler::exec::io::*;
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus! {

pub trait Reconciler{
    type R;
    type T;
    type ExternalAPIType: ExternalAPIShimLayer;
    spec fn well_formed(cr: &Self::R) -> bool;
    fn reconcile_init_state() -> Self::T;
    fn reconcile_core(cr: &Self::R, resp_o: Option<Response<<Self::ExternalAPIType as ExternalAPIShimLayer>::Output>>, state: Self::T) -> (Self::T, Option<Request<<Self::ExternalAPIType as ExternalAPIShimLayer>::Input>>)
        requires Self::well_formed(cr);
    fn reconcile_done(state: &Self::T) -> bool;
    fn reconcile_error(state: &Self::T) -> bool;
}

// pub open spec fn resource_version_check<I, O>(prev_resp_opt: Option<ResponseView<O>>, cur_req_opt: Option<RequestView<I>>) -> bool {
//     cur_req_opt.is_Some() && cur_req_opt.get_Some_0().is_k_update_request()
//     ==> prev_resp_opt.is_Some() && resource_version_check_helper(prev_resp_opt.get_Some_0(), cur_req_opt.get_Some_0())
// }

// pub open spec fn resource_version_check_helper<I, O>(prev_resp: ResponseView<O>, cur_req: RequestView<I>) -> bool {
//     let prev_get_resp = prev_resp.get_k_get_response();
//     let found_obj = prev_get_resp.res.get_Ok_0();
//     let cur_update_req = cur_req.get_k_update_request();
//     let obj_to_update = cur_update_req.obj;
//     cur_req.is_k_update_request()
//     ==> prev_resp.is_k_get_response()
//         && prev_get_resp.res.is_Ok()
//         && found_obj.kind == obj_to_update.kind
//         && found_obj.metadata.name == obj_to_update.metadata.name
//         && found_obj.metadata.namespace == obj_to_update.metadata.namespace
//         && found_obj.metadata.resource_version == obj_to_update.metadata.resource_version
// }

}
