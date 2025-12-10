// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::types::*, cluster::Cluster, controller::types::*,
};
use crate::reconciler::spec::{io::*, reconciler::*};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn installed_type<T: CustomResourceView>() -> InstalledType {
    InstalledType {
        unmarshallable_spec: |v: Value| T::unmarshal_spec(v) is Ok,
        unmarshallable_status: |v: Value| T::unmarshal_status(v) is Ok,
        valid_object: |obj: DynamicObjectView| T::unmarshal(obj)->Ok_0.state_validation(),
        valid_transition: |obj, old_obj: DynamicObjectView| T::unmarshal(obj)->Ok_0.transition_validation(T::unmarshal(old_obj)->Ok_0),
        marshalled_default_status: || T::marshal_status(T::default().status()),
    }
}

pub open spec fn type_is_installed_in_cluster<T: CustomResourceView>(self) -> bool {
    let string = T::kind()->CustomResourceKind_0;
    &&& self.installed_types.contains_key(string)
    &&& self.installed_types[string] == Self::installed_type::<T>()
}

pub open spec fn installed_reconcile_model<R, S, K, EReq, EResp>() -> ReconcileModel
    where
        R: Reconciler<S, K, EReq, EResp>,
        K: CustomResourceView,
        S: Marshallable,
        EReq: Marshallable,
        EResp: Marshallable,
{
    ReconcileModel {
        kind: K::kind(),
        init: || R::reconcile_init_state().marshal(),
        transition: |obj, resp_o, s| {
            let obj_um = K::unmarshal(obj)->Ok_0;
            let resp_o_um = match resp_o {
                None => None,
                Some(resp) => Some(match resp {
                    ResponseContent::KubernetesResponse(api_resp) => ResponseView::<EResp>::KResponse(api_resp),
                    ResponseContent::ExternalResponse(ext_resp) => ResponseView::<EResp>::ExternalResponse(EResp::unmarshal(ext_resp)->Ok_0),
                })
            };
            let s_um = S::unmarshal(s)->Ok_0;
            let (s_prime_um, req_o_um) = R::reconcile_core(obj_um, resp_o_um, s_um);
            (s_prime_um.marshal(), match req_o_um {
                None => None,
                Some(req) => Some(match req {
                    RequestView::<EReq>::KRequest(api_req) => RequestContent::KubernetesRequest(api_req),
                    RequestView::<EReq>::ExternalRequest(ext_req) => RequestContent::ExternalRequest(ext_req.marshal()),
                })
            })
        },
        done: |s| R::reconcile_done(S::unmarshal(s)->Ok_0),
        error: |s| R::reconcile_error(S::unmarshal(s)->Ok_0),
    }
}

}

}
