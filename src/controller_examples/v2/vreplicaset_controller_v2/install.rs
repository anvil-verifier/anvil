// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::external_api::spec::EmptyTypeView;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::spec::io::{RequestView, ResponseView};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::v2::kubernetes_cluster::spec::{
    api_server::types::InstalledType,
    cluster_state_machine::ControllerModel,
    controller::types::{ReconcileModel, RequestContent, ResponseContent},
    install_helpers::*,
    opaque::*,
};
use crate::v_replica_set_controller::model::reconciler::*;
use crate::v_replica_set_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

pub open spec fn vrs_installed_type() -> InstalledType {
    InstalledType {
        unmarshallable_spec: |v| {
            InstallTypeHelper::<VReplicaSetView>::unmarshal_spec(v)
        },
        unmarshallable_status: |v| {
            InstallTypeHelper::<VReplicaSetView>::unmarshal_status(v)
        },
        valid_object: |obj| {
            InstallTypeHelper::<VReplicaSetView>::valid_object(obj)
        },
        valid_transition: |obj, old_obj| {
            InstallTypeHelper::<VReplicaSetView>::valid_transition(obj, old_obj)
        },
        marshalled_default_status: || {
            InstallTypeHelper::<VReplicaSetView>::marshalled_default_status()
        }
    }
}

impl Marshallable for VReplicaSetReconcileState {
    spec fn marshal(self) -> Opaque;

    spec fn unmarshal(o: Opaque) -> Result<Self, ()>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()).is_Ok() && o == Self::unmarshal(o.marshal()).get_Ok_0()
    {}
}

impl Marshallable for EmptyTypeView {
    spec fn marshal(self) -> Opaque;

    spec fn unmarshal(o: Opaque) -> Result<Self, ()>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()).is_Ok() && o == Self::unmarshal(o.marshal()).get_Ok_0()
    {}
}

pub open spec fn vrs_reconcile_model() -> ReconcileModel {
    ReconcileModel {
        kind: VReplicaSetView::kind(),
        init: || VReplicaSetReconciler::reconcile_init_state().marshal(),
        transition: |obj, resp_o, s| {
            let obj_um = VReplicaSetView::unmarshal(obj).get_Ok_0();
            let resp_o_um = match resp_o {
                None => None,
                Some(resp) => Some(match resp {
                    ResponseContent::KubernetesResponse(api_resp) => ResponseView::<EmptyTypeView>::KResponse(api_resp),
                    ResponseContent::ExternalResponse(ext_resp) => ResponseView::<EmptyTypeView>::ExternalResponse(EmptyTypeView::unmarshal(ext_resp).get_Ok_0()),
                })
            };
            let s_um = VReplicaSetReconcileState::unmarshal(s).get_Ok_0();
            let (s_prime_um, req_o_um) = VReplicaSetReconciler::reconcile_core(obj_um, resp_o_um, s_um);
            (s_prime_um.marshal(), match req_o_um {
                None => None,
                Some(req) => Some(match req {
                    RequestView::<EmptyTypeView>::KRequest(api_req) => RequestContent::KubernetesRequest(api_req),
                    RequestView::<EmptyTypeView>::ExternalRequest(ext_req) => RequestContent::ExternalRequest(ext_req.marshal()),
                })
            })
        },
        done: |s| VReplicaSetReconciler::reconcile_done(VReplicaSetReconcileState::unmarshal(s).get_Ok_0()),
        error: |s| VReplicaSetReconciler::reconcile_error(VReplicaSetReconcileState::unmarshal(s).get_Ok_0()),
    }
}

pub open spec fn vrs_controller_model() -> ControllerModel {
    ControllerModel {
        reconcile_model: vrs_reconcile_model(),
        external_model: None,
    }
}

}
