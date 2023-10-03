// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit_config::common::*;
use crate::fluent_controller::fluentbit_config::spec::types::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, daemon_set::*, dynamic::*, label_selector::*,
    object_meta::*, owner_reference::*, persistent_volume_claim::*, pod::*, pod_template_spec::*,
    resource::*, role::*, role_binding::*, secret::*, service::*, service_account::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct FluentBitConfigReconcileState {
    pub reconcile_step: FluentBitConfigReconcileStep,
}

pub struct FluentBitConfigReconciler {}

impl Reconciler<FluentBitConfigView, EmptyAPI> for FluentBitConfigReconciler {
    type T = FluentBitConfigReconcileState;

    open spec fn reconcile_init_state() -> FluentBitConfigReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(
        fbc: FluentBitConfigView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitConfigReconcileState
    ) -> (FluentBitConfigReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(fbc, resp_o, state)
    }

    open spec fn reconcile_done(state: FluentBitConfigReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: FluentBitConfigReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool {
        false // Don't expect anything from the user except the cr object
    }
}

pub open spec fn reconcile_init_state() -> FluentBitConfigReconcileState {
    FluentBitConfigReconcileState {
        reconcile_step: FluentBitConfigReconcileStep::Init,
    }
}

pub open spec fn reconcile_done(state: FluentBitConfigReconcileState) -> bool {
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: FluentBitConfigReconcileState) -> bool {
    match state.reconcile_step {
        FluentBitConfigReconcileStep::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(
    fbc: FluentBitConfigView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitConfigReconcileState
) -> (FluentBitConfigReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        fbc.well_formed(),
{
    let step = state.reconcile_step;
    let resp = resp_o.get_Some_0();
    let fbc_name = fbc.metadata.name.get_Some_0();
    let fbc_namespace = fbc.metadata.namespace.get_Some_0();
    match step{
        FluentBitConfigReconcileStep::Init => {
            let req_o = APIRequest::GetRequest(GetRequest {
                key: make_secret_key(fbc.object_ref()),
            });
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: FluentBitConfigReconcileStep::AfterGetSecret,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        FluentBitConfigReconcileStep::AfterGetSecret => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_secret_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                let unmarshal_secret_result = SecretView::unmarshal(get_secret_resp.get_Ok_0());
                if get_secret_resp.is_Ok() {
                    if unmarshal_secret_result.is_Ok() {
                        // update
                        let found_secret = unmarshal_secret_result.get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            namespace: fbc_namespace,
                            name: make_secret_name(fbc_name),
                            obj: update_secret(fbc, found_secret).marshal(),
                        });
                        let state_prime = FluentBitConfigReconcileState {
                            reconcile_step: FluentBitConfigReconcileStep::AfterUpdateSecret,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = FluentBitConfigReconcileState {
                            reconcile_step: FluentBitConfigReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_secret_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: fbc_namespace,
                        obj: make_secret(fbc).marshal(),
                    });
                    let state_prime = FluentBitConfigReconcileState {
                        reconcile_step: FluentBitConfigReconcileStep::AfterCreateSecret,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = FluentBitConfigReconcileState {
                        reconcile_step: FluentBitConfigReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = FluentBitConfigReconcileState {
                    reconcile_step: FluentBitConfigReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitConfigReconcileStep::AfterCreateSecret => {
            let create_secret_resp = resp.get_KResponse_0().get_CreateResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_CreateResponse()
            && create_secret_resp.is_Ok() {
                let state_prime = FluentBitConfigReconcileState {
                    reconcile_step: FluentBitConfigReconcileStep::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                let state_prime = FluentBitConfigReconcileState {
                    reconcile_step: FluentBitConfigReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitConfigReconcileStep::AfterUpdateSecret => {
            let update_secret_resp = resp.get_KResponse_0().get_UpdateResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateResponse()
            && update_secret_resp.is_Ok() {
                let state_prime = FluentBitConfigReconcileState {
                    reconcile_step: FluentBitConfigReconcileStep::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                let state_prime = FluentBitConfigReconcileState {
                    reconcile_step: FluentBitConfigReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        _ => {
            let state_prime = FluentBitConfigReconcileState {
                reconcile_step: step,
                ..state
            };
            (state_prime, None)
        }
    }
}

pub open spec fn reconcile_error_result(state: FluentBitConfigReconcileState) -> (FluentBitConfigReconcileState, Option<APIRequest>) {
    let state_prime = FluentBitConfigReconcileState {
        reconcile_step: FluentBitConfigReconcileStep::Error,
        ..state
    };
    let req_o = None;
    (state_prime, req_o)
}

pub open spec fn make_owner_references(fbc: FluentBitConfigView) -> Seq<OwnerReferenceView> {
    seq![fbc.controller_owner_ref()]
}


pub open spec fn make_secret_name(fbc_name: StringView) -> StringView {
    fbc_name
}

pub open spec fn make_secret_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: SecretView::kind(),
        name: make_secret_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn make_secret(fbc: FluentBitConfigView) -> SecretView
    recommends
        fbc.well_formed(),
{
    SecretView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_secret_name(fbc.metadata.name.get_Some_0()))
            .set_owner_references(make_owner_references(fbc))
        ).set_data(Map::empty()
            .insert(new_strlit("fluent-bit.conf")@, fbc.spec.fluentbit_config)
            .insert(new_strlit("parsers.conf")@, fbc.spec.parsers_config)
        )
}

pub open spec fn update_secret(fbc: FluentBitConfigView, found_secret: SecretView) -> SecretView
    recommends
        fbc.well_formed(),
{
    SecretView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(fbc)),
            finalizers: None,
            ..found_secret.metadata
        },
        data: Some(Map::empty()
            .insert(new_strlit("fluent-bit.conf")@, fbc.spec.fluentbit_config)
            .insert(new_strlit("parsers.conf")@, fbc.spec.parsers_config)
        ),
        ..found_secret
    }
}

}
