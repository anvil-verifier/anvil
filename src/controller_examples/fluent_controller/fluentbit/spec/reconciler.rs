// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::common::*;
use crate::fluent_controller::fluentbit::spec::types::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, container::*, daemon_set::*, dynamic::*,
    label_selector::*, object_meta::*, persistent_volume_claim::*, pod::*, pod_template_spec::*,
    resource::*, role::*, role_binding::*, secret::*, service::*, service_account::*, volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_view::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct FluentBitReconcileState {
    pub reconcile_step: FluentBitReconcileStep,
}

pub struct FluentBitReconciler {}

impl Reconciler<FluentBitView, EmptyAPI> for FluentBitReconciler {
    type T = FluentBitReconcileState;

    open spec fn reconcile_init_state() -> FluentBitReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(
        fb: FluentBitView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitReconcileState
    ) -> (FluentBitReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(fb, resp_o, state)
    }

    open spec fn reconcile_done(state: FluentBitReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: FluentBitReconcileState) -> bool {
        reconcile_error(state)
    }

    open spec fn expect_from_user(obj: DynamicObjectView) -> bool {
        obj.kind == SecretView::kind() // expect the user might create some secret object
    }
}

pub open spec fn reconcile_init_state() -> FluentBitReconcileState {
    FluentBitReconcileState {
        reconcile_step: FluentBitReconcileStep::Init,
    }
}

pub open spec fn reconcile_done(state: FluentBitReconcileState) -> bool {
    match state.reconcile_step {
        FluentBitReconcileStep::Done => true,
        _ => false,
    }
}

pub open spec fn reconcile_error(state: FluentBitReconcileState) -> bool {
    match state.reconcile_step {
        FluentBitReconcileStep::Error => true,
        _ => false,
    }
}

pub open spec fn reconcile_core(
    fb: FluentBitView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitReconcileState
) -> (FluentBitReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        fb.well_formed(),
{
    let step = state.reconcile_step;
    let resp = resp_o.get_Some_0();
    let fb_name = fb.metadata.name.get_Some_0();
    let fb_namespace = fb.metadata.namespace.get_Some_0();
    match step{
        FluentBitReconcileStep::Init => {
            let req_o = APIRequest::GetRequest(GetRequest{
                key: ObjectRef {
                    kind: SecretView::kind(),
                    name: fb.spec.fluentbit_config_name,
                    namespace: fb.metadata.namespace.get_Some_0(),
                }
            });
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterGetSecret,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        FluentBitReconcileStep::AfterGetSecret => {
            if resp_o.is_Some() && resp_o.get_Some_0().is_KResponse()
            && resp_o.get_Some_0().get_KResponse_0().is_GetResponse() {
                let get_secret_resp = resp_o.get_Some_0().get_KResponse_0().get_GetResponse_0().res;
                if get_secret_resp.is_Ok() {
                    let req_o = APIRequest::GetRequest(GetRequest {
                        key: make_role_key(fb.object_ref()),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterGetRole,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterGetRole => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_role_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                let unmarshal_role_result = RoleView::unmarshal(get_role_resp.get_Ok_0());
                if get_role_resp.is_Ok() {
                    if unmarshal_role_result.is_Ok() {
                        // update
                        let found_role = unmarshal_role_result.get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            namespace: fb_namespace,
                            name: make_role_name(fb_name),
                            obj: update_role(fb, found_role).marshal(),
                        });
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::AfterUpdateRole,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_role_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: fb_namespace,
                        obj: make_role(fb).marshal(),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterCreateRole,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterCreateRole => {
            let create_role_resp = resp.get_KResponse_0().get_CreateResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_CreateResponse()
            && create_role_resp.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: make_service_account_key(fb.object_ref()),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetServiceAccount,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterUpdateRole => {
            let update_role_resp = resp.get_KResponse_0().get_UpdateResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateResponse()
            && update_role_resp.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: make_service_account_key(fb.object_ref()),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetServiceAccount,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterGetServiceAccount => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_service_account_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                let unmarshal_service_account_result = ServiceAccountView::unmarshal(get_service_account_resp.get_Ok_0());
                if get_service_account_resp.is_Ok() {
                    if unmarshal_service_account_result.is_Ok() {
                        // update
                        let found_service_account = unmarshal_service_account_result.get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            namespace: fb_namespace,
                            name: make_service_account_name(fb_name),
                            obj: update_service_account(fb, found_service_account).marshal(),
                        });
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::AfterUpdateServiceAccount,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_service_account_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: fb_namespace,
                        obj: make_service_account(fb).marshal(),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterCreateServiceAccount,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterCreateServiceAccount => {
            let create_service_account_resp = resp.get_KResponse_0().get_CreateResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_CreateResponse()
            && create_service_account_resp.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: make_role_binding_key(fb.object_ref()),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetRoleBinding,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterUpdateServiceAccount => {
            let update_service_account_resp = resp.get_KResponse_0().get_UpdateResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateResponse()
            && update_service_account_resp.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: make_role_binding_key(fb.object_ref()),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetRoleBinding,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterGetRoleBinding => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_role_binding_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                let unmarshal_role_binding_result = RoleBindingView::unmarshal(get_role_binding_resp.get_Ok_0());
                if get_role_binding_resp.is_Ok() {
                    if unmarshal_role_binding_result.is_Ok() {
                        // update
                        let found_role_binding = unmarshal_role_binding_result.get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            namespace: fb_namespace,
                            name: make_role_binding_name(fb_name),
                            obj: update_role_binding(fb, found_role_binding).marshal(),
                        });
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::AfterUpdateRoleBinding,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_role_binding_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: fb_namespace,
                        obj: make_role_binding(fb).marshal(),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterCreateRoleBinding,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterCreateRoleBinding => {
            let create_role_binding_resp = resp.get_KResponse_0().get_CreateResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_CreateResponse()
            && create_role_binding_resp.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: make_daemon_set_key(fb.object_ref()),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetDaemonSet,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterUpdateRoleBinding => {
            let update_role_binding_resp = resp.get_KResponse_0().get_UpdateResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateResponse()
            && update_role_binding_resp.is_Ok() {
                let req_o = APIRequest::GetRequest(GetRequest {
                    key: make_daemon_set_key(fb.object_ref()),
                });
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::AfterGetDaemonSet,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req_o)))
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterGetDaemonSet => {
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_GetResponse() {
                let get_daemon_set_resp = resp.get_KResponse_0().get_GetResponse_0().res;
                let unmarshal_daemon_set_result = DaemonSetView::unmarshal(get_daemon_set_resp.get_Ok_0());
                if get_daemon_set_resp.is_Ok() {
                    if unmarshal_daemon_set_result.is_Ok() && unmarshal_daemon_set_result.get_Ok_0().spec.is_Some() {
                        // update
                        let found_daemon_set = unmarshal_daemon_set_result.get_Ok_0();
                        let req_o = APIRequest::UpdateRequest(UpdateRequest {
                            namespace: fb_namespace,
                            name: make_daemon_set_name(fb_name),
                            obj: update_daemon_set(fb, found_daemon_set).marshal(),
                        });
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::AfterUpdateDaemonSet,
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req_o)))
                    } else {
                        let state_prime = FluentBitReconcileState {
                            reconcile_step: FluentBitReconcileStep::Error,
                            ..state
                        };
                        (state_prime, None)
                    }
                } else if get_daemon_set_resp.get_Err_0().is_ObjectNotFound() {
                    // create
                    let req_o = APIRequest::CreateRequest(CreateRequest {
                        namespace: fb_namespace,
                        obj: make_daemon_set(fb).marshal(),
                    });
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::AfterCreateDaemonSet,
                        ..state
                    };
                    (state_prime, Some(RequestView::KRequest(req_o)))
                } else {
                    let state_prime = FluentBitReconcileState {
                        reconcile_step: FluentBitReconcileStep::Error,
                        ..state
                    };
                    (state_prime, None)
                }
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterCreateDaemonSet => {
            let create_daemon_set_resp = resp.get_KResponse_0().get_CreateResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_CreateResponse()
            && create_daemon_set_resp.is_Ok() {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        FluentBitReconcileStep::AfterUpdateDaemonSet => {
            let update_daemon_set_resp = resp.get_KResponse_0().get_UpdateResponse_0().res;
            if resp_o.is_Some() && resp.is_KResponse() && resp.get_KResponse_0().is_UpdateResponse()
            && update_daemon_set_resp.is_Ok() {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                let state_prime = FluentBitReconcileState {
                    reconcile_step: FluentBitReconcileStep::Error,
                    ..state
                };
                (state_prime, None)
            }
        },
        _ => {
            let state_prime = FluentBitReconcileState {
                reconcile_step: step,
                ..state
            };
            (state_prime, None)
        }
    }
}

pub open spec fn reconcile_error_result(state: FluentBitReconcileState) -> (FluentBitReconcileState, Option<APIRequest>) {
    let state_prime = FluentBitReconcileState {
        reconcile_step: FluentBitReconcileStep::Error,
        ..state
    };
    let req_o = None;
    (state_prime, req_o)
}

pub open spec fn make_base_labels(fb: FluentBitView) -> Map<StringView, StringView> {
    map![new_strlit("app")@ => fb.metadata.name.get_Some_0()]
}

pub open spec fn make_labels(fb: FluentBitView) -> Map<StringView, StringView> {
    fb.spec.labels.union_prefer_right(make_base_labels(fb))
}

pub open spec fn make_role_name(fb_name: StringView) -> StringView {
    fb_name + new_strlit("-role")@
}

pub open spec fn make_role_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: RoleView::kind(),
        name: make_role_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn update_role(fb: FluentBitView, found_role: RoleView) -> RoleView
    recommends
        fb.well_formed(),
{
    RoleView {
        metadata: ObjectMetaView {
            labels: make_role(fb).metadata.labels,
            annotations: make_role(fb).metadata.annotations,
            ..found_role.metadata
        },
        ..found_role
    }
}

pub open spec fn make_role(fb: FluentBitView) -> RoleView
    recommends
        fb.well_formed(),
{
    RoleView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_role_name(fb.metadata.name.get_Some_0()))
            .set_labels(make_labels(fb))
            .set_annotations(fb.spec.annotations)
            .set_owner_references(seq![fb.controller_owner_ref()])
        ).set_policy_rules(
            seq![
                PolicyRuleView::default()
                    .set_api_groups(seq![new_strlit("")@])
                    .set_resources(seq![new_strlit("pods")@])
                    .set_verbs(seq![new_strlit("get")@])
            ]
        )
}

pub open spec fn make_service_account_name(fb_name: StringView) -> StringView {
    fb_name
}

pub open spec fn make_service_account_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: ServiceAccountView::kind(),
        name: make_service_account_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn update_service_account(fb: FluentBitView, found_service_account: ServiceAccountView) -> ServiceAccountView
    recommends
        fb.well_formed(),
{
    ServiceAccountView {
        metadata: ObjectMetaView {
            labels: make_service_account(fb).metadata.labels,
            annotations: make_service_account(fb).metadata.annotations,
            ..found_service_account.metadata
        },
        ..found_service_account
    }
}

pub open spec fn make_service_account(fb: FluentBitView) -> ServiceAccountView
    recommends
        fb.well_formed(),
{
    ServiceAccountView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_service_account_name(fb.metadata.name.get_Some_0()))
            .set_labels(make_labels(fb))
            .set_annotations(fb.spec.annotations)
            .set_owner_references(seq![fb.controller_owner_ref()])
        )
}

pub open spec fn make_role_binding_name(fb_name: StringView) -> StringView {
    fb_name + new_strlit("-role-binding")@
}

pub open spec fn make_role_binding_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: RoleBindingView::kind(),
        name: make_role_binding_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn update_role_binding(fb: FluentBitView, found_role_binding: RoleBindingView) -> RoleBindingView
    recommends
        fb.well_formed(),
{
    RoleBindingView {
        metadata: ObjectMetaView {
            labels: make_role_binding(fb).metadata.labels,
            annotations: make_role_binding(fb).metadata.annotations,
            ..found_role_binding.metadata
        },
        ..found_role_binding
    }
}

pub open spec fn make_role_binding(fb: FluentBitView) -> RoleBindingView
    recommends
        fb.well_formed(),
{
    RoleBindingView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_role_binding_name(fb.metadata.name.get_Some_0()))
            .set_labels(make_labels(fb))
            .set_annotations(fb.spec.annotations)
            .set_owner_references(seq![fb.controller_owner_ref()])
        ).set_role_ref(RoleRefView::default()
            .set_api_group(new_strlit("rbac.authorization.k8s.io")@)
            .set_kind(new_strlit("Role")@)
            .set_name(make_role_name(fb.metadata.name.get_Some_0()))
        ).set_subjects(seq![SubjectView::default()
            .set_kind(new_strlit("ServiceAccount")@)
            .set_name(make_service_account_name(fb.metadata.name.get_Some_0()))
            .set_namespace(fb.metadata.namespace.get_Some_0())
        ])
}

pub open spec fn make_daemon_set_name(fb_name: StringView) -> StringView {
    fb_name
}

pub open spec fn make_daemon_set_key(key: ObjectRef) -> ObjectRef
    recommends
        key.kind.is_CustomResourceKind(),
{
    ObjectRef {
        kind: DaemonSetView::kind(),
        name: make_daemon_set_name(key.name),
        namespace: key.namespace,
    }
}

pub open spec fn update_daemon_set(fb: FluentBitView, found_daemon_set: DaemonSetView) -> DaemonSetView
    recommends
        fb.well_formed(),
{
    DaemonSetView {
        metadata: ObjectMetaView {
            labels: make_daemon_set(fb).metadata.labels,
            annotations: make_daemon_set(fb).metadata.annotations,
            ..found_daemon_set.metadata
        },
        spec: Some(DaemonSetSpecView {
            template: make_daemon_set(fb).spec.get_Some_0().template,
            ..found_daemon_set.spec.get_Some_0()
        }),
        ..found_daemon_set
    }
}

pub open spec fn make_daemon_set(fb: FluentBitView) -> DaemonSetView
    recommends
        fb.well_formed(),
{
    DaemonSetView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_daemon_set_name(fb.metadata.name.get_Some_0()))
            .set_labels(make_labels(fb))
            .set_annotations(fb.spec.annotations)
            .set_owner_references(seq![fb.controller_owner_ref()])
        ).set_spec(DaemonSetSpecView::default()
            .set_selector(LabelSelectorView::default().set_match_labels(make_base_labels(fb)))
            .set_template(PodTemplateSpecView::default()
                .set_metadata(ObjectMetaView::default()
                    .set_labels(make_labels(fb))
                    .set_annotations(fb.spec.annotations)
                )
                .set_spec(make_fluentbit_pod_spec(fb))
            )
        )
}

pub open spec fn make_fluentbit_pod_spec(fb: FluentBitView) -> PodSpecView
    recommends
        fb.well_formed(),
{
    PodSpecView {
        service_account_name: Some(make_service_account_name(fb.metadata.name.get_Some_0())),
        volumes: Some(seq![
            VolumeView::default()
                .set_name(new_strlit("varlibcontainers")@)
                .set_host_path(HostPathVolumeSourceView::default()
                    .set_path(new_strlit("/containers")@)
                ),
            VolumeView::default()
                .set_name(new_strlit("config")@)
                .set_secret(SecretVolumeSourceView::default()
                    .set_secret_name(fb.spec.fluentbit_config_name)
                ),
            VolumeView::default()
                .set_name(new_strlit("varlogs")@)
                .set_host_path(HostPathVolumeSourceView::default()
                    .set_path(new_strlit("/var/log")@)
                ),
            VolumeView::default()
                .set_name(new_strlit("systemd")@)
                .set_host_path(HostPathVolumeSourceView::default()
                    .set_path(new_strlit("/var/log/journal")@)
                ),
            VolumeView::default()
                .set_name(new_strlit("positions")@)
                .set_host_path(HostPathVolumeSourceView::default()
                    .set_path(new_strlit("/var/lib/fluent-bit/")@)
                ),
        ]),
        containers: seq![
            ContainerView {
                name: new_strlit("fluent-bit")@,
                image: Some(new_strlit("kubesphere/fluent-bit:v2.1.7")@),
                env: Some(make_env(fb)),
                volume_mounts: Some(seq![
                    VolumeMountView::default()
                        .set_name(new_strlit("varlibcontainers")@)
                        .set_read_only(true)
                        .set_mount_path(new_strlit("/containers")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("config")@)
                        .set_read_only(true)
                        .set_mount_path(new_strlit("/fluent-bit/config")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("varlogs")@)
                        .set_read_only(true)
                        .set_mount_path(new_strlit("/var/log/")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("systemd")@)
                        .set_read_only(true)
                        .set_mount_path(new_strlit("/var/log/journal")@),
                    VolumeMountView::default()
                        .set_name(new_strlit("positions")@)
                        .set_mount_path(new_strlit("/fluent-bit/tail")@),
                ]),
                ports: Some(seq![
                    ContainerPortView::default()
                        .set_name(new_strlit("metrics")@)
                        .set_container_port(2020),
                ]),
                resources: fb.spec.resources,
                ..ContainerView::default()
            }
        ],
        tolerations: fb.spec.tolerations,
        ..PodSpecView::default()
    }
}

pub open spec fn make_env(fluentbit: FluentBitView) -> Seq<EnvVarView> {
    seq![
        EnvVarView {
            name: new_strlit("NODE_NAME")@,
            value_from: Some(EnvVarSourceView {
                field_ref: Some(ObjectFieldSelectorView {
                    field_path: new_strlit("spec.nodeName")@,
                    ..ObjectFieldSelectorView::default()
                }),
                ..EnvVarSourceView::default()
            }),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: new_strlit("HOST_IP")@,
            value_from: Some(EnvVarSourceView {
                field_ref: Some(ObjectFieldSelectorView {
                    field_path: new_strlit("status.hostIP")@,
                    ..ObjectFieldSelectorView::default()
                }),
                ..EnvVarSourceView::default()
            }),
            ..EnvVarView::default()
        },
    ]
}

}
