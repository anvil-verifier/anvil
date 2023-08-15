// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::common::*;
use crate::fluent_controller::fluentbit::spec::types::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, daemon_set::*, label_selector::*, object_meta::*,
    persistent_volume_claim::*, pod::*, pod_template_spec::*, resource::*, role::*,
    role_binding::*, secret::*, service::*, service_account::*,
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
        fluentbit: FluentBitView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitReconcileState
    ) -> (FluentBitReconcileState, Option<RequestView<EmptyTypeView>>) {
        reconcile_core(fluentbit, resp_o, state)
    }

    open spec fn reconcile_done(state: FluentBitReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: FluentBitReconcileState) -> bool {
        reconcile_error(state)
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
    fluentbit: FluentBitView, resp_o: Option<ResponseView<EmptyTypeView>>, state: FluentBitReconcileState
) -> (FluentBitReconcileState, Option<RequestView<EmptyTypeView>>)
    recommends
        fluentbit.metadata.name.is_Some(),
        fluentbit.metadata.namespace.is_Some(),
{
    let step = state.reconcile_step;
    match step{
        FluentBitReconcileStep::Init => {
            let req_o = APIRequest::GetRequest(GetRequest{
                key: ObjectRef {
                    kind: SecretView::kind(),
                    name: fluentbit.spec.fluentbit_config_name,
                    namespace: fluentbit.metadata.namespace.get_Some_0(),
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
                    let role = make_role(fluentbit);
                    let req_o = APIRequest::CreateRequest(CreateRequest{
                        namespace: fluentbit.metadata.namespace.get_Some_0(),
                        obj: role.to_dynamic_object(),
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
            let service_account = make_service_account(fluentbit);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: fluentbit.metadata.namespace.get_Some_0(),
                obj: service_account.to_dynamic_object(),
            });
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterCreateServiceAccount,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        FluentBitReconcileStep::AfterCreateServiceAccount => {
            let role_binding = make_role_binding(fluentbit);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: fluentbit.metadata.namespace.get_Some_0(),
                obj: role_binding.to_dynamic_object(),
            });
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterCreateRoleBinding,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        FluentBitReconcileStep::AfterCreateRoleBinding => {
            let daemon_set = make_daemon_set(fluentbit);
            let req_o = APIRequest::CreateRequest(CreateRequest{
                namespace: fluentbit.metadata.namespace.get_Some_0(),
                obj: daemon_set.to_dynamic_object(),
            });
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterCreateDaemonSet,
                ..state
            };
            (state_prime, Some(RequestView::KRequest(req_o)))
        },
        FluentBitReconcileStep::AfterCreateDaemonSet => {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::Done,
                ..state
            };
            (state_prime, None)
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

pub open spec fn make_role_name(fluentbit_name: StringView) -> StringView {
    fluentbit_name + new_strlit("-role")@
}

pub open spec fn make_role(fluentbit: FluentBitView) -> RoleView
    recommends
        fluentbit.metadata.name.is_Some(),
        fluentbit.metadata.namespace.is_Some(),
{
    RoleView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_role_name(fluentbit.metadata.name.get_Some_0()))
            .set_owner_references(seq![fluentbit.controller_owner_ref()])
        ).set_policy_rules(
            seq![
                PolicyRuleView::default()
                    .set_api_groups(seq![new_strlit("")@])
                    .set_resources(seq![new_strlit("pods")@])
                    .set_verbs(seq![new_strlit("get")@])
            ]
        )
}

pub open spec fn make_service_account_name(fluentbit_name: StringView) -> StringView {
    fluentbit_name
}

pub open spec fn make_service_account(fluentbit: FluentBitView) -> ServiceAccountView
    recommends
        fluentbit.metadata.name.is_Some(),
        fluentbit.metadata.namespace.is_Some(),
{
    ServiceAccountView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_service_account_name(fluentbit.metadata.name.get_Some_0()))
            .set_owner_references(seq![fluentbit.controller_owner_ref()])
        )
}

pub open spec fn make_role_binding_name(fluentbit_name: StringView) -> StringView {
    fluentbit_name + new_strlit("-role-binding")@
}

pub open spec fn make_role_binding(fluentbit: FluentBitView) -> RoleBindingView
    recommends
        fluentbit.metadata.name.is_Some(),
        fluentbit.metadata.namespace.is_Some(),
{
    RoleBindingView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_role_binding_name(fluentbit.metadata.name.get_Some_0()))
            .set_owner_references(seq![fluentbit.controller_owner_ref()])
        ).set_role_ref(RoleRefView::default()
            .set_api_group(new_strlit("rbac.authorization.k8s.io")@)
            .set_kind(new_strlit("Role")@)
            .set_name(make_role_name(fluentbit.metadata.name.get_Some_0()))
        ).set_subjects(seq![SubjectView::default()
            .set_kind(new_strlit("ServiceAccount")@)
            .set_name(make_service_account_name(fluentbit.metadata.name.get_Some_0()))
            .set_namespace(fluentbit.metadata.namespace.get_Some_0())
        ])
}

pub open spec fn make_daemon_set_name(fluentbit_name: StringView) -> StringView {
    fluentbit_name
}

pub open spec fn make_daemon_set(fluentbit: FluentBitView) -> DaemonSetView
    recommends
        fluentbit.metadata.name.is_Some(),
        fluentbit.metadata.namespace.is_Some(),
{
    let labels = Map::empty().insert(new_strlit("app")@, fluentbit.metadata.name.get_Some_0());
    DaemonSetView::default()
        .set_metadata(ObjectMetaView::default()
            .set_name(make_daemon_set_name(fluentbit.metadata.name.get_Some_0()))
            .set_labels(labels)
            .set_owner_references(seq![fluentbit.controller_owner_ref()])
        ).set_spec(DaemonSetSpecView::default()
            .set_selector(LabelSelectorView::default().set_match_labels(labels))
            .set_template(PodTemplateSpecView::default()
                .set_metadata(ObjectMetaView::default()
                    .set_labels(labels)
                )
                .set_spec(make_fluentbit_pod_spec(fluentbit))
            )
        )
}

pub open spec fn make_fluentbit_pod_spec(fluentbit: FluentBitView) -> PodSpecView
    recommends
        fluentbit.metadata.name.is_Some(),
        fluentbit.metadata.namespace.is_Some(),
{
    PodSpecView::default()
        .set_service_account_name(make_service_account_name(fluentbit.metadata.name.get_Some_0()))
        .set_volumes(seq![
            VolumeView::default()
                .set_name(new_strlit("varlibcontainers")@)
                .set_host_path(HostPathVolumeSourceView::default()
                    .set_path(new_strlit("/containers")@)
                ),
            VolumeView::default()
                .set_name(new_strlit("config")@)
                .set_secret(SecretVolumeSourceView::default()
                    .set_secret_name(fluentbit.spec.fluentbit_config_name)
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
        ])
        .set_containers(seq![
            ContainerView::default()
                .set_name(new_strlit("fluent-bit")@)
                .set_image(new_strlit("kubesphere/fluent-bit:v2.1.7")@)
                .set_volume_mounts(seq![
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
                ])
                .set_ports(seq![
                    ContainerPortView::default()
                        .set_name(new_strlit("metrics")@)
                        .set_container_port(2020),
                ])
                .set_resources(fluentbit.spec.resources)
        ])
}

}
