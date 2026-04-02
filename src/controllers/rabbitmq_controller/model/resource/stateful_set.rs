// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*, volume_resource_requirements::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::rabbitmq_controller::model::resource::config_map::make_server_config_map_key;
use crate::rabbitmq_controller::trusted::spec_types::*;
use crate::rabbitmq_controller::trusted::step::*;
use crate::rabbitmq_controller::trusted::liveness_theorem::make_rabbitmq_pod_spec;
use crate::vstatefulset_controller::trusted::spec_types::{VStatefulSetView, VStatefulSetSpecView};
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct StatefulSetBuilder {}

impl ResourceBuilder<RabbitmqClusterView, RabbitmqReconcileState> for StatefulSetBuilder {
    open spec fn get_request(rabbitmq: RabbitmqClusterView) -> GetRequest {
        GetRequest { key: make_stateful_set_key(rabbitmq) }
    }

    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<DynamicObjectView, ()> {
        if state.latest_config_map_rv_opt is Some {
            Ok(make_stateful_set(rabbitmq, state.latest_config_map_rv_opt->0).marshal())
        } else {
            Err(())
        }
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let sts = VStatefulSetView::unmarshal(obj);
        let found_sts = sts->Ok_0;
        if sts is Ok && found_sts.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
        && state.latest_config_map_rv_opt is Some {
            Ok(update_stateful_set(rabbitmq, found_sts, state.latest_config_map_rv_opt->0).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let sts = VStatefulSetView::unmarshal(obj);
        if sts is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(rabbitmq: RabbitmqClusterView, obj: DynamicObjectView, state: RabbitmqReconcileState) -> (res: Result<(RabbitmqReconcileState, Option<APIRequest>), ()>) {
        let sts = VStatefulSetView::unmarshal(obj);
        if sts is Ok {
            let state_prime = RabbitmqReconcileState {
                reconcile_step: RabbitmqReconcileStep::Done,
                ..state
            };
            Ok((state_prime, None))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_stateful_set_key(rabbitmq: RabbitmqClusterView) -> ObjectRef {
    ObjectRef {
        kind: VStatefulSetView::kind(),
        name: make_stateful_set_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace->0,
    }
}

pub open spec fn make_stateful_set_name(rabbitmq: RabbitmqClusterView) -> StringView { RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + rabbitmq.metadata.name->0 + "-server"@ }

pub open spec fn sts_restart_annotation() -> StringView { "anvil.dev/lastRestartAt"@ }

pub open spec fn update_stateful_set(rabbitmq: RabbitmqClusterView, found_stateful_set: VStatefulSetView, config_map_rv: StringView) -> VStatefulSetView {
    let made_spec = make_stateful_set(rabbitmq, config_map_rv).spec;
    VStatefulSetView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: make_stateful_set(rabbitmq, config_map_rv).metadata.labels,
            annotations: make_stateful_set(rabbitmq, config_map_rv).metadata.annotations,
            deletion_timestamp: None,
            ..found_stateful_set.metadata
        },
        spec: VStatefulSetSpecView {
            replicas: made_spec.replicas,
            template: made_spec.template,
            persistent_volume_claim_retention_policy: made_spec.persistent_volume_claim_retention_policy,
            ..found_stateful_set.spec
        },
        ..found_stateful_set
    }
}

pub open spec fn make_stateful_set(rabbitmq: RabbitmqClusterView, config_map_rv: StringView) -> VStatefulSetView {
    let name = rabbitmq.metadata.name->0;
    let sts_name = make_stateful_set_name(rabbitmq);
    let namespace = rabbitmq.metadata.namespace->0;

    let labels = Map::empty().insert("app"@, name);
    let metadata = ObjectMetaView::default()
        .with_name(sts_name)
        .with_namespace(namespace)
        .with_owner_references(make_owner_references(rabbitmq))
        .with_labels(make_labels(rabbitmq))
        .with_annotations(rabbitmq.spec.annotations);

    let spec = VStatefulSetSpecView {
        replicas: Some(rabbitmq.spec.replicas),
        service_name: RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + name + "-nodes"@,
        selector: LabelSelectorView::default().with_match_labels(labels),
        template: PodTemplateSpecView::default()
                    .with_metadata(
                        ObjectMetaView::default().with_labels(
                            make_labels(rabbitmq)
                        ).with_annotations(
                            rabbitmq.spec.annotations.insert(sts_restart_annotation(), config_map_rv)
                        )
                    )
                    .with_spec(make_rabbitmq_pod_spec(rabbitmq)),
        volume_claim_templates: Some({
            if rabbitmq.spec.persistence.storage == "0Gi"@ {
                seq![]
            } else {
                seq![
                    PersistentVolumeClaimView::default()
                        .with_metadata(ObjectMetaView::default()
                            .with_name("persistence"@)
                            .with_namespace(namespace)
                            .with_labels(labels)
                        )
                        .with_spec(PersistentVolumeClaimSpecView::default()
                            .with_access_modes(seq!["ReadWriteOnce"@])
                            .with_resources(VolumeResourceRequirementsView::default()
                                .with_requests(Map::empty()
                                    .insert("storage"@, rabbitmq.spec.persistence.storage)
                                )
                            )
                            .with_storage_class_name(rabbitmq.spec.persistence.storage_class_name)
                        )
                ]
            }
        }),
        pod_management_policy: Some(rabbitmq.spec.pod_management_policy),
        persistent_volume_claim_retention_policy: rabbitmq.spec.persistent_volume_claim_retention_policy,
        ..VStatefulSetSpecView::default()

    };

    VStatefulSetView::default().with_metadata(metadata).with_spec(spec)
}

pub open spec fn make_env_vars(rabbitmq: RabbitmqClusterView) -> Seq<EnvVarView> {
    seq![
        EnvVarView {
            name: "MY_POD_NAME"@,
            value_from: Some(EnvVarSourceView {
                field_ref: Some(ObjectFieldSelectorView{
                    api_version: Some("v1"@),
                    field_path: "metadata.name"@,
                    ..ObjectFieldSelectorView::default()
                }),
                ..EnvVarSourceView::default()
            }),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: "MY_POD_NAMESPACE"@,
            value_from: Some(EnvVarSourceView {
                field_ref: Some(ObjectFieldSelectorView{
                    api_version: Some("v1"@),
                    field_path: "metadata.namespace"@,
                    ..ObjectFieldSelectorView::default()
                }),
                ..EnvVarSourceView::default()
            }),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: "K8S_SERVICE_NAME"@,
            value:  Some(RabbitmqClusterView::kind()->CustomResourceKind_0 + "-"@ + rabbitmq.metadata.name->0 + "-nodes"@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: "RABBITMQ_ENABLED_PLUGINS_FILE"@,
            value: Some("/operator/enabled_plugins"@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: "RABBITMQ_USE_LONGNAME"@,
            value: Some("true"@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: "RABBITMQ_NODENAME"@,
            value: Some("rabbit@$(MY_POD_NAME).$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)"@),
            ..EnvVarView::default()
        },
        EnvVarView {
            name: "K8S_HOSTNAME_SUFFIX"@,
            value: Some(".$(K8S_SERVICE_NAME).$(MY_POD_NAMESPACE)"@),
            ..EnvVarView::default()
        },
    ]
}

}
