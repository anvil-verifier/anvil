// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::fluent_controller::fluentbit::model::resource::{
    common::*, daemon_set::DaemonSetBuilder,
};
use crate::fluent_controller::fluentbit::trusted::{spec_types::*, step::*};
use crate::kubernetes_api_objects::spec::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::spec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ServiceBuilder {}

impl ResourceBuilder<FluentBitView, FluentBitReconcileState> for ServiceBuilder {
    open spec fn get_request(fb: FluentBitView) -> GetRequest {
        GetRequest { key: make_service_key(fb) }
    }

    open spec fn make(fb: FluentBitView, state: FluentBitReconcileState) -> Result<DynamicObjectView, ()> {
        Ok(make_service(fb).marshal())
    }

    open spec fn update(fb: FluentBitView, state: FluentBitReconcileState, obj: DynamicObjectView) -> Result<DynamicObjectView, ()> {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() && service.get_Ok_0().spec.is_Some() {
            Ok(update_service(fb, service.get_Ok_0()).marshal())
        } else {
            Err(())
        }
    }

    open spec fn state_after_create(fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::DaemonSet),
                ..state
            };
            let req = APIRequest::GetRequest(DaemonSetBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }

    open spec fn state_after_update(fb: FluentBitView, obj: DynamicObjectView, state: FluentBitReconcileState) -> (res: Result<(FluentBitReconcileState, Option<APIRequest>), ()>) {
        let service = ServiceView::unmarshal(obj);
        if service.is_Ok() {
            let state_prime = FluentBitReconcileState {
                reconcile_step: FluentBitReconcileStep::AfterKRequestStep(ActionKind::Get, SubResource::DaemonSet),
                ..state
            };
            let req = APIRequest::GetRequest(DaemonSetBuilder::get_request(fb));
            Ok((state_prime, Some(req)))
        } else {
            Err(())
        }
    }
}

pub open spec fn make_service_name(fb: FluentBitView) -> StringView { fb.metadata.name.get_Some_0() }

pub open spec fn make_service_key(fb: FluentBitView) -> ObjectRef {
    ObjectRef {
        kind: ServiceView::kind(),
        name: make_service_name(fb),
        namespace: fb.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_service(fb: FluentBitView, found_service: ServiceView) -> ServiceView {
    let made_service = make_service(fb);
    ServiceView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(fb)),
            finalizers: None,
            labels: made_service.metadata.labels,
            annotations: made_service.metadata.annotations,
            ..found_service.metadata
        },
        spec: Some(ServiceSpecView {
            ports: made_service.spec.get_Some_0().ports,
            selector: made_service.spec.get_Some_0().selector,
            ..found_service.spec.get_Some_0()
        }),
        ..found_service
    }
}

pub open spec fn make_service(fb: FluentBitView) -> ServiceView {
    ServiceView {
        metadata: ObjectMetaView {
            name: Some(make_service_name(fb)),
            owner_references: Some(make_owner_references(fb)),
            labels: if fb.spec.service_labels.len() > 0 { Some(fb.spec.service_labels) } else { Some(make_labels(fb)) },
            annotations: Some(fb.spec.service_annotations),
            ..ObjectMetaView::default()
        },
        spec: Some(ServiceSpecView {
            ports: {
                let metrics_port = ServicePortView {
                    name: Some(new_strlit("metrics")@),
                    port: if fb.spec.metrics_port.is_Some() {
                        fb.spec.metrics_port.get_Some_0()
                    } else {
                        2020
                    },
                    ..ServicePortView::default()
                };
                if fb.spec.ports.is_Some() {
                    Some(fb.spec.ports.get_Some_0().map_values(|p: ContainerPortView| make_service_port(p)).push(metrics_port))
                } else {
                    Some(seq![metrics_port])
                }
            },
            selector: if fb.spec.service_selector.is_Some() {
                    fb.spec.service_selector
                } else {
                    Some(make_base_labels(fb))
                },
            ..ServiceSpecView::default()
        }),
        ..ServiceView::default()
    }
}

pub open spec fn make_service_port(port: ContainerPortView) -> ServicePortView {
    ServicePortView {
        port: port.container_port,
        name: if port.name.is_Some() { port.name } else { ServicePortView::default().name },
        protocol: if port.protocol.is_Some() { port.protocol } else { ServicePortView::default().protocol },
        ..ServicePortView::default()
    }
}

}
