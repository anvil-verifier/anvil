// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use k8s_openapi::api::core::v1 as k8s_core;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as k8s_meta;
use std::collections::BTreeMap;
use verifiable_controllers::crds;
use verifiable_controllers::kubernetes_api_objects::exec::{
    api_method::{
        KubeAPIRequest, KubeAPIResponse, KubeGetThenUpdateResponse, KubeListResponse,
    },
    pod::Pod,
    resource::ResourceWrapper,
};
use verifiable_controllers::reconciler::exec::{
    io::{Request, Response},
    reconciler::Reconciler,
};
use verifiable_controllers::vstatefulset_controller::{
    exec::reconciler::{make_pod, pod_spec_matches, VStatefulSetReconciler},
    trusted::{exec_types::VStatefulSet, step::VStatefulSetReconcileStep},
};

fn build_vsts_with_limits_only() -> VStatefulSet {
    let mut labels = BTreeMap::new();
    labels.insert("app".to_string(), "web".to_string());

    let mut limits = BTreeMap::new();
    limits.insert("cpu".to_string(), Quantity("500m".to_string()));

    VStatefulSet::from_kube(crds::VStatefulSet {
        metadata: k8s_meta::ObjectMeta {
            name: Some("web".to_string()),
            namespace: Some("default".to_string()),
            uid: Some("1001".to_string()),
            resource_version: Some("1".to_string()),
            ..Default::default()
        },
        spec: crds::VStatefulSetSpec {
            service_name: "web-svc".to_string(),
            replicas: Some(1),
            selector: k8s_meta::LabelSelector {
                match_labels: Some(labels.clone()),
                ..Default::default()
            },
            template: k8s_core::PodTemplateSpec {
                metadata: Some(k8s_meta::ObjectMeta {
                    labels: Some(labels),
                    ..Default::default()
                }),
                spec: Some(k8s_core::PodSpec {
                    containers: vec![k8s_core::Container {
                        name: "nginx".to_string(),
                        image: Some("nginx:1.25".to_string()),
                        resources: Some(k8s_core::ResourceRequirements {
                            limits: Some(limits),
                            requests: None,
                            claims: None,
                        }),
                        ..Default::default()
                    }],
                    ..Default::default()
                }),
            },
            ..Default::default()
        },
        status: None,
    })
}

#[test]
fn test_make_pod_matches_vstatefulset_template_without_spurious_normalization() {
    let vsts = build_vsts_with_limits_only();
    let mut pod = make_pod(&vsts, 0);
    let mut kube_pod = pod.into_kube();
    kube_pod.metadata.uid = Some("2001".to_string());
    kube_pod.metadata.resource_version = Some("2".to_string());
    pod = Pod::from_kube(kube_pod);

    // Previously, normalize_pod_spec(&vsts_spec) copied limits into requests on vsts_spec
    // while claiming `ensures spec@ == res@`, causing pod_spec_matches(&vsts, make_pod(&vsts, 0))
    // to return false!
    assert!(
        pod_spec_matches(&vsts, pod.clone()),
        "freshly synthesized make_pod(&vsts, 0) must match its own VStatefulSet template"
    );

    // End-to-end reconcile check: DeleteOutdated must transition to Done rather than
    // emitting GetThenDeleteRequest on a healthy pod synthesized by make_pod(&vsts, 0).
    let state = VStatefulSetReconciler::reconcile_init_state();
    let (state, req) = VStatefulSetReconciler::reconcile_core(&vsts, None, state);
    assert!(matches!(
        req,
        Some(Request::KRequest(KubeAPIRequest::ListRequest(_)))
    ));

    let list_resp = Response::KResponse(KubeAPIResponse::ListResponse(KubeListResponse {
        res: Ok(vec![pod.clone().marshal()]),
    }));
    let (state, req) = VStatefulSetReconciler::reconcile_core(&vsts, Some(list_resp), state);
    assert!(req.is_none());
    assert!(matches!(
        state.reconcile_step,
        VStatefulSetReconcileStep::UpdateNeeded
    ));

    let (state, req) = VStatefulSetReconciler::reconcile_core(&vsts, None, state);
    assert!(matches!(
        req,
        Some(Request::KRequest(KubeAPIRequest::GetThenUpdateRequest(_)))
    ));

    let update_resp = Response::KResponse(KubeAPIResponse::GetThenUpdateResponse(
        KubeGetThenUpdateResponse {
            res: Ok(pod.marshal()),
        },
    ));
    let (state, req) = VStatefulSetReconciler::reconcile_core(&vsts, Some(update_resp), state);
    assert!(req.is_none());
    assert!(matches!(
        state.reconcile_step,
        VStatefulSetReconcileStep::DeleteOutdated
    ));

    let (state, req) = VStatefulSetReconciler::reconcile_core(&vsts, None, state);
    assert!(
        req.is_none(),
        "DeleteOutdated must not emit GetThenDeleteRequest for a matching pod"
    );
    assert!(matches!(
        state.reconcile_step,
        VStatefulSetReconcileStep::Done
    ));
}
