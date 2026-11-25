// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use k8s_openapi::api::core::v1 as k8s_core;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as k8s_meta;
use std::collections::BTreeMap;
use verifiable_controllers::crds;
use verifiable_controllers::kubernetes_api_objects::exec::{
    api_method::{KubeAPIRequest, KubeAPIResponse, KubeListResponse},
    pod::Pod,
    resource::ResourceWrapper,
};
use verifiable_controllers::rabbitmq_controller::trusted::exec_types::RabbitmqCluster;
use verifiable_controllers::reconciler::exec::{
    io::{Request, Response},
    reconciler::Reconciler,
};
use verifiable_controllers::vdeployment_controller::{
    exec::reconciler::VDeploymentReconciler, trusted::exec_types::VDeployment,
};
use verifiable_controllers::vreplicaset_controller::{
    exec::reconciler::VReplicaSetReconciler, trusted::exec_types::VReplicaSet,
};
use verifiable_controllers::vstatefulset_controller::{
    exec::reconciler::VStatefulSetReconciler, trusted::exec_types::VStatefulSet,
};

#[test]
fn test_crd_controller_owner_refs_match_spec_block_owner_deletion() {
    let meta = |name: &str, uid: &str| k8s_meta::ObjectMeta {
        name: Some(name.to_string()),
        namespace: Some("default".to_string()),
        uid: Some(uid.to_string()),
        ..Default::default()
    };

    let vsts = VStatefulSet::from_kube(crds::VStatefulSet {
        metadata: meta("demo-vsts", "101"),
        ..Default::default()
    });
    let vsts_oref = vsts.controller_owner_ref().into_kube();
    assert_eq!(vsts_oref.api_version, "anvil.dev/v1");
    assert_eq!(vsts_oref.kind, "VStatefulSet");
    assert_eq!(vsts_oref.name, "demo-vsts");
    assert_eq!(vsts_oref.uid, "101");
    assert_eq!(vsts_oref.controller, Some(true));
    assert_eq!(vsts_oref.block_owner_deletion, Some(true));

    let vrs = VReplicaSet::from_kube(crds::VReplicaSet {
        metadata: meta("demo-vrs", "102"),
        ..Default::default()
    });
    let vrs_oref = vrs.controller_owner_ref().into_kube();
    assert_eq!(vrs_oref.api_version, "anvil.dev/v1");
    assert_eq!(vrs_oref.kind, "VReplicaSet");
    assert_eq!(vrs_oref.name, "demo-vrs");
    assert_eq!(vrs_oref.uid, "102");
    assert_eq!(vrs_oref.controller, Some(true));
    assert_eq!(vrs_oref.block_owner_deletion, Some(true));

    let vd = VDeployment::from_kube(crds::VDeployment {
        metadata: meta("demo-vd", "103"),
        ..Default::default()
    });
    let vd_oref = vd.controller_owner_ref().into_kube();
    assert_eq!(vd_oref.api_version, "anvil.dev/v1");
    assert_eq!(vd_oref.kind, "VDeployment");
    assert_eq!(vd_oref.name, "demo-vd");
    assert_eq!(vd_oref.uid, "103");
    assert_eq!(vd_oref.controller, Some(true));
    assert_eq!(vd_oref.block_owner_deletion, Some(true));

    // RabbitmqClusterView::controller_owner_ref specifies block_owner_deletion: None
    let rbmq = RabbitmqCluster::from_kube(crds::RabbitmqCluster {
        metadata: meta("demo-rbmq", "104"),
        ..Default::default()
    });
    let rbmq_oref = rbmq.controller_owner_ref().into_kube();
    assert_eq!(rbmq_oref.api_version, "anvil.dev/v1");
    assert_eq!(rbmq_oref.kind, "RabbitmqCluster");
    assert_eq!(rbmq_oref.controller, Some(true));
    assert_eq!(rbmq_oref.block_owner_deletion, None);
}

#[test]
fn test_controllers_stamp_block_owner_deletion_on_created_dependents() {
    let mut labels = BTreeMap::new();
    labels.insert("app".to_string(), "web".to_string());

    let pod_template = k8s_core::PodTemplateSpec {
        metadata: Some(k8s_meta::ObjectMeta {
            labels: Some(labels.clone()),
            ..Default::default()
        }),
        spec: Some(k8s_core::PodSpec {
            containers: vec![k8s_core::Container {
                name: "nginx".to_string(),
                image: Some("nginx:1.25".to_string()),
                ..Default::default()
            }],
            ..Default::default()
        }),
    };

    // 1. VStatefulSet -> Pod
    let vsts = VStatefulSet::from_kube(crds::VStatefulSet {
        metadata: k8s_meta::ObjectMeta {
            name: Some("web".to_string()),
            namespace: Some("default".to_string()),
            uid: Some("9001".to_string()),
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
            template: pod_template.clone(),
            ..Default::default()
        },
        status: None,
    });

    let state = VStatefulSetReconciler::reconcile_init_state();
    let (state, req) = VStatefulSetReconciler::reconcile_core(&vsts, None, state);
    assert!(matches!(req, Some(Request::KRequest(KubeAPIRequest::ListRequest(_)))));

    let empty_list = || {
        Response::KResponse(KubeAPIResponse::ListResponse(KubeListResponse {
            res: Ok(vec![]),
        }))
    };
    let (state, req) = VStatefulSetReconciler::reconcile_core(&vsts, Some(empty_list()), state);
    assert!(req.is_none());
    let (_state, req) = VStatefulSetReconciler::reconcile_core(&vsts, None, state);
    let create_req = match req {
        Some(Request::KRequest(KubeAPIRequest::CreateRequest(r))) => r,
        other => panic!("expected CreateRequest for VStatefulSet pod-0, got {:?}", other.is_some()),
    };
    let kube_pod = Pod::unmarshal(create_req.obj).unwrap().into_kube();
    let owner_refs = kube_pod.metadata.owner_references.unwrap();
    assert_eq!(owner_refs.len(), 1);
    assert_eq!(owner_refs[0].controller, Some(true));
    assert_eq!(owner_refs[0].block_owner_deletion, Some(true));

    // 2. VReplicaSet -> Pod
    let vrs = VReplicaSet::from_kube(crds::VReplicaSet {
        metadata: k8s_meta::ObjectMeta {
            name: Some("web-vrs".to_string()),
            namespace: Some("default".to_string()),
            uid: Some("9002".to_string()),
            resource_version: Some("1".to_string()),
            ..Default::default()
        },
        spec: crds::VReplicaSetSpec {
            replicas: Some(1),
            selector: k8s_meta::LabelSelector {
                match_labels: Some(labels.clone()),
                ..Default::default()
            },
            template: Some(pod_template.clone()),
        },
        status: None,
    });
    let state = VReplicaSetReconciler::reconcile_init_state();
    let (state, _req) = VReplicaSetReconciler::reconcile_core(&vrs, None, state);
    let (_state, req) = VReplicaSetReconciler::reconcile_core(&vrs, Some(empty_list()), state);
    let create_req = match req {
        Some(Request::KRequest(KubeAPIRequest::CreateRequest(r))) => r,
        other => panic!("expected CreateRequest for VReplicaSet pod, got {:?}", other.is_some()),
    };
    let vrs_pod = Pod::unmarshal(create_req.obj).unwrap().into_kube();
    assert_eq!(
        vrs_pod.metadata.owner_references.unwrap()[0].block_owner_deletion,
        Some(true)
    );

    // 3. VDeployment -> VReplicaSet
    let vd = VDeployment::from_kube(crds::VDeployment {
        metadata: k8s_meta::ObjectMeta {
            name: Some("web-vd".to_string()),
            namespace: Some("default".to_string()),
            uid: Some("9003".to_string()),
            resource_version: Some("1".to_string()),
            ..Default::default()
        },
        spec: crds::VDeploymentSpec {
            replicas: Some(1),
            selector: k8s_meta::LabelSelector {
                match_labels: Some(labels),
                ..Default::default()
            },
            template: pod_template,
            ..Default::default()
        },
    });
    let state = VDeploymentReconciler::reconcile_init_state();
    let (state, _req) = VDeploymentReconciler::reconcile_core(&vd, None, state);
    let (_state, req) = VDeploymentReconciler::reconcile_core(&vd, Some(empty_list()), state);
    let create_req = match req {
        Some(Request::KRequest(KubeAPIRequest::CreateRequest(r))) => r,
        other => panic!("expected CreateRequest for VDeployment VReplicaSet, got {:?}", other.is_some()),
    };
    let vd_vrs = VReplicaSet::unmarshal(create_req.obj).unwrap().into_kube();
    assert_eq!(
        vd_vrs.metadata.owner_references.unwrap()[0].block_owner_deletion,
        Some(true)
    );
}
