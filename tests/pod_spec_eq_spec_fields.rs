use std::collections::BTreeMap;
use k8s_openapi::api::core::v1 as k8s_core;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as k8s_meta;
use verifiable_controllers::kubernetes_api_objects::exec::{
    api_method::{
        KubeAPIRequest, KubeAPIResponse, KubeGetThenUpdateResponse, KubeListResponse,
    },
    pod::{Pod, PodSpec},
    resource::ResourceWrapper,
};
use verifiable_controllers::reconciler::exec::{
    io::{Request, Response, VoidEReq, VoidEResp},
    reconciler::Reconciler,
};
use verifiable_controllers::vstatefulset_controller::{
    exec::reconciler::{make_pod, VStatefulSetReconciler},
    trusted::{
        exec_types::{VStatefulSet, VStatefulSetSpec},
        step::VStatefulSetReconcileStep,
    },
};

fn base_kube_pod_spec() -> k8s_core::PodSpec {
    k8s_core::PodSpec {
        containers: vec![k8s_core::Container {
            name: "app".to_string(),
            image: Some("nginx:1.25".to_string()),
            command: Some(vec!["/bin/server".to_string(), "--v1".to_string()]),
            args: Some(vec!["--port=8080".to_string()]),
            image_pull_policy: Some("IfNotPresent".to_string()),
            env: Some(vec![k8s_core::EnvVar {
                name: "LOG_LEVEL".to_string(),
                value: Some("info".to_string()),
                ..Default::default()
            }]),
            ports: Some(vec![k8s_core::ContainerPort {
                name: Some("http".to_string()),
                container_port: 8080,
                protocol: Some("TCP".to_string()),
                ..Default::default()
            }]),
            ..Default::default()
        }],
        service_account_name: Some("app-sa".to_string()),
        dns_policy: Some("ClusterFirst".to_string()),
        scheduler_name: Some("default-scheduler".to_string()),
        termination_grace_period_seconds: Some(30),
        ..Default::default()
    }
}

#[test]
fn test_eq_spec_compares_modeled_pod_and_container_fields() {
    let base = PodSpec::from_kube(base_kube_pod_spec());
    assert!(base.eq_spec(&PodSpec::from_kube(base_kube_pod_spec())));

    // Container.command change
    let mut k = base_kube_pod_spec();
    k.containers[0].command = Some(vec!["/bin/server".to_string(), "--v2".to_string()]);
    assert!(!base.eq_spec(&PodSpec::from_kube(k)), "eq_spec must detect Container.command changes");

    // Container.args change
    let mut k = base_kube_pod_spec();
    k.containers[0].args = Some(vec!["--port=9090".to_string()]);
    assert!(!base.eq_spec(&PodSpec::from_kube(k)), "eq_spec must detect Container.args changes");

    // Container.env change
    let mut k = base_kube_pod_spec();
    k.containers[0].env.as_mut().unwrap()[0].value = Some("debug".to_string());
    assert!(!base.eq_spec(&PodSpec::from_kube(k)), "eq_spec must detect Container.env changes");

    // Container.ports change
    let mut k = base_kube_pod_spec();
    k.containers[0].ports.as_mut().unwrap()[0].container_port = 9090;
    assert!(!base.eq_spec(&PodSpec::from_kube(k)), "eq_spec must detect Container.ports changes");

    // Container.name change
    let mut k = base_kube_pod_spec();
    k.containers[0].name = "sidecar".to_string();
    assert!(!base.eq_spec(&PodSpec::from_kube(k)), "eq_spec must detect Container.name changes");

    // Container.readiness_probe change
    let mut k = base_kube_pod_spec();
    k.containers[0].readiness_probe = Some(k8s_core::Probe {
        period_seconds: Some(10),
        ..Default::default()
    });
    assert!(!base.eq_spec(&PodSpec::from_kube(k)), "eq_spec must detect Container.readiness_probe changes");

    // PodSpec-level modeled fields
    let mut k = base_kube_pod_spec();
    k.service_account_name = Some("other-sa".to_string());
    assert!(!base.eq_spec(&PodSpec::from_kube(k)), "eq_spec must detect service_account_name changes");

    let mut k = base_kube_pod_spec();
    k.node_selector = Some(BTreeMap::from([("disktype".to_string(), "ssd".to_string())]));
    assert!(!base.eq_spec(&PodSpec::from_kube(k)), "eq_spec must detect node_selector changes");

    let mut k = base_kube_pod_spec();
    k.host_network = Some(true);
    assert!(!base.eq_spec(&PodSpec::from_kube(k)), "eq_spec must detect host_network changes");

    let mut k = base_kube_pod_spec();
    k.termination_grace_period_seconds = Some(60);
    assert!(!base.eq_spec(&PodSpec::from_kube(k)), "eq_spec must detect termination_grace_period_seconds changes");

    let mut k = base_kube_pod_spec();
    k.init_containers = Some(vec![k8s_core::Container {
        name: "init".to_string(),
        image: Some("busybox:1.36".to_string()),
        ..Default::default()
    }]);
    assert!(!base.eq_spec(&PodSpec::from_kube(k)), "eq_spec must detect init_containers changes");

    // ResourceRequirements: "1000m" vs "1" have distinct StringViews in ResourceRequirementsView
    let mut k1 = base_kube_pod_spec();
    k1.containers[0].resources = Some(k8s_core::ResourceRequirements {
        limits: Some(BTreeMap::from([("cpu".to_string(), Quantity("1000m".to_string()))])),
        requests: None,
        claims: None,
    });
    let mut k2 = base_kube_pod_spec();
    k2.containers[0].resources = Some(k8s_core::ResourceRequirements {
        limits: Some(BTreeMap::from([("cpu".to_string(), Quantity("1".to_string()))])),
        requests: None,
        claims: None,
    });
    assert!(
        !PodSpec::from_kube(k1).eq_spec(&PodSpec::from_kube(k2)),
        "eq_spec must distinguish distinct modeled Quantity string representations"
    );

    // Opaque unit-view wrappers (TolerationView {}, AffinityView {}) compare presence / count
    let mut t1 = base_kube_pod_spec();
    t1.affinity = Some(k8s_core::Affinity {
        node_affinity: Some(k8s_core::NodeAffinity::default()),
        ..Default::default()
    });
    t1.tolerations = Some(vec![k8s_core::Toleration {
        key: Some("k1".to_string()),
        ..Default::default()
    }]);
    let mut t2 = base_kube_pod_spec();
    t2.affinity = Some(k8s_core::Affinity::default());
    t2.tolerations = Some(vec![k8s_core::Toleration {
        key: Some("k2".to_string()),
        ..Default::default()
    }]);
    assert!(
        PodSpec::from_kube(t1).eq_spec(&PodSpec::from_kube(t2)),
        "eq_spec must match PodSpecView equality for unit-view wrappers"
    );
}

fn make_rolling_update_vsts(cmd_flag: &str) -> VStatefulSet {
    let labels = BTreeMap::from([("app".to_string(), "web".to_string())]);
    let cpu_map = BTreeMap::from([("cpu".to_string(), Quantity("500m".to_string()))]);
    let kube_vsts: verifiable_controllers::crds::VStatefulSet = serde_json::from_value(serde_json::json!({
        "apiVersion": "anvil.dev/v1",
        "kind": "VStatefulSet",
        "metadata": {
            "name": "web",
            "namespace": "default",
            "uid": "vsts-uid-3"
        },
        "spec": {
            "replicas": 1,
            "serviceName": "web-svc",
            "selector": { "matchLabels": labels },
            "template": {
                "metadata": { "labels": labels },
                "spec": {
                    "tolerations": [
                        {
                            "key": "node.kubernetes.io/not-ready",
                            "operator": "Exists",
                            "effect": "NoExecute",
                            "tolerationSeconds": 300
                        },
                        {
                            "key": "node.kubernetes.io/unreachable",
                            "operator": "Exists",
                            "effect": "NoExecute",
                            "tolerationSeconds": 300
                        }
                    ],
                    "containers": [{
                        "name": "app",
                        "image": "nginx:1.25",
                        "command": ["/bin/server", cmd_flag],
                        "resources": {
                            "limits": cpu_map,
                            "requests": cpu_map
                        }
                    }]
                }
            }
        }
    }))
    .unwrap();
    let _ = VStatefulSetSpec::default();
    let _ = k8s_meta::ObjectMeta::default();
    VStatefulSet::from_kube(kube_vsts)
}

#[test]
fn test_rolling_update_deletes_outdated_pod_when_command_changes() {
    let vsts_v1 = make_rolling_update_vsts("--v1");
    let mut existing_pod = make_pod(&vsts_v1, 0);
    let mut kube_pod = existing_pod.into_kube();
    kube_pod.metadata.uid = Some("pod-0-uid".to_string());
    kube_pod.metadata.resource_version = Some("1".to_string());
    existing_pod = Pod::from_kube(kube_pod);

    // User updates VStatefulSet container command from --v1 to --v2 without changing image tag
    let vsts_v2 = make_rolling_update_vsts("--v2");

    let state = VStatefulSetReconciler::reconcile_init_state();
    let (state, _req): (_, Option<Request<VoidEReq>>) =
        VStatefulSetReconciler::reconcile_core(&vsts_v2, None, state);
    let list_resp: Response<VoidEResp> =
        Response::KResponse(KubeAPIResponse::ListResponse(KubeListResponse {
            res: Ok(vec![existing_pod.clone().marshal()]),
        }));
    let (state, _req) = VStatefulSetReconciler::reconcile_core(&vsts_v2, Some(list_resp), state);
    let (state, _req) = VStatefulSetReconciler::reconcile_core(&vsts_v2, None, state);
    let update_resp: Response<VoidEResp> = Response::KResponse(
        KubeAPIResponse::GetThenUpdateResponse(KubeGetThenUpdateResponse {
            res: Ok(existing_pod.marshal()),
        }),
    );
    let (state, _req) = VStatefulSetReconciler::reconcile_core(&vsts_v2, Some(update_resp), state);
    assert!(matches!(
        state.reconcile_step,
        VStatefulSetReconcileStep::DeleteOutdated
    ));

    let (_state, delete_req) = VStatefulSetReconciler::reconcile_core(&vsts_v2, None, state);
    match delete_req {
        Some(Request::KRequest(KubeAPIRequest::GetThenDeleteRequest(req))) => {
            assert_eq!(req.name, "vstatefulset-web-0");
        }
        _ => panic!(
            "DeleteOutdated must emit GetThenDeleteRequest when container command changes"
        ),
    }
}
