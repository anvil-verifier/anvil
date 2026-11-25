use std::collections::BTreeMap;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use k8s_openapi::apimachinery::pkg::apis::meta::v1::{FieldsV1, ManagedFieldsEntry};
use verifiable_controllers::kubernetes_api_objects::exec::{
    api_method::{KubeAPIRequest, KubeAPIResponse, KubeListResponse},
    pod::Pod,
    resource::ResourceWrapper,
};
use verifiable_controllers::reconciler::exec::{
    io::{Request, Response, VoidEReq, VoidEResp},
    reconciler::Reconciler,
};
use verifiable_controllers::vstatefulset_controller::{
    exec::reconciler::{make_pod, VStatefulSetReconciler},
    trusted::{exec_types::VStatefulSet, step::VStatefulSetReconcileStep},
};

fn build_deep_fields_v1(depth: usize) -> FieldsV1 {
    let mut val = serde_json::json!({});
    for i in 0..depth {
        let mut outer = serde_json::Map::new();
        outer.insert(format!("f:level_{}", i), val);
        val = serde_json::Value::Object(outer);
    }
    FieldsV1(val)
}

#[test]
fn test_marshal_and_reconcile_update_handle_deep_managed_fields_v1() {
    let labels = BTreeMap::from([("app".to_string(), "web".to_string())]);
    let cpu_map = BTreeMap::from([("cpu".to_string(), Quantity("500m".to_string()))]);
    let kube_vsts: verifiable_controllers::crds::VStatefulSet = serde_json::from_value(serde_json::json!({
        "apiVersion": "anvil.dev/v1",
        "kind": "VStatefulSet",
        "metadata": {
            "name": "web",
            "namespace": "default",
            "uid": "vsts-uid-6"
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
    let vsts = VStatefulSet::from_kube(kube_vsts);

    // Attach 150 levels of nested JSON in metadata.managed_fields (exceeding serde_json::from_str's 128-level limit).
    let mut kube_pod = make_pod(&vsts, 0).into_kube();
    kube_pod.metadata.uid = Some("pod-0-uid".to_string());
    kube_pod.metadata.resource_version = Some("7".to_string());
    kube_pod.metadata.managed_fields = Some(vec![ManagedFieldsEntry {
        manager: Some("kubectl-client-side-apply".to_string()),
        operation: Some("Apply".to_string()),
        api_version: Some("v1".to_string()),
        fields_type: Some("FieldsV1".to_string()),
        fields_v1: Some(build_deep_fields_v1(150)),
        ..Default::default()
    }]);
    let existing_pod = Pod::from_kube(kube_pod);

    // Direct marshal + unmarshal must succeed without hitting serde_json's text-parser recursion limit.
    let marshaled = existing_pod.marshal();
    let roundtripped = Pod::unmarshal(marshaled.clone()).expect("deeply nested Pod must unmarshal");
    assert_eq!(roundtripped.metadata().name().as_deref(), Some("vstatefulset-web-0"));

    // End-to-end VStatefulSet UpdateNeeded step calls Pod::marshal when building GetThenUpdateRequest.
    let state = VStatefulSetReconciler::reconcile_init_state();
    let (state, _req): (_, Option<Request<VoidEReq>>) =
        VStatefulSetReconciler::reconcile_core(&vsts, None, state);
    let list_resp: Response<VoidEResp> =
        Response::KResponse(KubeAPIResponse::ListResponse(KubeListResponse {
            res: Ok(vec![marshaled]),
        }));
    let (state, _req) = VStatefulSetReconciler::reconcile_core(&vsts, Some(list_resp), state);
    assert!(matches!(
        state.reconcile_step,
        VStatefulSetReconcileStep::UpdateNeeded
    ));

    let (_state, req) = VStatefulSetReconciler::reconcile_core(&vsts, None, state);
    assert!(
        matches!(
            req,
            Some(Request::KRequest(KubeAPIRequest::GetThenUpdateRequest(_)))
        ),
        "UpdateNeeded must emit GetThenUpdateRequest without panicking on deeply nested managed_fields"
    );
}
