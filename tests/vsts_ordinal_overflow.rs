use std::collections::BTreeMap;
use k8s_openapi::apimachinery::pkg::api::resource::Quantity;
use verifiable_controllers::kubernetes_api_objects::exec::{
    api_method::{
        KubeAPIRequest, KubeAPIResponse, KubeGetThenDeleteResponse, KubeGetThenUpdateResponse,
        KubeListResponse,
    },
    pod::Pod,
    resource::ResourceWrapper,
};
use verifiable_controllers::reconciler::exec::{
    io::{Request, Response, VoidEReq, VoidEResp},
    reconciler::Reconciler,
};
use verifiable_controllers::vstatefulset_controller::{
    exec::reconciler::{make_pod, VStatefulSetReconciler},
    trusted::{
        exec_types::VStatefulSet,
        reconciler::{get_ordinal, has_ordinal},
        step::VStatefulSetReconcileStep,
    },
};

fn make_vsts(replicas: i32) -> VStatefulSet {
    let labels = BTreeMap::from([("app".to_string(), "web".to_string())]);
    let cpu_map = BTreeMap::from([("cpu".to_string(), Quantity("500m".to_string()))]);
    let kube_vsts: verifiable_controllers::crds::VStatefulSet = serde_json::from_value(serde_json::json!({
        "apiVersion": "anvil.dev/v1",
        "kind": "VStatefulSet",
        "metadata": {
            "name": "web",
            "namespace": "default",
            "uid": "vsts-uid-4"
        },
        "spec": {
            "replicas": replicas,
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
    VStatefulSet::from_kube(kube_vsts)
}

fn make_owned_named_pod(vsts: &VStatefulSet, name: &str) -> Pod {
    let pod = make_pod(vsts, 0);
    let mut kube_pod = pod.into_kube();
    kube_pod.metadata.name = Some(name.to_string());
    kube_pod.metadata.uid = Some(format!("uid-{}", name));
    kube_pod.metadata.resource_version = Some("1".to_string());
    Pod::from_kube(kube_pod)
}

#[test]
fn test_has_ordinal_and_get_ordinal_handle_values_above_usize_max() {
    let parent = "web".to_string();
    let overflow_name = "vstatefulset-web-18446744073709551616".to_string();
    let huge_name = "vstatefulset-web-100000000000000000000".to_string();
    let zero_pad_name = "vstatefulset-web-00".to_string();
    let plus_name = "vstatefulset-web-+1".to_string();

    assert!(has_ordinal(&parent, &overflow_name));
    assert_eq!(get_ordinal(&parent, &overflow_name), None);

    assert!(has_ordinal(&parent, &huge_name));
    assert_eq!(get_ordinal(&parent, &huge_name), None);

    assert!(!has_ordinal(&parent, &zero_pad_name));
    assert!(!has_ordinal(&parent, &plus_name));
}

#[test]
fn test_condemned_pods_include_and_sort_ordinals_above_usize_max() {
    let vsts = make_vsts(1);

    let pod_0 = make_owned_named_pod(&vsts, "vstatefulset-web-0");
    let pod_2 = make_owned_named_pod(&vsts, "vstatefulset-web-2");
    let pod_overflow = make_owned_named_pod(&vsts, "vstatefulset-web-18446744073709551616");
    let pod_huge = make_owned_named_pod(&vsts, "vstatefulset-web-100000000000000000000");
    let pod_non_canonical = make_owned_named_pod(&vsts, "vstatefulset-web-00");

    let state = VStatefulSetReconciler::reconcile_init_state();
    let (state, _req): (_, Option<Request<VoidEReq>>) =
        VStatefulSetReconciler::reconcile_core(&vsts, None, state);

    let list_resp: Response<VoidEResp> =
        Response::KResponse(KubeAPIResponse::ListResponse(KubeListResponse {
            res: Ok(vec![
                pod_2.marshal(),
                pod_overflow.marshal(),
                pod_0.clone().marshal(),
                pod_non_canonical.marshal(),
                pod_huge.marshal(),
            ]),
        }));
    let (state, _req) = VStatefulSetReconciler::reconcile_core(&vsts, Some(list_resp), state);
    assert!(matches!(
        state.reconcile_step,
        VStatefulSetReconcileStep::UpdateNeeded
    ));

    // Step through UpdateNeeded for pod 0
    let (state, _req) = VStatefulSetReconciler::reconcile_core(&vsts, None, state);
    let update_resp: Response<VoidEResp> = Response::KResponse(
        KubeAPIResponse::GetThenUpdateResponse(KubeGetThenUpdateResponse {
            res: Ok(pod_0.marshal()),
        }),
    );
    let (mut state, _req) = VStatefulSetReconciler::reconcile_core(&vsts, Some(update_resp), state);
    assert!(matches!(
        state.reconcile_step,
        VStatefulSetReconcileStep::DeleteCondemned
    ));

    let mut deleted_names = Vec::new();
    while matches!(state.reconcile_step, VStatefulSetReconcileStep::DeleteCondemned) {
        let (next_state, req) = VStatefulSetReconciler::reconcile_core(&vsts, None, state);
        match req {
            Some(Request::KRequest(KubeAPIRequest::GetThenDeleteRequest(del_req))) => {
                deleted_names.push(del_req.name);
            }
            _ => panic!("expected GetThenDeleteRequest for condemned Pod"),
        }
        let del_resp: Response<VoidEResp> = Response::KResponse(
            KubeAPIResponse::GetThenDeleteResponse(KubeGetThenDeleteResponse { res: Ok(()) }),
        );
        let (after_del_state, _req) =
            VStatefulSetReconciler::reconcile_core(&vsts, Some(del_resp), next_state);
        state = after_del_state;
    }

    assert_eq!(
        deleted_names,
        vec![
            "vstatefulset-web-100000000000000000000".to_string(),
            "vstatefulset-web-18446744073709551616".to_string(),
            "vstatefulset-web-2".to_string(),
        ],
        "condemned Pods must include canonical ordinals > usize::MAX and delete in descending numerical order while ignoring non-canonical suffixes"
    );
}
