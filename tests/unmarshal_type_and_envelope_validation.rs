use verifiable_controllers::kubernetes_api_objects::exec::{
    dynamic::DynamicObject,
    persistent_volume_claim::PersistentVolumeClaim,
    pod::Pod,
    resource::ResourceWrapper,
    stateful_set::StatefulSet,
};
use verifiable_controllers::shim_layer::controller_runtime::wrap_listed_dynamic_object;
use verifiable_controllers::vstatefulset_controller::trusted::exec_types::VStatefulSet;

#[test]
fn test_unmarshal_rejects_untyped_wrong_kind_and_shadowed_envelope_keys() {
    // 1. Untyped DynamicObject must not parse as either Pod or PersistentVolumeClaim.
    let untyped = DynamicObject::from_kube(kube::api::DynamicObject {
        types: None,
        metadata: kube::api::ObjectMeta {
            name: Some("ambiguous".to_string()),
            namespace: Some("default".to_string()),
            ..Default::default()
        },
        data: serde_json::json!({}),
    });
    assert!(Pod::unmarshal(untyped.clone()).is_err());
    assert!(PersistentVolumeClaim::unmarshal(untyped).is_err());

    // 2. apps/v1 StatefulSet DynamicObject must be rejected by VStatefulSet::unmarshal
    // even when its spec fields are structurally compatible.
    let kube_sts: k8s_openapi::api::apps::v1::StatefulSet = serde_json::from_value(serde_json::json!({
        "apiVersion": "apps/v1",
        "kind": "StatefulSet",
        "metadata": { "name": "web", "namespace": "default" },
        "spec": {
            "serviceName": "web-svc",
            "selector": { "matchLabels": { "app": "web" } },
            "template": {
                "metadata": { "labels": { "app": "web" } },
                "spec": { "containers": [{ "name": "app", "image": "nginx:1.25" }] }
            }
        }
    }))
    .unwrap();
    let sts_dyn = StatefulSet::from_kube(kube_sts).marshal();
    assert!(StatefulSet::unmarshal(sts_dyn.clone()).is_ok());
    assert!(VStatefulSet::unmarshal(sts_dyn).is_err());

    // 3. Flattened `data` containing "metadata", "apiVersion", or "kind" must be rejected
    // so it cannot overwrite the outer DynamicObject envelope during try_parse.
    for forbidden_key in ["metadata", "apiVersion", "kind"] {
        let mut data = serde_json::Map::new();
        data.insert(
            forbidden_key.to_string(),
            serde_json::json!({ "name": "spoofed-name" }),
        );
        let shadowed = DynamicObject::from_kube(kube::api::DynamicObject {
            types: Some(kube::api::TypeMeta {
                api_version: "v1".to_string(),
                kind: "Pod".to_string(),
            }),
            metadata: kube::api::ObjectMeta {
                name: Some("legit-name".to_string()),
                namespace: Some("default".to_string()),
                ..Default::default()
            },
            data: serde_json::Value::Object(data),
        });
        assert!(
            Pod::unmarshal(shadowed).is_err(),
            "Pod::unmarshal must reject DynamicObject.data shadowing `{}`",
            forbidden_key
        );
    }

    // 4. Non-object `data` (e.g. JSON null/array) must also be rejected.
    let non_object_data = DynamicObject::from_kube(kube::api::DynamicObject {
        types: Some(kube::api::TypeMeta {
            api_version: "v1".to_string(),
            kind: "Pod".to_string(),
        }),
        metadata: kube::api::ObjectMeta {
            name: Some("pod-null-data".to_string()),
            ..Default::default()
        },
        data: serde_json::Value::Null,
    });
    assert!(Pod::unmarshal(non_object_data).is_err());
}

#[test]
fn test_list_response_items_stamped_with_api_resource_unmarshal_cleanly() {
    // Wire Kubernetes PodList omits per-item apiVersion/kind.
    let pod_list: kube::core::ObjectList<kube::api::DynamicObject> =
        serde_json::from_value(serde_json::json!({
            "apiVersion": "v1",
            "kind": "PodList",
            "metadata": { "resourceVersion": "10" },
            "items": [{
                "metadata": { "name": "web-0", "namespace": "default" },
                "spec": { "containers": [{ "name": "app", "image": "nginx:1.25" }] }
            }]
        }))
        .unwrap();

    let raw_item = pod_list.items.into_iter().next().unwrap();
    assert!(raw_item.types.is_none());

    let pod_ar = Pod::api_resource();
    let wrapped = wrap_listed_dynamic_object(raw_item, &pod_ar);

    let unmarshaled_pod = Pod::unmarshal(wrapped.clone()).expect("stamped Pod list item must unmarshal");
    assert_eq!(
        unmarshaled_pod.metadata().name().as_deref(),
        Some("web-0")
    );
    assert!(PersistentVolumeClaim::unmarshal(wrapped).is_err());
}
