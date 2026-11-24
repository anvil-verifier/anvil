// Native checks for what the verified controller_owner_ref of each custom resource relies on.
//
// controller_owner_ref now builds the owner reference itself, with the apiVersion and kind
// strings that owner_reference_kind_view maps to the resource's Kind, instead of calling
// kube::Resource::controller_owner_ref. These tests check that the result agrees with kube's
// own owner reference in every field but block_owner_deletion (which the spec of each resource
// fixes), and that the trusted ObjectMeta::uid getter returns the uid string.
use k8s_openapi::apimachinery::pkg::apis::meta::v1 as k8s_meta;
use kube::Resource;
use verifiable_controllers::crds;
use verifiable_controllers::kubernetes_api_objects::exec::{
    object_meta::ObjectMeta, resource::ResourceWrapper,
};
use verifiable_controllers::rabbitmq_controller::trusted::exec_types::RabbitmqCluster;
use verifiable_controllers::vdeployment_controller::trusted::exec_types::VDeployment;
use verifiable_controllers::vreplicaset_controller::trusted::exec_types::VReplicaSet;
use verifiable_controllers::vstatefulset_controller::trusted::exec_types::VStatefulSet;

fn meta(name: &str, uid: &str) -> k8s_meta::ObjectMeta {
    k8s_meta::ObjectMeta {
        name: Some(name.to_string()),
        namespace: Some("default".to_string()),
        uid: Some(uid.to_string()),
        ..Default::default()
    }
}

fn check(ours: k8s_meta::OwnerReference, kube: k8s_meta::OwnerReference, block_owner_deletion: Option<bool>) {
    assert_eq!(ours.api_version, kube.api_version);
    assert_eq!(ours.kind, kube.kind);
    assert_eq!(ours.name, kube.name);
    assert_eq!(ours.uid, kube.uid);
    assert_eq!(ours.controller, kube.controller);
    assert_eq!(ours.controller, Some(true));
    assert_eq!(ours.block_owner_deletion, block_owner_deletion);
}

#[test]
fn test_controller_owner_ref_agrees_with_kube() {
    let vsts = crds::VStatefulSet { metadata: meta("demo-vsts", "uid-1"), ..Default::default() };
    check(
        VStatefulSet::from_kube(vsts.clone()).controller_owner_ref().into_kube(),
        vsts.controller_owner_ref(&()).unwrap(),
        Some(true),
    );
    let vrs = crds::VReplicaSet { metadata: meta("demo-vrs", "uid-2"), ..Default::default() };
    check(
        VReplicaSet::from_kube(vrs.clone()).controller_owner_ref().into_kube(),
        vrs.controller_owner_ref(&()).unwrap(),
        Some(true),
    );
    let vd = crds::VDeployment { metadata: meta("demo-vd", "uid-3"), ..Default::default() };
    check(
        VDeployment::from_kube(vd.clone()).controller_owner_ref().into_kube(),
        vd.controller_owner_ref(&()).unwrap(),
        Some(true),
    );
    let rmq = crds::RabbitmqCluster { metadata: meta("demo-rmq", "uid-4"), ..Default::default() };
    check(
        RabbitmqCluster::from_kube(rmq.clone()).controller_owner_ref().into_kube(),
        rmq.controller_owner_ref(&()).unwrap(),
        None,
    );
}

#[test]
fn test_object_meta_uid() {
    assert_eq!(ObjectMeta::from_kube(meta("a", "uid-5")).uid(), Some("uid-5".to_string()));
    assert_eq!(ObjectMeta::from_kube(meta("a", "")).uid(), Some("".to_string()));
    assert_eq!(ObjectMeta::from_kube(k8s_meta::ObjectMeta::default()).uid(), None);
}
