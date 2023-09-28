#![allow(unused_imports)]
#![allow(unused_variables)]

use futures::{StreamExt, TryStreamExt};
use kube::{
    api::{
        Api, AttachedProcess, DeleteParams, DynamicObject, ListParams, Patch, PatchParams,
        ResourceExt,
    },
    core::crd::CustomResourceExt,
    core::GroupVersionKind,
    discovery::{ApiCapabilities, ApiResource, Discovery, Scope},
    Client, CustomResource,
};
use std::process::Command;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Failed to get kube client: {0}")]
    ClientGetFailed(#[from] kube_client::Error),

    #[error("Failed to apply yaml file!")]
    ApplyFailed,

    #[error("Failed to parse the yaml file!")]
    ParseYamlFailed(#[from] serde_yaml::Error),

    #[error("Failed to parse the json format!")]
    ParseJsonFailed(#[from] serde_json::Error),

    #[error("Failed to find the yaml file in provided path!")]
    GVKFailed(#[from] std::io::Error),

    #[error("Failed to get CRD: {0}")]
    CRDGetFailed(#[source] kube::Error),

    #[error("Timeout, e2e test failed!")]
    Timeout,

    #[error("Statefulset is not consistent with zookeeper cluster spec!")]
    ZookeeperStsFailed,

    #[error("Failed to set/get data to/from the zookeeper cluster!")]
    ZookeeperWorkloadFailed,

    #[error("Statefulset is not consistent with rabbitmq cluster spec!")]
    RabbitmqStsFailed,

    #[error("ConfigMap is not consistent with rabbitmq cluster spec!")]
    RabbitmqConfigMapFailed,

    #[error("Rabbitmq failed to set customized user/password!")]
    RabbitmqUserPassFailed,
}

pub async fn apply_file(
    pth: std::path::PathBuf,
    client: Client,
    discovery: &Discovery,
) -> Result<String, Error> {
    let yaml = std::fs::read_to_string(&pth)?;
    apply(yaml, client, discovery).await
}

pub async fn apply(yaml: String, client: Client, discovery: &Discovery) -> Result<String, Error> {
    let ssapply = PatchParams::apply("kubectl-light").force();
    let doc = serde_yaml::from_str(&yaml)?;

    let obj: DynamicObject = serde_yaml::from_value(doc)?;
    let namespace = obj.metadata.namespace.as_deref();
    let gvk = if let Some(tm) = &obj.types {
        GroupVersionKind::try_from(tm).unwrap()
    } else {
        println!("cannot apply object without valid TypeMeta {:?}", obj);
        return Err(Error::ApplyFailed);
    };
    let name = obj.name_any();
    if let Some((ar, caps)) = discovery.resolve_gvk(&gvk) {
        let api = dynamic_api(ar, caps, client.clone(), namespace, false);
        println!("Applying {}: \n{}", gvk.kind, serde_yaml::to_string(&obj)?);
        let data: serde_json::Value = serde_json::to_value(&obj)?;
        let _r = api.patch(&name, &ssapply, &Patch::Apply(data)).await?;
        println!("applied {} {}", gvk.kind, name);
    } else {
        println!("Cannot apply document for unknown {:?}", gvk);
        return Err(Error::ApplyFailed);
    }

    Ok(name)
}

fn dynamic_api(
    ar: ApiResource,
    caps: ApiCapabilities,
    client: Client,
    ns: Option<&str>,
    all: bool,
) -> Api<DynamicObject> {
    if caps.scope == Scope::Cluster || all {
        Api::all_with(client, &ar)
    } else if let Some(namespace) = ns {
        Api::namespaced_with(client, namespace, &ar)
    } else {
        Api::default_namespaced_with(client, &ar)
    }
}

pub async fn get_output_and_err(mut attached: AttachedProcess) -> (String, String) {
    let stdout = tokio_util::io::ReaderStream::new(attached.stdout().unwrap());
    let out = stdout
        .filter_map(|r| async { r.ok().and_then(|v| String::from_utf8(v.to_vec()).ok()) })
        .collect::<Vec<_>>()
        .await
        .join("");
    let stderr = tokio_util::io::ReaderStream::new(attached.stderr().unwrap());
    let err = stderr
        .filter_map(|r| async { r.ok().and_then(|v| String::from_utf8(v.to_vec()).ok()) })
        .collect::<Vec<_>>()
        .await
        .join("");
    attached.join().await.unwrap();
    (out, err)
}

pub fn run_command(program: &str, args: Vec<&str>, err_msg: &str) -> (String, String) {
    println!("{} {}", program, args.join(" "));
    let cmd = Command::new(program).args(args).output().expect(err_msg);
    println!("cmd output: {}", String::from_utf8_lossy(&cmd.stdout));
    println!("cmd error: {}", String::from_utf8_lossy(&cmd.stderr));
    (
        String::from_utf8_lossy(&cmd.stdout).to_string(),
        String::from_utf8_lossy(&cmd.stderr).to_string(),
    )
}
