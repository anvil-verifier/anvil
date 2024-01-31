use crate::executable_model::prelude::*;
use crate::kubernetes_api_objects::{
    error::*,
    exec::{api_resource::*, prelude::*},
    spec::prelude::Kind,
};
use deps_hack::kube::{
    api::{Api, DeleteParams, ListParams, ObjectMeta, PostParams},
    Client,
};
use deps_hack::tokio::runtime::Runtime;
use proptest::prelude::*;
use std::process::Command;
use vstd::prelude::*;
use vstd::string::*;

#[derive(Debug, Clone)]
enum GeneratedRequest {
    Get {
        kind: Kind,
        namespace: std::string::String,
        name: std::string::String,
    },
    Create {
        kind: Kind,
        namespace: std::string::String,
        name: std::string::String,
    },
}

impl Kind {
    fn to_api_resource(&self) -> ApiResource {
        match self {
            Kind::ConfigMapKind => {
                ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<
                    deps_hack::k8s_openapi::api::core::v1::ConfigMap,
                >(&()))
            }
            Kind::SecretKind => ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<
                deps_hack::k8s_openapi::api::core::v1::Secret,
            >(&())),
            _ => panic!(),
        }
    }

    fn to_default_dynamic_object(&self) -> DynamicObject {
        match self {
            Kind::ConfigMapKind => ConfigMap::default().marshal(),
            Kind::SecretKind => Secret::default().marshal(),
            _ => panic!(),
        }
    }
}

fn kind_strategy() -> BoxedStrategy<Kind> {
    prop_oneof![Just(Kind::ConfigMapKind), Just(Kind::SecretKind),].boxed()
}

prop_compose! {
  fn generated_request_get_case()(
      kind in kind_strategy(),
      namespace in "default",
      name in "[a-z0-9]([-a-z0-9]*[a-z0-9])?",
  ) -> GeneratedRequest {
      GeneratedRequest::Get { kind, namespace, name }
  }
}

prop_compose! {
  fn generated_request_create_case()(
      kind in kind_strategy(),
      namespace in "default",
      name in "[a-z0-9]([-a-z0-9]*[a-z0-9])?",
  ) -> GeneratedRequest {
      GeneratedRequest::Create { kind, namespace, name }
  }
}

fn generated_request_strategy() -> BoxedStrategy<GeneratedRequest> {
    prop_oneof![
        generated_request_get_case(),
        generated_request_create_case(),
    ]
    .boxed()
}

fn create_kind_cluster() {
    let kind_create_command = Command::new("kind")
        .arg("create")
        .arg("cluster")
        .arg("--image")
        .arg(format!("kindest/node:v1.26.0"))
        .output();
    match kind_create_command {
        Ok(output) => {
            if output.status.success() {
                println!("Kind cluster created successfully!");
            } else {
                eprintln!(
                    "Error creating Kind cluster: {}",
                    std::string::String::from_utf8_lossy(&output.stderr)
                );
                panic!();
            }
        }
        Err(err) => {
            eprintln!("Error running 'kind create cluster': {}", err);
            panic!();
        }
    }
}

fn delete_kind_cluster() {
    let kind_delete_command = Command::new("kind").arg("delete").arg("cluster").output();
    match kind_delete_command {
        Ok(output) => {
            if output.status.success() {
                println!("Kind cluster deleted successfully!");
            } else {
                eprintln!(
                    "Error deleting Kind cluster: {}",
                    std::string::String::from_utf8_lossy(&output.stderr)
                );
                panic!();
            }
        }
        Err(err) => {
            eprintln!("Error running 'kind delete cluster': {}", err);
            panic!();
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 1, .. ProptestConfig::default()
      })]
    #[test]
    fn test_model(generated_request in generated_request_strategy().no_shrink()) {
        let mut api_server_state = ApiServerState::new();
        match generated_request {
            GeneratedRequest::Get{kind, namespace, name} => {
                let get_request = KubeGetRequest {
                    api_resource: kind.to_api_resource(),
                    namespace: String::from_rust_string(namespace.to_string()),
                    name: String::from_rust_string(name.to_string()),
                };
                let model_resp = SimpleExecutableApiServerModel::handle_get_request(&get_request, &api_server_state);

                let rt = Runtime::new().unwrap();
                let kind_resp = rt.block_on(async {
                    let client = Client::try_default().await.unwrap();
                    let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                        client, &namespace, kind.to_api_resource().as_kube_ref()
                    );
                    api.get(&name).await
                });

                prop_assert_eq!(model_resp.res.is_ok(), kind_resp.is_ok());
            }
            GeneratedRequest::Create{kind, namespace, name} => {
                let obj = {
                    let mut obj = kind.to_default_dynamic_object();
                    obj.set_name(String::from_rust_string(name));
                    obj
                };
                let create_request = KubeCreateRequest {
                    api_resource: kind.to_api_resource(),
                    namespace: String::from_rust_string(namespace.to_string()),
                    obj: obj.clone(),
                };
                let (api_server_state, model_resp) = SimpleExecutableApiServerModel::handle_create_request(&create_request, api_server_state);

                let rt = Runtime::new().unwrap();
                let kind_resp = rt.block_on(async {
                    let client = Client::try_default().await.unwrap();
                    let api = Api::<deps_hack::kube::api::DynamicObject>::namespaced_with(
                        client, &namespace, kind.to_api_resource().as_kube_ref()
                    );
                    api.create(&PostParams::default(), &obj.into_kube()).await
                });
                prop_assert_eq!(model_resp.res.is_ok(), kind_resp.is_ok());
            }
        }
    }
}
