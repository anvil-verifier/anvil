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
use rand::Rng;
use std::process::Command;
use vstd::prelude::*;
use vstd::string::*;

#[derive(Debug, Clone)]
enum GeneratedRequest {
    Get {
        kind: Kind,
        name: std::string::String,
    },
    Create {
        kind: Kind,
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
      name in "[a-z0-9]([-a-z0-9]*[a-z0-9])?",
  ) -> GeneratedRequest {
      GeneratedRequest::Get { kind, name }
  }
}

prop_compose! {
  fn generated_request_create_case()(
      kind in kind_strategy(),
      name in "[a-z0-9]([-a-z0-9]*[a-z0-9])?",
  ) -> GeneratedRequest {
      GeneratedRequest::Create { kind, name }
  }
}

fn generated_request_strategy() -> BoxedStrategy<GeneratedRequest> {
    prop_oneof![
        generated_request_get_case(),
        generated_request_create_case(),
    ]
    .boxed()
}

fn create_new_testing_namespace(len: usize) -> Option<std::string::String> {
    let mut rng = rand::thread_rng();
    let random_number: i32 = rng.gen_range(0..=10000);
    let namespace_name = format!("{}-{}", len, random_number);

    let rt = Runtime::new().unwrap();
    let resp = rt.block_on(async {
        let client = Client::try_default().await.unwrap();
        let namespace_api = Api::<deps_hack::k8s_openapi::api::core::v1::Namespace>::all(client);
        let namespace_obj = deps_hack::k8s_openapi::api::core::v1::Namespace {
            metadata: deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta {
                name: Some(namespace_name.to_string()),
                ..Default::default()
            },
            ..Default::default()
        };

        namespace_api.create(&PostParams::default(), &namespace_obj).await
    });

    match resp {
        Ok(_) => Some(namespace_name),
        Err(_) => None
    }
}

proptest! {
    // We specify that proptest will generate 50 test cases for the test function below
    // and each test case is a vector of generated_request with a length between 1 and 50.
    #![proptest_config(ProptestConfig::with_cases(50))]
    #[test]
    fn test_model(generated_request_sequence in prop::collection::vec(generated_request_strategy(), 1..=50).no_shrink()) {
        // Since we share the same kind cluster for different test cases, it is important to isolate different test cases.
        // We do so by running them in different namespace.
        // For each test case, we generate a random namespace.
        // If the namespace already exists (which happens very rarely), we skip this test case.
        let namespace_opt = create_new_testing_namespace(generated_request_sequence.len());
        prop_assume!(namespace_opt.is_some());
        let namespace = namespace_opt.unwrap();
        println!("Running with {} generated requests in namespace {}", generated_request_sequence.len(), namespace);
        let mut api_server_state = ApiServerState::new();
        for generated_request in generated_request_sequence {
            match generated_request {
                // Testing get request handler
                GeneratedRequest::Get{kind, name} => {
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
                // Testing create request handler
                GeneratedRequest::Create{kind, name} => {
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
                    let model_resp = SimpleExecutableApiServerModel::handle_create_request(&create_request, &mut api_server_state);

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
}
