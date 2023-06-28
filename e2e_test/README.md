## How to run the end to end test?

#### Prerequisites

Before you run the test, please make sure:

1. The corresponding controller has been deployed.
2. The corresponding CRD has been created.

Recommend using `deploy.sh` to do prerequisites above.

---

#### Run

Use `cargo run zookeeper` to test zookeeper controller or `cargo run rabbitmq` to test rabbitmq controller 

If the controller works as expected, the program will print `xxx cluster is ready! e2e test passed`.

The test may also return different errors based on different situations:

* `Failed to get kube client: ...` means kube client error. There is something wrong with k8s cluster or kube client connections.
* `Failed to get CRD: ...` means the corresponding CRD has not been created.
* `Timeout, e2e test failed!` means the state doesn't reach to expected state in 6 mins.
* `Statefulset is not consistent with zookeeper/rabbitmq cluster spec!` means the statefulset spec is not correct.
* `ConfigMap is not consistent with rabbitmq cluster spec!` means the configmap spec is not correct.
* `Rabbitmq failed to set customized user/password!` means the test for customized user/password failed.

