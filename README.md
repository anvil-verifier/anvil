[![License](https://img.shields.io/badge/License-MIT-green.svg)](https://github.com/anvil-verifier/anvil/blob/main/LICENSE)
[![CI](https://github.com/anvil-verifier/anvil/actions/workflows/ci.yml/badge.svg)](https://github.com/anvil-verifier/anvil/actions/workflows/ci.yml)

# Anvil: Building Formally Verified Kubernetes Controllers

Anvil is a framework for building and formally verifying Kubernetes controllers. Developers use Anvil to implement Kubernetes controllers in Rust, specify correctness properties in a formal language, and verify that the controller implementations satisfy the correctness properties with machine-checkable proofs. Anvil is built on top of [Verus](https://github.com/verus-lang/verus), a tool for verifying Rust programs, and [kube](https://github.com/kube-rs/kube), a Kubernetes client in Rust.

So far, we have built and verified Kubernetes controllers (including ones for managing RabbitMQ and Kubernetes built-in workloads such as ReplicaSet, Deployment and StatefulSet) using Anvil. We used the [official RabbitMQ operator](https://github.com/rabbitmq/cluster-operator) and the upstream Kubernetes controllers as references when building our controllers. We are now using Anvil to build (and verify) more controllers.

For now, the best way to use Anvil is to download the source code and import its components into your controller projects, like what we did for our controller [examples](src/controllers/). Anvil builds and verifies through [`cargo verus`](https://github.com/verus-lang/verus): all third-party dependencies live in the top-level `Cargo.toml` and the Verus standard library (`vstd`) is pulled from [crates.io](https://crates.io/crates/vstd). See [`build.md`](build.md) for how to build, verify and run controllers. You will need a [Verus](https://github.com/verus-lang/verus) binary whose version is consistent with the pinned `vstd` (See the [installation instructions](https://github.com/verus-lang/verus/blob/main/INSTALL.md)).

If you want to reproduce the results in the OSDI'24 paper "Anvil: Verifying Liveness of Cluster Management Controllers", please refer to the [osdi24](https://github.com/anvil-verifier/anvil/tree/osdi24) branch.

## Implementing controllers with Anvil

Implementing a Kubernetes controller in Anvil mostly means implementing a `reconcile()` function for a particular custom resource type (which is no different from the traditional way of implementing controllers). The only major difference is that one has to write `reconcile()` as a state machine that defines initial state, ending state and state transitions. The reason for this style is to enable formal verification. Anvil provides an [API](src/reconciler/exec/reconciler.rs) for developers to implement their `reconcile()` in this way:
```rust
// Anvil's interface for implementing reconcile() as a state machine
pub trait Reconciler{
    type R; // custom resource type
    type T; // reconcile local state type
    // initial state
    fn reconcile_init_state() -> Self::T;
    // state transition
    fn reconcile_core(cr: &Self::R, resp_o: Option<Response<...>, state: Self::T) -> (Self::T, Option<Request<...>>);
    // ending state (reconcile is done without any error)
    fn reconcile_done(state: &Self::T) -> bool;
    // ending state (reconcile encounters error)
    fn reconcile_error(state: &Self::T) -> bool;
}
```
Every time when `reconcile()` is invoked, it starts with the initial state, transitions to the next state until it arrives at an ending state. Each state transition returns a new state and one request that the controller wants to send to the API server (e.g., Get, List, Create, Update or Delete). The request could also be application specific (e.g., calling ZooKeeper's reconfiguration API). Anvil has a shim layer that issues these requests and feed the corresponding response to the next state transition.

For more details, you can refer to the controller [examples](src/controllers/) we have built (see their `exec/` folders).

## Verifying controllers with Anvil

Verifying a Kubernetes controller requires the developers to specify some correctness properties and write machine-checkable proofs to show the controller implementation satisfies the properties.

Anvil allows developers to verify diverse types of correctness properties. A key property we find useful is **Eventually Stable Reconciliation (ESR)**, a liveness property stating that a controller should eventually manage the system to its desired state, and stays in that desired state, despite failures and network issues.

Verifying controllers still requires some expertise on SMT-based theorem proving. For more details, you can refer to the controller [examples](src/controllers/) we have verified (see their `proof/` folders).


## Source organization

`src/`

- `reconciler/` This defines the API for implementing `reconcile()` as a state machine.
- `shim_layer/` A layer that intercepts the requests returned by each state transition of `reconcile()`, issues the requests to the Kubernetes API server (or other endpoints customized by developers), and feeds the response to the next state transition of `reconcile()`. This layer is built on top of [kube](https://github.com/kube-rs/kube).
- `kubernetes_cluster/` A model of the core components in a Kubernetes cluster that controllers often interact with, including API servers, etcd, and some built-in controllers. It is written as a TLA-style state machine.
- `kubernetes_api_objects/` A library that defines commonly used Kubernetes API objects (e.g., Pod, ConfigMap, StatefulSet, Service, etc.). Most definitions are imported from [k8s-openapi](https://github.com/Arnavion/k8s-openapi) (which is also used by [kube](https://github.com/kube-rs/kube)) with a wrapper that allows formal reasoning on these objects.
- `state_machine/` A library for defining TLA-style state machines, used by `kubernetes_cluster/`.
- `temporal_logic/` A library for performing temporal logic reasoning on top of Verus. It is mainly used for enabling TLA-style liveness verification.
- `controllers/` Example controllers we built and verified using Anvil (e.g., `rabbitmq_controller/`, `vreplicaset_controller/`, `vdeployment_controller/`, `vstatefulset_controller/`), plus their `composition/` proofs.
- `crds.rs` Custom resource type definitions (`kube`-derived), shared by the controllers and the e2e tests.
- `bin/` Binary entry points, one per controller, admission webhook, and verification target (e.g., `esr_composition.rs`, `tla_demo.rs`).

Everything lives in a single cargo package (`verifiable-controllers`); see [`build.md`](build.md) for the full layout and the `cargo verus` build/verify commands.

## Publications

- [Anvil: Verifying Liveness of Cluster Management Controllers](https://www.usenix.org/conference/osdi24/presentation/sun-xudong) <br>
Xudong Sun, Wenjie Ma, Jiawei Tyler Gu, Zicheng Ma, Tej Chajed, Jon Howell, Andrea Lattuada, Oded Padon, Lalith Suresh, Adriana Szekeres, and Tianyin Xu. In Proceedings of the 18th USENIX Symposium on Operating Systems Design and Implementation (OSDI'24), Santa Clara, CA, USA, Jul. 2024.

