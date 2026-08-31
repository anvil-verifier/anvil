[![License](https://img.shields.io/badge/License-MIT-green.svg)](https://github.com/anvil-verifier/anvil/blob/main/LICENSE)
[![CI](https://github.com/anvil-verifier/anvil/actions/workflows/ci.yml/badge.svg)](https://github.com/anvil-verifier/anvil/actions/workflows/ci.yml)

# Anvil: Building Formally Verified Kubernetes Controllers

Anvil is a framework for building and formally verifying Kubernetes controllers. Developers use Anvil to implement Kubernetes controllers in Rust, specify correctness properties in a formal language, and verify that the controller implementations satisfy the correctness properties with machine-checkable proofs. Anvil is built on top of [Verus](https://github.com/verus-lang/verus), a tool for verifying Rust programs. Anvil's specifications and proofs are written in [verus-tla](https://github.com/anvil-verifier/verus-tla), the TLA embedding in Verus. The verified controllers use the [kube](https://github.com/kube-rs/kube) client to communicate with the Kubernetes API server and can be deployed in real-world Kubernetes clusters.

To verify Kubernetes controllers, developers need to specify the correctness properties and write machine-checkable proofs to show the controller implementation satisfies the properties. Anvil enables developers to verify a key liveness property called **Eventually Stable Reconciliation (ESR)**,it states that a controller should *eventually* make the cluster state match its desired state, and stay in that desired state *stably*, despite failures and network issues.

Verifying controllers still requires some expertise in SMT-based theorem proving. For more details, you can refer to the controller [examples](src/controllers/) we have verified (see their `proof/` folders).

## Welder: Compositional Verification for Kubernetes Control Plane

Welder is a framework built on top of Anvil for verifying a fleet of Kubernetes controllers. In addition to Anvil's correctness specification, developers formally specify rely-guarantee conditions and liveness dependencies (CORE) of each controller, and verify that controllers respect each other's non-interference requirements and dependencies.

So far, we have built and verified both builtin and custom Kubernetes controllers using Welder: three controllers for managing builtin Kubernetes workloads, including ReplicaSet, Deployment, and StatefulSet, and one custom controller for managing RabbitMQ deployed on Kubernetes. We used the [upstream Kubernetes controllers](https://github.com/kubernetes/kubernetes/tree/master/pkg/controller) and the [official RabbitMQ operator](https://github.com/rabbitmq/cluster-operator) as references when building our controllers. Welder is now merged into Anvil's main branch, and we are using it to build and verify more controllers.

The best way to use Anvil is to download the source code and import its components into your controller projects, like what we did for our controller [examples](src/controllers/). We briefly cover how to build, verify and run controllers in the following sections.

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
Every time `reconcile()` is invoked, it starts with the initial state, transitions to the next state until it arrives at an ending state. Each state transition returns a new state and one request that the controller wants to send to the API server (e.g., Get, List, Create, Update, or Delete). The request could also be application-specific (e.g., calling ZooKeeper's reconfiguration API). Anvil has a shim layer that issues these requests and feeds the corresponding response to the next state transition.

For more details, you can refer to the controller [examples](src/controllers/) we have built (see their `exec/` folders).

### Composing controllers with Welder

> Welder is only required for multi-controller verifications

A controller verified in isolation says nothing about how it behaves next to others. On top of its ESR, Welder asks each controller for more specifications:

```rust
pub struct ControllerSpec {
    // liveness goal (ESR from Anvil, but it can be a different liveness spec)
    pub esr: TempPred<ClusterState>,
    // what this controller requires from the controllers it depends on
    pub liveness_dependency: TempPred<ClusterState>,
    // what guarantee conditions this controller gives
    pub safety_guarantee: TempPred<ClusterState>,
    // controller's assumptions on faults
    pub environment_rely: TempPred<ClusterState>,
    // controller's assumptions on each other controller, given its id
    pub safety_partial_rely: spec_fn(int) -> TempPred<ClusterState>,
    // fairness assumptions
    pub fairness: spec_fn(Cluster) -> TempPred<ClusterState>,
    // controller installation requirements
    pub membership: spec_fn(Cluster, int) -> bool,
}
```

Developers construct a `ControllerSpec` carrying all conditions above for their controllers. Not all conditions may be required, for example, the ReplicaSet controller's `environment_rely` is trivial (`true_pred()`).

Then, developers pair the cluster model with a registry mapping each controller id to its `ControllerSpec`, producing a `CoreCluster`, and name the set of controllers to be composed with a `CoreSet`. The registry is required to avoid controller id collision and we want to remove it later. CORE spec is defined as

```rust
pub open spec fn core(cluster: CoreCluster, s: CoreSet) -> bool
```

Proving it for a given `CoreCluster` and `CoreSet` establishes the guarantee conditions of every controller in the set unconditionally, and their ESR whenever the relies and liveness dependencies are met. We provide proof helpers in `src/kubernetes_cluster/proof/core.rs`. Usually we begin with a singleton `CoreSet`, prove the CORE spec for it, then compose it with another `CoreSet` by `compose` when the two sets are independent, or by `compose_dep` when one depends on the other's progress. Please check our composition proof examples in `src/controllers/composition`.

### Compiling, Verifying, deploying and testing controllers

See [build.md](./build.md).

## Publications

- Welder: Compositional Liveness Verification of Cluster Control Planes <br>
Zhizhen Cathy Cai, Nikhil Date, Jiawei Tyler Gu, Cody Rivera, Tej Chajed, Oded Padon, Tianyin Xu, and Xudong Sun. In Proceedings of the 32nd ACM Symposium on Operating Systems Principles (SOSP'26), Prague, Czechia, Sep. 2026.

- [Anvil: Verifying Liveness of Cluster Management Controllers](https://www.usenix.org/conference/osdi24/presentation/sun-xudong) <br>
Xudong Sun, Wenjie Ma, Jiawei Tyler Gu, Zicheng Ma, Tej Chajed, Jon Howell, Andrea Lattuada, Oded Padon, Lalith Suresh, Adriana Szekeres, and Tianyin Xu. In Proceedings of the 18th USENIX Symposium on Operating Systems Design and Implementation (OSDI'24), Santa Clara, CA, USA, Jul. 2024.

- [Anvil: Building Kubernetes Controllers That Do Not Break](https://www.usenix.org/publications/loginonline/anvil-building-formally-verified-kubernetes-controllers) <br>
Xudong Sun, Jiawei Tyler Gu, Cody Rivera, Tej Chajed, Jon Howell, Andrea Lattuada, Oded Padon, Lalith Suresh, Adriana Szekeres, and Tianyin Xu. USENIX ;login:, Jun. 2024.

### Artifacts

If you want to reproduce the results in the SOSP'26 paper "Welder: Compositional Liveness Verification of Cluster Control Planes", please refer to the [sosp26](https://github.com/anvil-verifier/anvil/tree/sosp26) branch.

If you want to reproduce the results in the OSDI'24 paper "Anvil: Verifying Liveness of Cluster Management Controllers", please refer to the [osdi24](https://github.com/anvil-verifier/anvil/tree/osdi24) branch.