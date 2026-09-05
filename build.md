# How to build, verify and run controllers

This project uses [`cargo verus`](https://github.com/verus-lang/verus). All third-party dependencies (kube, k8s-openapi, tokio, …) live in the top-level `Cargo.toml`; the Verus standard library (`vstd`) is tracking the `main` branch of [verus-lang/verus](https://github.com/verus-lang/verus).

## Source organization

`src/`

- `reconciler/` This defines the API for implementing `reconcile()` as a state machine.
- `shim_layer/` A layer that intercepts the requests returned by each state transition of `reconcile()`, issues the requests to the Kubernetes API server (or other endpoints customized by developers), and feeds the response to the next state transition of `reconcile()`. This layer is built on top of [kube](https://github.com/kube-rs/kube).
- `kubernetes_cluster/` A model of the core components in a Kubernetes cluster that controllers often interact with, including API servers, etcd, and some built-in controllers. It is written as a TLA-style state machine.
- `kubernetes_api_objects/` A library that defines commonly used Kubernetes API objects (e.g., Pod, ConfigMap, StatefulSet, Service, etc.). Most definitions are imported from [k8s-openapi](https://github.com/Arnavion/k8s-openapi) (which is also used by [kube](https://github.com/kube-rs/kube)) with a wrapper that allows formal reasoning on these objects.
- `state_machine/` A library for defining TLA-style state machines, used by `kubernetes_cluster/`.
- `controllers/` Example controllers we built and verified using Anvil (e.g., `rabbitmq_controller/`, `vreplicaset_controller/`, `vdeployment_controller/`, `vstatefulset_controller/`), plus their `composition/` proofs.
- `crds.rs` Custom resource type definitions (`kube`-derived), shared by the controllers and the e2e tests.
- `bin/` Binary entry points, one per controller, admission webhook, and verification target (e.g., `esr_composition.rs`).
- `tla_demo.rs` Proof code for the TLA demo.

`e2e/`: end-to-end tests for controllers

`tools/`: scripts to setup environment, build controller images and deploy controllers

Anvil is packed into a single cargo package (`verifiable-controllers`); see the sections below for the `cargo verus` build/verify commands.

### Dependencies

```
kind_version: 0.23.0
go_version:   "^1.20"
```

Run `./tools/setup-verus.sh` to fetch, build, and wire up a local Verus binary.

## Build and verify

Most verification targets are library modules (under `src/controllers/`, `src/kubernetes_cluster/`, etc.), so combine `--lib` with `--verify-only-module <mod>` to narrow scope:

```sh
# Verify the entire Anvil framework + every controller and proof:
cargo verus verify --lib

# Verify a single controller, scoped to its module:
cargo verus verify --lib -- --verify-only-module vreplicaset_controller

# Verify the composition proofs:
cargo verus verify --lib -- --verify-only-module composition

# Verify the TLA demo (proof code lives in src/tla_demo.rs):
cargo verus verify --lib -- --verify-only-module tla_demo
```

Pass extra Verus flags after `--`. Replace `--lib` with `--bin <name>` to verify a specific binary's own source.

## Build and test

### Build a controller binary (fast, no verification)

```sh
cargo verus build --bin <controller_name> -- --no-verify
```

The binary lands in `target/debug/<controller_name>` (or
`target/release/<controller_name>` if you add `--release`).

### Test pipeline

1. Build the controller binary with `cargo verus build` on the host.
2. Bake the binary into a controller Docker image with
   `docker/controller/Dockerfile`.
3. Set up a kind cluster and load the image.
4. Apply the e2e tests from `e2e/src/` and the workload from `deploy/`
   via `tools/deploy.sh`.

Steps 1–3 are automated:

```
./tools/local-test.sh <controller_name> [--build]
  --build     build via `cargo verus build` on the host, then make the image
  (no flag)   reuse an existing local image named local/<app>-controller:v0.1.0
```

Step 4:

```sh
cd e2e
cargo run -- <controller_name>
```

See `.github/workflows/ci.yml` for the exact CI invocations.
