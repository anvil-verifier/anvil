# How to build, verify and run controllers

This project uses [`cargo verus`](https://github.com/verus-lang/verus). All
third-party dependencies (kube, k8s-openapi, tokio, …) live in the top-level
`Cargo.toml`; the Verus standard library (`vstd`) is pulled from
[crates.io](https://crates.io/crates/vstd).

## Code structure

```
.
├── Cargo.toml          # single root package: verifiable-controllers
├── build.md
├── deploy/             # CRDs, RBAC, kind config, sample workloads
├── deploy.sh           # apply deploy/<controller>/* to a kind cluster
├── docker/
│   ├── controller/     # Dockerfile.local / Dockerfile.publish
│   └── verus/          # builder image used by Dockerfile.publish
├── e2e/                # end-to-end test crate
├── local-test.sh       # build controller image + run e2e against kind
└── src/
    ├── lib.rs          # framework library
    ├── crds.rs         # k8s CRD type definitions
    ├── kubernetes_api_objects/ kubernetes_cluster/ reconciler/
    ├── shim_layer/ external_shim_layer/ state_machine/
    ├── temporal_logic/ vstd_ext/ unit_tests/
    ├── controllers/    # verified controller implementations
    │   ├── vdeployment_controller/  vreplicaset_controller/
    │   ├── vstatefulset_controller/ rabbitmq_controller/
    │   └── composition/
    └── bin/            # binary entry points (one per controller / verification target)
        ├── anvil.rs   esr_composition.rs   tla_demo.rs
        ├── vdeployment_controller.rs   vdeployment_admission_controller.rs
        ├── vreplicaset_controller.rs   vreplicaset_admission_controller.rs
        ├── vstatefulset_controller.rs  vstatefulset_admission_controller.rs
        └── rabbitmq_controller.rs
```

### Dependencies

```
kind_version: 0.23.0
go_version:   "^1.20"
```

`Cargo.toml` pins `vstd = "=…"` to a specific crates.io snapshot. CI
fetches the latest Verus release from
[verus-lang/verus](https://github.com/verus-lang/verus/releases/latest)
at runtime. When you bump `vstd`, also rebuild your local Verus binary
to a compatible release (typically the closest dated GitHub release).

## Build and verify

Use `cargo verus focus` for verification. Unlike `cargo verus verify`,
`focus` actually runs the SMT solver on the current crate. Most
verification targets are library modules (under `src/controllers/`,
`src/kubernetes_cluster/`, etc.), so combine `--lib` with
`--verify-module <mod>` to narrow scope:

```sh
# Verify the entire Anvil framework + every controller and proof:
cargo verus focus --lib -- --rlimit 50 --time

# Verify a single controller, scoped to its module:
cargo verus focus --lib -- \
    --rlimit 50 --time --verify-module vreplicaset_controller

# Verify the composition proofs:
cargo verus focus --lib -- \
    --rlimit 50 --time --verify-module composition

# Verify the TLA demo (proof code lives in src/bin/tla_demo.rs):
cargo verus focus --bin tla_demo -- --time
```

Pass extra Verus flags after `--`. Replace `--lib` with `--bin <name>`
to verify a specific binary's own source.

## Build and test

### Build a controller binary (fast, no verification)

```sh
cargo verus build --bin <controller_name> -- --no-verify
```

The binary lands in `target/debug/<controller_name>` (or
`target/release/<controller_name>` if you add `--release`).

### Test pipeline

1. Build the controller binary with `cargo verus build`.
2. Build the controller Docker image:
   * `docker/controller/Dockerfile.local` — uses your locally-built binary.
   * `docker/controller/Dockerfile.publish` — builds inside the Verus
     builder image (see `docker/verus/Dockerfile`); useful when the
     host's glibc differs from the target image.
3. Set up a kind cluster and load the image.
4. Apply the e2e tests from `e2e/src/` and the workload from `deploy/`
   via `deploy.sh`.

Steps 1–3 are automated:

```
./local-test.sh <controller_name> [--build|--build-remote]
  --build         build via `cargo verus build` on the host, then make the image
  --build-remote  build the image using the Verus builder (Dockerfile.publish)
  (no flag)       reuse an existing local image named local/<app>-controller:v0.1.0
```

Step 4:

```sh
cd e2e
cargo run -- <controller_name>
```

See `.github/workflows/ci.yml` for the exact CI invocations.
