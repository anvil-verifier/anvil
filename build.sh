#!/usr/bin/env bash

## Build and verify the main controller example.
##
## Requires VERUS_DIR to be set to the path to verus.

set -eu

# script dir is root of repo
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR/src"

rv=$VERUS_DIR/source/tools/rust-verify.sh
cd deps_hack
cargo build
cd ..
k8s_openapi_rlib="$(find deps_hack/target/debug/deps -name 'libk8s_openapi-*.rlib' | head -n 1)"
kube_rlib="$(find deps_hack/target/debug/deps -name 'libkube-*.rlib' | head -n 1)"
kube_client_rlib="$(find deps_hack/target/debug/deps -name 'libkube_client-*.rlib' | head -n 1)"
kube_core_rlib="$(find deps_hack/target/debug/deps -name 'libkube_core-*.rlib' | head -n 1)"
kube_runtime_rlib="$(find deps_hack/target/debug/deps -name 'libkube_runtime-*.rlib' | head -n 1)"
serde_rlib="$(find deps_hack/target/debug/deps -name 'libserde-*.rlib' | head -n 1)"
serde_json_rlib="$(find deps_hack/target/debug/deps -name 'libserde_json-*.rlib' | head -n 1)"
serde_yaml_rlib="$(find deps_hack/target/debug/deps -name 'libserde_yaml-*.rlib' | head -n 1)"
schemars_rlib="$(find deps_hack/target/debug/deps -name 'libschemars-*.rlib' | head -n 1)"
tokio_rlib="$(find deps_hack/target/debug/deps -name 'libtokio-*.rlib' | head -n 1)"
tracing_rlib="$(find deps_hack/target/debug/deps -name 'libtracing-*.rlib' | head -n 1)"
anyhow_rlib="$(find deps_hack/target/debug/deps -name 'libanyhow-*.rlib' | head -n 1)"
futures_rlib="$(find deps_hack/target/debug/deps -name 'libfutures-*.rlib' | head -n 1)"
"$rv" -L dependency=deps_hack/target/debug/deps \
  --extern=k8s_openapi="$k8s_openapi_rlib" \
  --extern=kube="$kube_rlib" \
  --extern=kube_client="$kube_client_rlib" \
  --extern=kube_core="$kube_core_rlib" \
  --extern=kube_runtime="$kube_runtime_rlib" \
  --extern=serde="$serde_rlib" \
  --extern=serde_json="$serde_json_rlib" \
  --extern=serde_yaml="$serde_yaml_rlib" \
  --extern=schemars="$schemars_rlib" \
  --extern=tokio="$tokio_rlib" \
  --extern=tracing="$tracing_rlib" \
  --extern=anyhow="$anyhow_rlib" \
  --extern=futures="$futures_rlib" \
  --extern=deps_hack="deps_hack/target/debug/libdeps_hack.rlib" \
  --expand-errors \
  --compile \
  --time \
  main.rs
