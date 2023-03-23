#!/usr/bin/env bash

## Build and verify the main controller example.
##
## Requires VERUS_DIR to be set to the path to verus.

set -eu

# script dir is root of repo
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR/src"

rv=$VERUS_DIR/source/tools/rust-verify.sh
./deps_hack/build.sh
k8s_openapi_rlib="$(find deps_hack/target/debug/deps/ -name 'libk8s_openapi-*.rlib')"
$rv -L dependency=deps_hack/target/debug/deps \
  --extern=k8s_openapi="$k8s_openapi_rlib" \
  --cfg erasure_macro_todo --erasure macro --compile \
  main.rs
