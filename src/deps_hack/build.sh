#!/usr/bin/env bash

set -eu

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR"

RUSTC=$VERUS_DIR/rust/install/bin/rustc \
  RUSTDOC=$VERUS_DIR/rust/install/bin/rustdoc \
  "$VERUS_DIR"/rust/install/bin/cargo build

# then compile `main.rs` in the root with (the rlib hash may change, not sure)
# ~/Src/verus/source/tools/rust-verify.sh --log-all -L dependency=deps_hack/target/debug/deps --extern=k8s_openapi=deps_hack/target/debug/deps/libk8s_openapi-ab02ba08bf2471fa.rlib --cfg erasure_macro_todo --erasure macro --compile --no-verify main.rs
