#!/usr/bin/env bash

set -eu

# script dir is root of repo
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR/src"

cd deps_hack
cargo build
cd ..

verus -L dependency=deps_hack/target/debug/deps \
  --extern=deps_hack="deps_hack/target/debug/libdeps_hack.rlib" \
  --compile \
  "$@"