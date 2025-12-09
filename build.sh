#!/usr/bin/env bash

set -xeu

env
which verus

# script dir is root of repo
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR/src"

cd deps_hack
cargo build
cd ..
# TODO: after the lifetime check is fixed in verus, remove the --no-lifetime flag
verus -L dependency=deps_hack/target/debug/deps \
  --extern=deps_hack="deps_hack/target/debug/libdeps_hack.rlib" \
  --compile \
  "$@"