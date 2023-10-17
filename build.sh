#!/usr/bin/env bash

## Build and verify the controller example.
##
## Requires VERUS_DIR to be set to the path to verus.

set -eu

# script dir is root of repo
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR/src"

rv=$VERUS_DIR/source/target-verus/release/verus
cd deps_hack
cargo build
cd ..
"$rv" -L dependency=deps_hack/target/debug/deps \
  --extern=deps_hack="deps_hack/target/debug/libdeps_hack.rlib" \
  --compile \
  "$@"
