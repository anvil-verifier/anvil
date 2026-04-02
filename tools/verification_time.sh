#!/usr/bin/env bash
set -eu

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." >/dev/null 2>&1 && pwd)"
cd "$DIR/src"

# Build deps once
cd deps_hack && cargo build && cd ..

VERUS="verus -L dependency=deps_hack/target/debug/deps \
  --extern=deps_hack=deps_hack/target/debug/libdeps_hack.rlib"

OUTDIR="$DIR/tools"
SUMMARY="$OUTDIR/verification_time.log"
> "$SUMMARY"

echo "=== Build started at $(date) ===" | tee -a "$SUMMARY"

run_verify() {
  local LABEL="$1"; shift
  echo "--- Verifying: $LABEL ---" | tee -a "$SUMMARY"
  START=$(date +%s)
  set +e
  $VERUS --rlimit 50 --time --allow=unused "$@" >> "$SUMMARY" 2>&1
  EXIT=$?
  set -e
  END=$(date +%s)
  ELAPSED=$((END - START))

  RESULT=$(grep -E "^verification results::" "$SUMMARY" | tail -1 || echo "(no result line)")
  echo "  ${LABEL}: ${ELAPSED}s, exit=${EXIT}, ${RESULT}" | tee -a "$SUMMARY"
}

# Controllers (compiled crates)
run_verify vreplicaset_controller  --compile --verify-module vreplicaset_controller  vreplicaset_controller.rs
run_verify vdeployment_controller  --compile --verify-module vdeployment_controller  vdeployment_controller.rs
run_verify vstatefulset_controller --compile --verify-module vstatefulset_controller vstatefulset_controller.rs
run_verify rabbitmq_controller     --compile --verify-module rabbitmq_controller     rabbitmq_controller.rs

# Composition (lib crate, multiple modules)
run_verify composition --crate-type=lib \
  --verify-module composition::vreplicaset_reconciler \
  --verify-module composition::vdeployment_reconciler \
  --verify-module composition::vstatefulset_controller \
  --verify-module composition::rabbitmq_controller \
  esr_composition.rs

echo "=== Build finished at $(date) ===" | tee -a "$SUMMARY"
