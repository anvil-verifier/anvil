#!/usr/bin/env bash
# Push-button script to reproduce the Welder testing and performance results.
# See the README of this branch for the full instructions.
#
# Usage:
#   ./tools/reproduce-welder-testing.sh functional     # functional tests (Acto), needed by the other phases
#   ./tools/reproduce-welder-testing.sh crash          # controller-crash and Pod-crash tests (Chactos)
#   ./tools/reproduce-welder-testing.sh performance    # performance measurement
#   ./tools/reproduce-welder-testing.sh all            # everything, in order
#
# Environment variables:
#   ACTO_DIR      path to the acto checkout on the v-dev branch
#                 (default ~/workdir/acto, where the CloudLab profile places it)
#   NUM_WORKERS   number of parallel workers, each runs its own kind cluster (default 4)
#   PYTHON        python interpreter to use (default: $ACTO_DIR/venv-welder from
#                 setup-welder-env.sh if present, otherwise python3)

set -euo pipefail

case "${1:-}" in
    functional|crash|performance|all) ;;
    *)
        sed -n '2,17p' "$0" | sed 's/^# \{0,1\}//'
        exit 1
        ;;
esac

ACTO_DIR="${ACTO_DIR:-$HOME/workdir/acto}"
[ -d "$ACTO_DIR" ] || { echo "error: acto checkout not found at $ACTO_DIR; set ACTO_DIR" >&2; exit 1; }
cd "$ACTO_DIR"

NUM_WORKERS="${NUM_WORKERS:-4}"
if [ -z "${PYTHON:-}" ] && [ -x "venv-welder/bin/python" ]; then
    PYTHON="venv-welder/bin/python"
fi
PYTHON="${PYTHON:-python3}"

VD_CONFIG="data/vdeployment-controller/v0/config.json"
VD_REF_CONFIG="data/deployment-controller/v0/config.json"
RMQ_CONFIG="data/anvil-rabbitmq-controller/config.json"
RMQ_REF_CONFIG="data/rabbitmq-operator/v2-19-2/config.json"

VD_TESTRUN="testrun-vdeployment"
RMQ_TESTRUN="testrun-rabbitmq"

functional() {
    echo "=== Functional tests: Deployment + ReplicaSet campaign ==="
    "$PYTHON" -m acto --config "$VD_CONFIG" --num-workers "$NUM_WORKERS" --workdir "$VD_TESTRUN"
    echo "=== Functional tests: RabbitMQ + StatefulSet campaign ==="
    "$PYTHON" -m acto --config "$RMQ_CONFIG" --num-workers "$NUM_WORKERS" --workdir "$RMQ_TESTRUN"
    echo "=== Collecting functional test results ==="
    "$PYTHON" -m acto.post_process.collect_test_result --config "$VD_CONFIG" --testrun-dir "$VD_TESTRUN"
    "$PYTHON" -m acto.post_process.collect_test_result --config "$RMQ_CONFIG" --testrun-dir "$RMQ_TESTRUN"
}

run_chactos() {
    local config="$1" testrun="$2" fic="$3"
    echo "=== Crash tests: $fic ==="
    "$PYTHON" -m chactos --config "$config" \
        --fi-config "chactos/${fic}.json" \
        --testrun-dir "$testrun" \
        --workdir "testrun-crash-${fic}" \
        --num-workers "$NUM_WORKERS"
}

crash() {
    [ -d "$VD_TESTRUN" ] || { echo "error: $VD_TESTRUN not found; run '$0 functional' first" >&2; exit 1; }
    [ -d "$RMQ_TESTRUN" ] || { echo "error: $RMQ_TESTRUN not found; run '$0 functional' first" >&2; exit 1; }
    # Deployment + ReplicaSet campaign: individual, correlated, and Pod crashes
    for fic in vdeployment vreplicaset vdeployment-correlated vdeployment-pod-crash vdeployment-pod-crash-rand; do
        run_chactos "$VD_CONFIG" "$VD_TESTRUN" "$fic"
    done
    # RabbitMQ + StatefulSet campaign: individual, correlated, and Pod crashes
    for fic in rabbitmq-controller vstatefulset rabbitmq-controller-correlated rabbitmq-controller-pod-crash rabbitmq-controller-pod-crash-rand; do
        run_chactos "$RMQ_CONFIG" "$RMQ_TESTRUN" "$fic"
    done
}

performance() {
    [ -d "$VD_TESTRUN" ] || { echo "error: $VD_TESTRUN not found; run '$0 functional' first" >&2; exit 1; }
    [ -d "$RMQ_TESTRUN" ] || { echo "error: $RMQ_TESTRUN not found; run '$0 functional' first" >&2; exit 1; }

    echo "=== Performance: generating input workloads ==="
    "$PYTHON" plugins/performance_measurement/measure_performance.py --gen \
        --input-dir "$VD_TESTRUN" -c "$VD_CONFIG" -j vdeployment-controller
    "$PYTHON" plugins/performance_measurement/measure_performance.py --gen \
        --input-dir "$RMQ_TESTRUN" -c "$RMQ_CONFIG" -j rabbitmq-operator

    echo "=== Performance: Deployment + ReplicaSet ==="
    "$PYTHON" plugins/performance_measurement/measure_performance.py \
        --workdir testrun-vdeployment-performance-first-write \
        --input-dir "$VD_TESTRUN" \
        -c "$VD_CONFIG" -r "$VD_REF_CONFIG" -j vdeployment-controller
    echo "=== Performance: RabbitMQ + StatefulSet ==="
    "$PYTHON" plugins/performance_measurement/measure_performance.py \
        --workdir testrun-rabbitmq-performance-first-write \
        --input-dir "$RMQ_TESTRUN" \
        -c "$RMQ_CONFIG" -r "$RMQ_REF_CONFIG" -j rabbitmq-operator

    echo "=== Performance: processing results ==="
    "$PYTHON" plugins/performance_measurement/process_ts.py
    echo "=== Done: see anvil-table-3.txt ==="
}

case "$1" in
    functional)  functional ;;
    crash)       crash ;;
    performance) performance ;;
    all)
        functional
        crash
        performance
        ;;
esac
