#!/bin/bash
# Push-button script to generate the LOC table.
# Usage: ./tools/gen-loc-table.sh
#
# Prerequisites:
#   - VERUS_DIR is set (e.g., ~/Project/verus)
#   - deps_hack is built: cd src/deps_hack && cargo build
#   - line_count tool is built: cd $VERUS_DIR/source/tools/line_count && cargo build --release

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
VERUS_BIN="$(which verus)"
LINE_COUNT_DIR="$VERUS_DIR/source/tools/line_count"

VERUS_COMMON_ARGS=(
    -L "dependency=src/deps_hack/target/debug/deps"
    --extern=deps_hack="src/deps_hack/target/debug/libdeps_hack.rlib"
    --crate-type=lib
    --emit=dep-info
    --no-verify
)

# Controllers to process: (short_name, crate_entry_file)
CONTROLLERS=(
    "vreplicaset:src/vreplicaset_controller.rs"
    "vdeployment:src/vdeployment_controller.rs"
    "vstatefulset:src/vstatefulset_controller.rs"
    "rabbitmq:src/rabbitmq_controller.rs"
)
COMPOSITION_ENTRY="src/esr_composition.rs"

cd "$PROJECT_DIR"

echo "=== Step 1: Generate .d files ==="
for entry in "${CONTROLLERS[@]}"; do
    name="${entry%%:*}"
    crate_file="${entry##*:}"
    echo "  Generating ${name} .d file from ${crate_file}..."
    $VERUS_BIN "${VERUS_COMMON_ARGS[@]}" "$crate_file"
done
echo "  Generating esr_composition .d file from ${COMPOSITION_ENTRY}..."
$VERUS_BIN "${VERUS_COMMON_ARGS[@]}" "$COMPOSITION_ENTRY"

echo ""
echo "=== Step 2: Run line_count tool to generate tables ==="
for entry in "${CONTROLLERS[@]}"; do
    name="${entry%%:*}"
    d_file="${PROJECT_DIR}/$(basename "${entry##*:}" .rs).d"
    echo "  Processing ${name} (${d_file})..."
    cd "$LINE_COUNT_DIR"
    cargo run --release -- "$d_file" > "${name}_loc_table"
    cargo run --release -- "$d_file" --json > "${name}.json"
    cd "$PROJECT_DIR"
done

# esr_composition includes composition proofs
COMP_D_FILE="${PROJECT_DIR}/esr_composition.d"
echo "  Processing esr_composition (${COMP_D_FILE})..."
cd "$LINE_COUNT_DIR"
cargo run --release -- "$COMP_D_FILE" > "esr_composition_loc_table"
cargo run --release -- "$COMP_D_FILE" --json > "esr_composition.json"
cd "$PROJECT_DIR"

echo ""
echo "=== Step 3: Run count-loc.py for each controller ==="
cd "$SCRIPT_DIR"
for entry in "${CONTROLLERS[@]}"; do
    name="${entry%%:*}"
    echo "  Counting ${name}..."
    python3 count-loc.py "$LINE_COUNT_DIR/${name}_loc_table" "$name"
done
echo "  Counting composition..."
python3 count-loc.py "$LINE_COUNT_DIR/esr_composition_loc_table" composition

echo ""
echo "=== Step 4: Generate final table ==="
python3 gen-t1.py

echo ""
echo "=== Done ==="
