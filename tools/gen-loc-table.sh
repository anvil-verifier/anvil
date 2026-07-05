#!/bin/bash
# Push-button script to generate the LOC table.
# Usage: ./tools/gen-loc-table.sh
#
# Prerequisites:
#   - VERUS_DIR is set (e.g., ~/Project/verus)
#   - `cargo verus` is on PATH (or in $VERUS_DIR/source/target-verus/release)
#   - line_count tool is built:
#       cd $VERUS_DIR/source/tools/line_count && cargo build --release

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
LINE_COUNT_DIR="$VERUS_DIR/source/tools/line_count"

cd "$PROJECT_DIR"

echo "=== Step 1: Generate dep-info (.d) for the whole library ==="
cargo verus verify --lib -- --no-verify --emit=dep-info
D_FILE_SRC="$(find "$PROJECT_DIR/target" -name 'verifiable_controllers-*.d' \
    -printf '%T@ %p\n' | sort -rn | head -n1 | cut -d' ' -f2-)"
D_FILE="$PROJECT_DIR/anvil.d"
cp "$D_FILE_SRC" "$D_FILE"
echo "  dep-info: $D_FILE (from $D_FILE_SRC)"

echo ""
echo "=== Step 2: Run line_count to generate the combined table ==="
LOC_TABLE="$PROJECT_DIR/anvil_loc_table"
( cd "$LINE_COUNT_DIR" && cargo run --release -- "$D_FILE" ) > "$LOC_TABLE"
echo "  table: $LOC_TABLE"

echo ""
echo "=== Step 3: Categorize LOC per controller ==="
cd "$SCRIPT_DIR"
for name in vreplicaset vdeployment vstatefulset rabbitmq composition; do
    echo "  Counting ${name}..."
    python3 count-loc.py "$LOC_TABLE" "$name"
done

echo ""
echo "=== Step 4: Generate final table ==="
LOC_TABLE="$LOC_TABLE" python3 gen-t1.py

echo ""
echo "=== Done ==="
