#!/usr/bin/env bash
# One-shot setup for the Welder verification experiments (anvil repo only).
# Testing/performance dependencies (Docker, Python env for acto) are
# provisioned separately; see the README of this branch.
#
# Usage (from the anvil repo root, or anywhere):
#   ./tools/setup-welder-env.sh
#
# Installs, without sudo:
#   - the Rust toolchain pinned by rust-toolchain.toml (via rustup)
#   - the Verus release binary at $HOME/verus
#   - the Verus source at $HOME/verus-source, with the line_count tool built
#     (needed by tools/gen-loc-table.sh; not shipped in the release binary)
#   - the `tabulate` Python package used to render the LOC table
#
# Idempotent: safe to rerun after a transient failure.

set -euo pipefail

VERUS_VERSION="${VERUS_VERSION:-0.2026.06.28.1847ab3}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$PROJECT_DIR"

echo "=== Installing Rust toolchain ==="
if ! command -v rustup >/dev/null 2>&1 && [ ! -x "$HOME/.cargo/bin/rustup" ]; then
    curl --proto '=https' --tlsv1.2 -fsSL "https://sh.rustup.rs" | sh -s -- --default-toolchain none -y
fi
. "$HOME/.cargo/env"
rustup toolchain install

echo "=== Installing Verus release binary at \$HOME/verus ==="
if [ ! -x "$HOME/verus/cargo-verus" ]; then
    curl -fsSL -o /tmp/verus.zip "https://github.com/verus-lang/verus/releases/download/release%2F${VERUS_VERSION}/verus-${VERUS_VERSION}-x86-linux.zip"
    unzip -q /tmp/verus.zip -d "$HOME"
    rm -rf "$HOME/verus"
    mv "$HOME/verus-x86-linux" "$HOME/verus"
    rm /tmp/verus.zip
fi

echo "=== Building the Verus line_count tool at \$HOME/verus-source ==="
if [ ! -d "$HOME/verus-source" ]; then
    git clone --branch "release/${VERUS_VERSION}" https://github.com/verus-lang/verus.git "$HOME/verus-source"
fi
(cd "$HOME/verus-source/source/tools/line_count" && cargo build --release)

echo "=== Installing the Python dependency of the LOC table script ==="
pip3 install tabulate

echo ""
echo "=== Anvil environment ready ==="
echo "Add Verus to your PATH before running the verification commands:"
echo "  export PATH=\"\$PATH:\$HOME/verus\""
echo "The LOC table script expects:"
echo "  export VERUS_DIR=\"\$HOME/verus-source\""
