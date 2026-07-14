#!/usr/bin/env bash
# One-shot environment setup for the Welder testing and performance experiments.
# See the README of this branch for the full instructions.
#
# Usage:
#   ACTO_DIR=<path to the acto checkout (v-dev branch)> ./tools/setup-welder-env.sh
#   (ACTO_DIR defaults to ~/workdir/acto, where the CloudLab profile places it)
#
# Installs, without sudo:
#   - a Python 3.12 virtualenv at $ACTO_DIR/venv-welder with all Python
#     dependencies (provisioned via uv, so the system Python version does
#     not matter)
#   - kind and kubectl into ~/.local/bin, if missing
#
# Prerequisites: Docker (running), and Go if kind is not already installed.

set -euo pipefail

ACTO_DIR="${ACTO_DIR:-$HOME/workdir/acto}"
[ -d "$ACTO_DIR" ] || { echo "error: acto checkout not found at $ACTO_DIR; set ACTO_DIR" >&2; exit 1; }
cd "$ACTO_DIR"

KIND_VERSION="v0.23.0"
KUBECTL_VERSION="v1.30.0"

BIN_DIR="$HOME/.local/bin"
mkdir -p "$BIN_DIR"
export PATH="$BIN_DIR:$PATH"

echo "=== Checking Docker ==="
docker info >/dev/null 2>&1 || { echo "error: Docker is not running; install/start it first" >&2; exit 1; }

echo "=== Setting up Python 3.12 environment at $ACTO_DIR/venv-welder ==="
command -v uv >/dev/null 2>&1 || curl -LsSf https://astral.sh/uv/install.sh | sh
uv venv --clear --python 3.12 venv-welder
uv pip install -p venv-welder/bin/python -r requirements-dev.txt \
    matplotlib pandas tabulate prometheus_client

echo "=== Checking kind ==="
if ! command -v kind >/dev/null 2>&1; then
    command -v go >/dev/null 2>&1 || { echo "error: kind is missing and Go is not installed (https://go.dev/doc/install)" >&2; exit 1; }
    GOBIN="$BIN_DIR" go install "sigs.k8s.io/kind@$KIND_VERSION"
fi

echo "=== Checking kubectl ==="
if ! command -v kubectl >/dev/null 2>&1; then
    curl -fsSLo "$BIN_DIR/kubectl" "https://dl.k8s.io/release/$KUBECTL_VERSION/bin/linux/amd64/kubectl"
    chmod +x "$BIN_DIR/kubectl"
fi

echo ""
echo "=== Environment ready ==="
echo "Make sure $BIN_DIR is on your PATH."
echo "The push-button script picks up $ACTO_DIR/venv-welder automatically:"
echo "  ACTO_DIR=$ACTO_DIR ./tools/reproduce-welder-testing.sh functional"
