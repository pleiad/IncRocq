#!/usr/bin/env bash
set -euo pipefail

SWITCH_NAME="rocq-icp"
# This script lives in scripts/, so the workspace is the parent directory.
WORKSPACE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)"

ROCQ_PACKAGES="rocq-runtime,rocq-core,coq-core,coqide-server,rocqide"

# Activate the right switch regardless of the working directory
export OPAMSWITCH="$SWITCH_NAME"
eval "$(opam env --switch="$SWITCH_NAME" --set-switch)"

echo "==> Active switch: $(opam switch show)"
echo "==> Workspace: $WORKSPACE_DIR"
echo ""

# ------------------------------------------------------------------
# 1. Rocq
# ------------------------------------------------------------------
echo "==> [1/5] Building Rocq..."
cd "$WORKSPACE_DIR/deps/coq"

make dunestrap
dune build -p "$ROCQ_PACKAGES"
dune install -p "$ROCQ_PACKAGES" --prefix="$(opam var prefix)"

echo "==> [1/5] Rocq installed."
echo ""

# ------------------------------------------------------------------
# 2. Stdlib
# ------------------------------------------------------------------
echo "==> [2/5] Building Stdlib..."
cd "$WORKSPACE_DIR/deps/stdlib"

make dune
make dune-install

echo "==> [2/5] Stdlib installed."
echo ""

# ------------------------------------------------------------------
# 3. Equations
# ------------------------------------------------------------------
echo "==> [3/5] Building Equations..."
cd "$WORKSPACE_DIR/deps/Coq-Equations"

./configure.sh local
make
make install

echo "==> [3/5] Equations installed."
echo ""

# ------------------------------------------------------------------
# 4. MetaRocq
# ------------------------------------------------------------------
echo "==> [4/5] Building MetaRocq..."
cd "$WORKSPACE_DIR/deps/metarocq"

./configure.sh local
make -j template-rocq
make -C utils install
make -C common install
make -C template-rocq install

echo "==> [4/5] MetaRocq installed."
echo ""
# ------------------------------------------------------------------
# 5. IncRocq
# ------------------------------------------------------------------
echo "==> [5/5] Building IncRocq..."
cd "$WORKSPACE_DIR"

make

echo ""
echo "==> Build complete."
