#!/usr/bin/env bash
set -euo pipefail

# This script lives in scripts/, so the workspace defaults to the parent directory.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)"
WORKSPACE_DIR="${1:-$(cd "$SCRIPT_DIR/.." && pwd)}"
SWITCH_NAME="${2:-rocq-icp}"
OCAML_VERSION="4.14.2"

echo "Starting OPAM environment setup..."
echo "==> Workspace: $WORKSPACE_DIR"
echo "==> Target switch: '$SWITCH_NAME'"
echo "==> OCaml version: '$OCAML_VERSION'"

create_switch() {
  echo "==> Creating switch '$SWITCH_NAME' with OCaml version $OCAML_VERSION..."
  opam switch create "$SWITCH_NAME" "ocaml-base-compiler.$OCAML_VERSION"
}

# Check if the switch exists
if opam switch list --short 2>/dev/null | grep -qx "${SWITCH_NAME}"; then
  echo "The switch '$SWITCH_NAME' already exists."

  read -p "Do you want to remove it and recreate it? (Projects will be installed in it) [Y/n]: " REPLY
  REPLY=${REPLY:-Y}

  if [[ "$REPLY" =~ ^[Yy]$ ]]; then
    echo "==> Removing switch '$SWITCH_NAME'..."
    opam switch remove "$SWITCH_NAME" -y
    echo "==> Switch removed."
    create_switch
  else
    echo "==> Keeping existing switch. Installing projects in it."
  fi
else
  create_switch
fi

# Set the environment for the new switch
echo "==> Activating switch '$SWITCH_NAME'..."
eval "$(opam env --switch="$SWITCH_NAME" --set-switch)"

echo "==> Initializing submodules..."
git -C "$WORKSPACE_DIR" submodule update --init

echo "==> Installing dependencies from deps/coq/..."
opam install -y --deps-only "$WORKSPACE_DIR/deps/coq"

echo "==> Installing additional dependency for MetaRocq..."
opam install ppx_optcomp -y

echo "==> Linking OPAM switch '$SWITCH_NAME' locally to each project"
opam switch link $SWITCH_NAME "$WORKSPACE_DIR"
opam switch link $SWITCH_NAME "$WORKSPACE_DIR/deps/coq/"
opam switch link $SWITCH_NAME "$WORKSPACE_DIR/deps/stdlib/"
opam switch link $SWITCH_NAME "$WORKSPACE_DIR/deps/Coq-Equations/"
opam switch link $SWITCH_NAME "$WORKSPACE_DIR/deps/metarocq/"

echo ""
echo "==> Setup completed. To build:"
echo "    ./scripts/build.sh"
