#!/usr/bin/env bash
# Idempotent Cloud Agent bootstrap for this Lean 4 / Lake project.
# Installs elan (the Lean toolchain manager) if missing, ensures the
# pinned toolchain from `lean-toolchain` is available, and builds the project.
set -euo pipefail

ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
ELAN_ENV="$ELAN_HOME/env"

if [ ! -x "$ELAN_HOME/bin/elan" ]; then
  echo "==> Installing elan"
  curl -fsSL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh
  # --default-toolchain none: let elan pick the version from lean-toolchain.
  sh /tmp/elan-init.sh -y --default-toolchain none
  rm -f /tmp/elan-init.sh
else
  echo "==> elan already installed"
fi

# Make elan available to this shell and to future non-login shells.
# shellcheck disable=SC1090
. "$ELAN_ENV"
if [ -f "$HOME/.bashrc" ] && ! grep -q '.elan/env' "$HOME/.bashrc"; then
  echo '. "$HOME/.elan/env"' >> "$HOME/.bashrc"
fi

echo "==> elan $(elan --version)"

# Install the toolchain pinned by lean-toolchain (no-op if already present).
TOOLCHAIN="$(tr -d '[:space:]' < lean-toolchain)"
if ! elan toolchain list | grep -q "$TOOLCHAIN"; then
  elan toolchain install "$TOOLCHAIN"
else
  echo "==> Toolchain $TOOLCHAIN already installed"
fi

echo "==> Building project"
lake build

echo "==> Environment ready: $(lake --version)"
