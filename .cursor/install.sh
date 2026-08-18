#!/usr/bin/env bash
# Idempotent Cloud Agent bootstrap for this Lean 4 / Lake project.
# Installs elan if missing, ensures the pinned toolchain from `lean-toolchain`
# is available, and builds the project.
set -euo pipefail

ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export PATH="${ELAN_HOME}/bin:${PATH}"

if [ ! -x "${ELAN_HOME}/bin/elan" ]; then
  echo "==> Installing elan"
  curl -fsSL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh
  # --default-toolchain none: let elan pick the version from lean-toolchain.
  sh /tmp/elan-init.sh -y --default-toolchain none
  rm -f /tmp/elan-init.sh
else
  echo "==> elan already installed"
fi

if [ -f "${ELAN_HOME}/env" ]; then
  # shellcheck disable=SC1090
  . "${ELAN_HOME}/env"
fi
export PATH="${ELAN_HOME}/bin:${PATH}"

# Persist PATH for later non-interactive agent shells, without duplicating.
ELAN_PATH_LINE='export PATH="$HOME/.elan/bin:$PATH"'
for profile in "${HOME}/.bashrc" "${HOME}/.profile"; do
  if [ -e "${profile}" ] && grep -Fq '.elan/bin' "${profile}"; then
    continue
  fi
  printf '\n# elan (Lean toolchain)\n%s\n' "${ELAN_PATH_LINE}" >> "${profile}"
done

echo "==> elan $(elan --version)"

TOOLCHAIN="$(tr -d '[:space:]' < lean-toolchain)"
if elan toolchain list | grep -Fq "${TOOLCHAIN}"; then
  echo "==> Toolchain ${TOOLCHAIN} already installed"
else
  echo "==> Installing toolchain ${TOOLCHAIN}"
  elan toolchain install "${TOOLCHAIN}"
fi

echo "==> Building project"
lake build

echo "==> Environment ready: $(lake --version)"
