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

# Official GitHub CLI (https://github.com/cli/cli/blob/trunk/docs/install_linux.md).
# Ubuntu may ship an older universe package; Cloud Agent images also put
# `/exec-daemon/gh` first on PATH. Install the GitHub apt package and prefer it.
GH_APT_LIST="/etc/apt/sources.list.d/github-cli.list"
GH_APT_KEY="/etc/apt/keyrings/githubcli-archive-keyring.gpg"
if [ -f "${GH_APT_LIST}" ] && dpkg-query -W -f='${Status}' gh 2>/dev/null | grep -q "install ok installed"; then
  echo "==> gh package already present"
else
  echo "==> Installing official GitHub CLI"
  sudo mkdir -p -m 755 /etc/apt/keyrings /etc/apt/sources.list.d
  curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg \
    | sudo tee "${GH_APT_KEY}" >/dev/null
  sudo chmod go+r "${GH_APT_KEY}"
  echo "deb [arch=$(dpkg --print-architecture) signed-by=${GH_APT_KEY}] https://cli.github.com/packages stable main" \
    | sudo tee "${GH_APT_LIST}" >/dev/null
  sudo apt-get update -y
  sudo DEBIAN_FRONTEND=noninteractive apt-get install -y gh
fi
mkdir -p "${HOME}/.local/bin"
ln -sfn /usr/bin/gh "${HOME}/.local/bin/gh"
export PATH="${HOME}/.local/bin:${PATH}"
LOCAL_BIN_LINE='export PATH="$HOME/.local/bin:$PATH"'
for profile in "${HOME}/.bashrc" "${HOME}/.profile"; do
  if [ -e "${profile}" ] && grep -Fq '.local/bin' "${profile}"; then
    continue
  fi
  printf '\n# official GitHub CLI on PATH\n%s\n' "${LOCAL_BIN_LINE}" >> "${profile}"
done
echo "==> gh $(command -v gh) ($(gh --version | head -1))"

TOOLCHAIN="$(tr -d '[:space:]' < lean-toolchain)"
if elan toolchain list | grep -Fq "${TOOLCHAIN}"; then
  echo "==> Toolchain ${TOOLCHAIN} already installed"
else
  echo "==> Installing toolchain ${TOOLCHAIN}"
  elan toolchain install "${TOOLCHAIN}"
fi

# Mathlib is required by this project. Fetch precompiled oleans instead of
# building it from source (which can take hours).
if grep -q 'name = "mathlib"' lakefile.toml 2>/dev/null; then
  echo "==> Fetching Mathlib cache"
  lake exe cache get
fi

echo "==> Building project"
lake build

echo "==> Environment ready: $(lake --version)"
