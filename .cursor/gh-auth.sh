#!/usr/bin/env bash
# Authenticate the official GitHub CLI as the operator.
# Cursor injects a GitHub App installation token as GH_TOKEN (ghs_...); that
# token can clone/push but often cannot create PRs as a user. A personal PAT
# must be supplied as the Runtime Secret GH_USER_TOKEN (not GH_TOKEN).
set -euo pipefail

export PATH="${HOME}/.local/bin:/usr/bin:${PATH}"

if [ -z "${GH_USER_TOKEN:-}" ]; then
  echo "==> GH_USER_TOKEN unset; gh uses the Cursor GitHub App token"
  exit 0
fi

echo "==> Authenticating gh with GH_USER_TOKEN"
printf '%s\n' "${GH_USER_TOKEN}" | gh auth login --with-token --hostname github.com
gh auth status --hostname github.com
