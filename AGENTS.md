# Git conventions

- Use Conventional Commits with a scope: `type(scope): description` (e.g. `feat(lake): add mathlib dependency`).
- Keep commits atomic: one logical change per commit.
- Never add attribution trailers (no `Co-Authored-By`, no "Generated with" lines, etc.).

# Lean 4

Toolchain is pinned in `lean-toolchain` (elan). Mathlib is pinned to the same tag (`v4.32.2`). Cloud Agent bootstrap is `.cursor/install.sh`.

- After adding or updating Mathlib: `lake update` then `lake exe cache get` (do not compile Mathlib from source).
- Build: `lake build`
- Run the executable: `lake exe lean4`
- First olympiad problem: `Lean4/Imo1959P1.lean` (IMO 1959 Q1).
- After install, `elan`, `lean`, and `lake` are on `PATH` via `$HOME/.elan/bin`.
- GitHub CLI: official `gh` apt package, on `PATH` via `$HOME/.local/bin`.
- GitHub auth: add a **Runtime Secret** named `GH_USER_TOKEN` (a PAT). Do not use `GH_TOKEN`; Cursor overwrites that with the GitHub App token. `.cursor/gh-auth.sh` runs on each boot and logs `gh` in with that PAT.
