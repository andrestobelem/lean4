# Git conventions

- Use Conventional Commits with a scope: `type(scope): description` (e.g. `feat(lake): add mathlib dependency`).
- Keep commits atomic: one logical change per commit.
- Never add attribution trailers (no `Co-Authored-By`, no "Generated with" lines, etc.).

# Lean 4

Toolchain is pinned in `lean-toolchain` (elan). Cloud Agent bootstrap is `.cursor/install.sh`.

- Build: `lake build`
- Run the executable: `lake exe lean4`
- After install, `elan`, `lean`, and `lake` are on `PATH` via `$HOME/.elan/bin`.
