/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker

Adapted from mathlib4 Archive/Imo/Imo1959Q1.lean (tag v4.32.2) /
Compfiles Imo1959P1, the first International Mathematical Olympiad problem.
-/
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Prime.Basic

/-!
# IMO 1959 Q1

Prove that the fraction `(21n+4)/(14n+3)` is irreducible for every natural number `n`.

Since Lean doesn't have a concept of "irreducible fractions" per se, we just formalize this
as saying the numerator and denominator are relatively prime.
-/

open Nat

namespace Imo1959P1

theorem calculation (n k : ℕ) (h1 : k ∣ 21 * n + 4) (h2 : k ∣ 14 * n + 3) : k ∣ 1 :=
  have h3 : k ∣ 2 * (21 * n + 4) := h1.mul_left 2
  have h4 : k ∣ 3 * (14 * n + 3) := h2.mul_left 3
  have h5 : 3 * (14 * n + 3) = 2 * (21 * n + 4) + 1 := by ring
  (Nat.dvd_add_right h3).mp (h5 ▸ h4)

theorem imo1959_p1 : ∀ n : ℕ, Coprime (21 * n + 4) (14 * n + 3) := fun n =>
  coprime_of_dvd' fun k _ h1 h2 => calculation n k h1 h2

end Imo1959P1
