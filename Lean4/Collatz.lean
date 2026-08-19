/-
Formalización adaptada de
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/CollatzConjecture.lean

Conjetura de Collatz (abierta): toda órbita llega a 1.
-/
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

open Nat

namespace CollatzConjecture

/-- Un paso de Collatz: si `n` es par, `n/2`; si es impar, `3n+1`. -/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/--
**Conjetura de Collatz (abierta).**
Para todo entero positivo `n` existe `m` tal que el `m`-ésimo iterado de `collatzStep` es 1.
-/
theorem collatz_conjecture (n : ℕ) (hn : 0 < n) :
    ∃ m, collatzStep^[m] n = 1 := by
  sorry

/-- ¿Llega `n` a 1 en a lo sumo `fuel` pasos? -/
def reachesOne : ℕ → ℕ → Bool
  | n, 0 => n == 1
  | n, fuel + 1 => n == 1 || reachesOne (collatzStep n) fuel

theorem reachesOne_spec {n fuel : ℕ} (h : reachesOne n fuel = true) :
    ∃ m, collatzStep^[m] n = 1 := by
  induction fuel generalizing n with
  | zero =>
    simp [reachesOne, beq_iff_eq] at h
    exact ⟨0, by simp [h]⟩
  | succ fuel ih =>
    simp [reachesOne, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with hn1 | h'
    · exact ⟨0, by simp [hn1]⟩
    · obtain ⟨m, hm⟩ := ih h'
      exact ⟨m + 1, (Function.iterate_succ_apply collatzStep m n).trans hm⟩

/-- Todos los `n` con `1 ≤ n ≤ 100` llegan a 1 con a lo sumo 200 pasos. -/
private theorem reachesOne_upto_100 :
    (List.range' 1 100).all (fun n => reachesOne n 200) = true := by
  native_decide

/-- La conjetura de Collatz vale para todo `n` con `1 ≤ n ≤ 100`. -/
theorem collatz_upto_100 {n : ℕ} (hn₁ : 1 ≤ n) (hn : n ≤ 100) :
    ∃ m, collatzStep^[m] n = 1 := by
  have hmem : n ∈ List.range' 1 100 := by
    rw [List.mem_range'_1]
    exact ⟨hn₁, by omega⟩
  have hbool : reachesOne n 200 = true :=
    (List.all_eq_true.1 reachesOne_upto_100) n hmem
  exact reachesOne_spec hbool

theorem collatz_1 : ∃ m, collatzStep^[m] 1 = 1 :=
  collatz_upto_100 (by norm_num) (by norm_num)

theorem collatz_27 : ∃ m, collatzStep^[m] 27 = 1 :=
  collatz_upto_100 (by norm_num) (by norm_num)

theorem collatz_97 : ∃ m, collatzStep^[m] 97 = 1 :=
  collatz_upto_100 (by norm_num) (by norm_num)

end CollatzConjecture
