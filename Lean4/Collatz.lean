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

theorem collatzStep_of_even {n : ℕ} (h : n % 2 = 0) : collatzStep n = n / 2 := by
  simp [collatzStep, h]

theorem collatzStep_of_odd {n : ℕ} (h : n % 2 = 1) : collatzStep n = 3 * n + 1 := by
  simp [collatzStep, h]

/-- Si `n` es par y `n/2` llega a 1, entonces `n` llega a 1 en un paso más. -/
theorem collatz_even_succ {n : ℕ} (he : n % 2 = 0)
    (h : ∃ m, collatzStep^[m] (n / 2) = 1) :
    ∃ m, collatzStep^[m] n = 1 := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m + 1, (Function.iterate_succ_apply collatzStep m n).trans
    (by rw [collatzStep_of_even he, hm])⟩

/--
La conjetura de Collatz se reduce a los impares: si todo impar positivo llega a 1,
entonces todo positivo llega a 1.
Este lema es un teorema; la hipótesis sobre los impares sigue abierta.
-/
theorem collatz_of_odd
    (hodd : ∀ n, 0 < n → n % 2 = 1 → ∃ m, collatzStep^[m] n = 1) :
    ∀ n, 0 < n → ∃ m, collatzStep^[m] n = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases he : n % 2 = 0
    · have hn2 : 2 ≤ n := by
        have : n ≠ 1 := fun h => by subst h; cases he
        omega
      have hpos : 0 < n / 2 := Nat.div_pos hn2 (by decide)
      have hlt : n / 2 < n := Nat.div_lt_self hn (by decide : 1 < 2)
      exact collatz_even_succ he (ih (n / 2) hlt hpos)
    · have hodd' : n % 2 = 1 := Nat.mod_two_ne_zero.1 he
      exact hodd n hn hodd'

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

/-- Todos los `n` con `1 ≤ n ≤ 1000` llegan a 1 con a lo sumo 200 pasos. -/
private theorem reachesOne_upto_1000 :
    (List.range' 1 1000).all (fun n => reachesOne n 200) = true := by
  native_decide

/-- La conjetura de Collatz vale para todo `n` con `1 ≤ n ≤ 1000`. -/
theorem collatz_upto_1000 {n : ℕ} (hn₁ : 1 ≤ n) (hn : n ≤ 1000) :
    ∃ m, collatzStep^[m] n = 1 := by
  have hmem : n ∈ List.range' 1 1000 := by
    rw [List.mem_range'_1]
    exact ⟨hn₁, by omega⟩
  have hbool : reachesOne n 200 = true :=
    (List.all_eq_true.1 reachesOne_upto_1000) n hmem
  exact reachesOne_spec hbool

/-- Caso particular: Collatz hasta 100. -/
theorem collatz_upto_100 {n : ℕ} (hn₁ : 1 ≤ n) (hn : n ≤ 100) :
    ∃ m, collatzStep^[m] n = 1 :=
  collatz_upto_1000 hn₁ (by omega)

theorem collatz_1 : ∃ m, collatzStep^[m] 1 = 1 :=
  collatz_upto_1000 (by norm_num) (by norm_num)

theorem collatz_27 : ∃ m, collatzStep^[m] 27 = 1 :=
  collatz_upto_1000 (by norm_num) (by norm_num)

theorem collatz_97 : ∃ m, collatzStep^[m] 97 = 1 :=
  collatz_upto_1000 (by norm_num) (by norm_num)

theorem collatz_871 : ∃ m, collatzStep^[m] 871 = 1 :=
  collatz_upto_1000 (by norm_num) (by norm_num)

end CollatzConjecture
