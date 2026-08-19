/-
Formalización adaptada de
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/GoldbachConjecture.lean

Conjetura abierta de Goldbach: todo entero par mayor que 2 es suma de dos primos.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

open Nat

namespace GoldbachConjecture

/--
**Conjetura de Goldbach (abierta).**
¿Todo entero par mayor que 2 se puede escribir como suma de dos primos?
-/
theorem goldbach :
    ∀ n : ℕ, 2 < n → Even n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  sorry

/-- Test booleano: ¿existe un primo `p < n` tal que `n - p` también es primo? -/
def goldbachWitness (n : ℕ) : Bool :=
  (List.range n).any fun p => decide (Nat.Prime p) && decide (Nat.Prime (n - p))

theorem goldbach_of_witness {n : ℕ} (h : goldbachWitness n = true) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  unfold goldbachWitness at h
  obtain ⟨p, hp_mem, hp⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨hp_prime, hq_prime⟩ := hp
  refine ⟨p, n - p, hp_prime, hq_prime, ?_⟩
  have : p < n := List.mem_range.1 hp_mem
  omega

/-- Todos los pares entre 4 y 100 tienen un testigo de Goldbach. -/
private theorem goldbach_witness_upto_100 :
    ((List.range 49).map fun i => 2 * i + 4).all goldbachWitness = true := by
  native_decide

/-- La conjetura de Goldbach vale para todo par `n` con `4 ≤ n ≤ 100`. -/
theorem goldbach_upto_100 {n : ℕ} (hn₄ : 4 ≤ n) (hn₁₀₀ : n ≤ 100) (hen : Even n) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  obtain ⟨k, hk⟩ := hen
  -- `n = k + k`, so `n = 2 * k` and `2 ≤ k ≤ 50`
  have hk2 : n = 2 * k := by omega
  subst hk2
  have hi : k - 2 < 49 := by omega
  have hmem : 2 * (k - 2) + 4 ∈ (List.range 49).map fun j => 2 * j + 4 := by
    refine List.mem_map.2 ⟨k - 2, List.mem_range.2 hi, ?_⟩
    omega
  have hall := goldbach_witness_upto_100
  have hw : goldbachWitness (2 * (k - 2) + 4) = true :=
    (List.all_eq_true.1 hall) _ hmem
  have : 2 * (k - 2) + 4 = 2 * k := by omega
  rw [← this]
  exact goldbach_of_witness hw

/-- Ejemplos concretos verificados. -/
theorem goldbach_4 : ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ 4 = p + q :=
  goldbach_upto_100 (by norm_num) (by norm_num) (by decide)

theorem goldbach_100 : ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ 100 = p + q :=
  goldbach_upto_100 (by norm_num) (by norm_num) (by decide)

end GoldbachConjecture
