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

/-- Pares desde 4 hasta `2 * count + 2` inclusive: `4, 6, …, 2*(count+1)`.
Para llegar a `N` par hace falta `count = N/2 - 1`. -/
def evenNumbersFrom4 (count : ℕ) : List ℕ :=
  (List.range count).map fun i => 2 * i + 4

theorem mem_evenNumbersFrom4 {count n : ℕ} :
    n ∈ evenNumbersFrom4 count ↔ ∃ i < count, n = 2 * i + 4 := by
  simp [evenNumbersFrom4, List.mem_map, List.mem_range]
  constructor <;> rintro ⟨i, hi, h⟩ <;> exact ⟨i, hi, h.symm⟩

/-- Todos los pares entre 4 y 1000 tienen un testigo de Goldbach. -/
private theorem goldbach_witness_upto_1000 :
    (evenNumbersFrom4 499).all goldbachWitness = true := by
  native_decide

/-- La conjetura de Goldbach vale para todo par `n` con `4 ≤ n ≤ 1000`. -/
theorem goldbach_upto_1000 {n : ℕ} (hn₄ : 4 ≤ n) (hnN : n ≤ 1000) (hen : Even n) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  obtain ⟨k, hk⟩ := hen
  have hk2 : n = 2 * k := by omega
  subst hk2
  have hi : k - 2 < 499 := by omega
  have heq : 2 * (k - 2) + 4 = 2 * k := by omega
  have hmem : 2 * (k - 2) + 4 ∈ evenNumbersFrom4 499 :=
    (mem_evenNumbersFrom4).2 ⟨k - 2, hi, rfl⟩
  have hw : goldbachWitness (2 * (k - 2) + 4) = true :=
    (List.all_eq_true.1 goldbach_witness_upto_1000) _ hmem
  rw [← heq]
  exact goldbach_of_witness hw

/-- Caso particular: Goldbach hasta 100. -/
theorem goldbach_upto_100 {n : ℕ} (hn₄ : 4 ≤ n) (hn₁₀₀ : n ≤ 100) (hen : Even n) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q :=
  goldbach_upto_1000 hn₄ (by omega) hen

/-- Ejemplos concretos verificados. -/
theorem goldbach_4 : ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ 4 = p + q :=
  goldbach_upto_1000 (by norm_num) (by norm_num) (by decide)

theorem goldbach_100 : ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ 100 = p + q :=
  goldbach_upto_1000 (by norm_num) (by norm_num) (by decide)

theorem goldbach_1000 : ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ 1000 = p + q :=
  goldbach_upto_1000 (by norm_num) (by norm_num) (by decide)

end GoldbachConjecture
