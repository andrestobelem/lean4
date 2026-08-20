/-
Formalización adaptada de
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/PrimesAndPerfectSquares.lean

Cuarto problema de Landau (abierto): ¿existen infinitos primos de la forma `n² + 1`?
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

open Nat

namespace LandauNsqPlusOne

/--
**Cuarto problema de Landau (abierto).**
¿Existen infinitos primos de la forma `n² + 1`?
-/
theorem infinite_prime_sq_add_one :
    {n : ℕ | Nat.Prime (n ^ 2 + 1)}.Infinite := by
  sorry

/-- Test booleano: `n² + 1` es primo. -/
def isNsqPlusOnePrime (n : ℕ) : Bool :=
  decide (Nat.Prime (n ^ 2 + 1))

theorem isNsqPlusOnePrime_iff (n : ℕ) :
    Nat.Prime (n ^ 2 + 1) ↔ isNsqPlusOnePrime n = true := by
  simp [isNsqPlusOnePrime]

/-- Valores de `n` con `1 ≤ n ≤ 100` para los que `n² + 1` es primo. -/
def nsqPlusOneNsLe100 : List ℕ :=
  [1, 2, 4, 6, 10, 14, 16, 20, 24, 26, 36, 40, 54, 56, 66, 74, 84, 90, 94]

private theorem nsqPlusOne_bool_le_100 :
    (List.range' 1 100).filter isNsqPlusOnePrime = nsqPlusOneNsLe100 := by
  native_decide

/-- Para `1 ≤ n ≤ 100`, `n² + 1` es primo ssi `n` está en `nsqPlusOneNsLe100`. -/
theorem prime_sq_add_one_le_100 {n : ℕ} (hn₁ : 1 ≤ n) (hn : n ≤ 100) :
    Nat.Prime (n ^ 2 + 1) ↔ n ∈ nsqPlusOneNsLe100 := by
  have hmem_range : n ∈ List.range' 1 100 := by
    rw [List.mem_range'_1]
    exact ⟨hn₁, by omega⟩
  constructor
  · intro hp
    have : n ∈ (List.range' 1 100).filter isNsqPlusOnePrime :=
      List.mem_filter.2 ⟨hmem_range, (isNsqPlusOnePrime_iff n).1 hp⟩
    rwa [nsqPlusOne_bool_le_100] at this
  · intro hmem
    have : n ∈ (List.range' 1 100).filter isNsqPlusOnePrime := by
      rwa [nsqPlusOne_bool_le_100]
    exact (isNsqPlusOnePrime_iff n).2 (List.mem_filter.1 this).2

/-- Hay exactamente 19 valores `1 ≤ n ≤ 100` con `n² + 1` primo. -/
theorem nineteen_nsq_plus_one_le_100 :
    nsqPlusOneNsLe100.length = 19 := by
  native_decide

/-- Ejemplos clásicos: `1²+1 = 2`, `2²+1 = 5`, `4²+1 = 17`, `10²+1 = 101`. -/
theorem prime_1_sq_add_one : Nat.Prime (1 ^ 2 + 1) := by decide
theorem prime_2_sq_add_one : Nat.Prime (2 ^ 2 + 1) := by decide
theorem prime_4_sq_add_one : Nat.Prime (4 ^ 2 + 1) := by decide
theorem prime_10_sq_add_one : Nat.Prime (10 ^ 2 + 1) := by native_decide

/-- El conjunto es no vacío (la infinitud sigue abierta). -/
theorem nsq_plus_one_primes_nonempty :
    {n : ℕ | Nat.Prime (n ^ 2 + 1)}.Nonempty :=
  ⟨1, prime_1_sq_add_one⟩

end LandauNsqPlusOne
