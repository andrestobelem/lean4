/-
Formalización adaptada de
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/WoodalPrimes.lean

Conjetura abierta: existen infinitos primos de Woodall (de la forma k·2^k − 1, con k > 1).
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

open Nat

namespace WoodallPrimes

/-- Un entero de Woodall es de la forma `k * 2 ^ k - 1`. -/
def woodall (k : ℕ) : ℕ := k * 2 ^ k - 1

/-- Conjetura abierta: infinitos primos de Woodall. -/
theorem infinitely_many_woodall_primes :
    {k : ℕ | 1 < k ∧ (woodall k).Prime}.Infinite := by
  sorry

/-- El entero de Woodall con k = 2 es el primo 7. -/
theorem woodall_two_is_seven : woodall 2 = 7 := by
  norm_num [woodall]

/-- El entero de Woodall con k = 3 es el primo 23. -/
theorem woodall_three_is_twentyThree : woodall 3 = 23 := by
  norm_num [woodall]

/-- El entero de Woodall con k = 6 es el primo 383. -/
theorem woodall_six_is_383 : woodall 6 = 383 := by
  norm_num [woodall]

/-- El entero de Woodall con k = 30 es `32212254719`. -/
theorem woodall_thirty : woodall 30 = 32212254719 := by
  native_decide

theorem woodall_prime_two : (woodall 2).Prime := by
  rw [woodall_two_is_seven]
  native_decide

theorem woodall_prime_three : (woodall 3).Prime := by
  rw [woodall_three_is_twentyThree]
  native_decide

theorem woodall_prime_six : (woodall 6).Prime := by
  rw [woodall_six_is_383]
  native_decide

/-- El Woodall número con k = 30 es primo. -/
theorem woodall_prime_thirty : (woodall 30).Prime := by
  rw [woodall_thirty]
  native_decide

/-- Existe al menos un primo de Woodall (aunque la infinitud sigue abierta). -/
theorem exists_woodall_prime :
    ∃ k, 1 < k ∧ (woodall k).Prime :=
  ⟨2, by decide, woodall_prime_two⟩

/-- Hay al menos cuatro índices k ∈ {2, 3, 6, 30} que dan primos de Woodall. -/
theorem four_woodall_primes :
    ({2, 3, 6, 30} : Set ℕ) ⊆ {k : ℕ | 1 < k ∧ (woodall k).Prime} := by
  intro k hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with (rfl | rfl | rfl | rfl)
  · exact ⟨by decide, woodall_prime_two⟩
  · exact ⟨by decide, woodall_prime_three⟩
  · exact ⟨by decide, woodall_prime_six⟩
  · exact ⟨by decide, woodall_prime_thirty⟩

end WoodallPrimes
