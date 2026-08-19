/-
Formalización adaptada de
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/WilsonPrime.lean

Conjetura abierta: existen infinitos primos de Wilson.
Los únicos ejemplos conocidos son 5, 13 y 563.
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

open Nat

namespace WilsonPrime

/-- Un primo de Wilson es un primo `p` tal que `p² ∣ (p-1)! + 1`. -/
def IsWilsonPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ (p - 1).factorial + 1

/-- Existen infinitos primos de Wilson (conjetura abierta). -/
theorem infinitely_many_wilson_primes : Set.Infinite {p : ℕ | IsWilsonPrime p} := by
  sorry

private theorem prime_563 : Nat.Prime 563 := by
  native_decide

private theorem wilson_div_563 : (563 * 563) ∣ Nat.factorial 562 + 1 := by
  native_decide

/-- El primo 5 es un primo de Wilson. -/
theorem isWilsonPrime_five : IsWilsonPrime 5 := by
  norm_num [IsWilsonPrime, Nat.factorial]

/-- El primo 13 es un primo de Wilson. -/
theorem isWilsonPrime_thirteen : IsWilsonPrime 13 := by
  norm_num [IsWilsonPrime, Nat.factorial]

/-- El primo 563 es el tercer primo de Wilson conocido. -/
theorem isWilsonPrime_563 : IsWilsonPrime 563 := by
  refine ⟨prime_563, ?_⟩
  simpa [pow_two] using wilson_div_563

/-- Los tres primos de Wilson conocidos pertenecen al conjunto. -/
theorem known_wilson_primes :
    IsWilsonPrime 5 ∧ IsWilsonPrime 13 ∧ IsWilsonPrime 563 :=
  ⟨isWilsonPrime_five, isWilsonPrime_thirteen, isWilsonPrime_563⟩

/-- El conjunto de primos de Wilson es no vacío (la infinitud sigue abierta). -/
theorem wilson_primes_nonempty : {p : ℕ | IsWilsonPrime p}.Nonempty :=
  ⟨563, isWilsonPrime_563⟩

/-- La condición de primalidad excluye 1, que cumple la divisibilidad por sí sola. -/
theorem not_isWilsonPrime_one : ¬ IsWilsonPrime 1 := by
  norm_num [IsWilsonPrime]

/-- El primo 7 no es un primo de Wilson. -/
theorem not_isWilsonPrime_seven : ¬ IsWilsonPrime 7 := by
  norm_num [IsWilsonPrime, Nat.factorial]

end WilsonPrime
