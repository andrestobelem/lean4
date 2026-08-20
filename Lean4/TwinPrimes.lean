/-
Formalización adaptada de
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/TwinPrimes.lean

Conjetura abierta de los primos gemelos: existen infinitos primos `p` tales que `p + 2` también es primo.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

open Nat

namespace TwinPrimes

/-- Un primo gemelo es un primo `p` tal que `p + 2` también es primo. -/
def IsTwinPrime (p : ℕ) : Prop :=
  p.Prime ∧ (p + 2).Prime

instance (p : ℕ) : Decidable (IsTwinPrime p) :=
  inferInstanceAs (Decidable (p.Prime ∧ (p + 2).Prime))

/--
**Conjetura de los primos gemelos (abierta).**
¿Existen infinitos primos `p` tales que `p + 2` también es primo?
-/
theorem twin_primes : Set.Infinite {p : ℕ | IsTwinPrime p} := by
  sorry

/-- Pares gemelos clásicos. -/
theorem twin_3 : IsTwinPrime 3 := by decide
theorem twin_5 : IsTwinPrime 5 := by decide
theorem twin_11 : IsTwinPrime 11 := by decide
theorem twin_17 : IsTwinPrime 17 := by decide
theorem twin_29 : IsTwinPrime 29 := by decide
theorem twin_41 : IsTwinPrime 41 := by decide
theorem twin_59 : IsTwinPrime 59 := by decide
theorem twin_71 : IsTwinPrime 71 := by decide

/-- Test booleano para primos gemelos. -/
def isTwinPrimeBool (p : ℕ) : Bool :=
  decide (Nat.Prime p) && decide (Nat.Prime (p + 2))

theorem isTwinPrime_iff_bool (p : ℕ) :
    IsTwinPrime p ↔ isTwinPrimeBool p = true := by
  simp [IsTwinPrime, isTwinPrimeBool]

/-- Lista de primos gemelos estrictamente menores que 100. -/
private theorem twin_bool_list_lt_100 :
    (List.range 100).filter isTwinPrimeBool =
      [3, 5, 11, 17, 29, 41, 59, 71] := by
  native_decide

/-- Por debajo de 100, los primos gemelos son exactamente estos ocho. -/
theorem twin_primes_below_100 :
    {p : ℕ | p < 100 ∧ IsTwinPrime p} =
      ({3, 5, 11, 17, 29, 41, 59, 71} : Set ℕ) := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨hlt, hT⟩
    have hmem : p ∈ (List.range 100).filter isTwinPrimeBool := by
      rw [List.mem_filter, List.mem_range]
      exact ⟨hlt, (isTwinPrime_iff_bool p).1 hT⟩
    rw [twin_bool_list_lt_100] at hmem
    simpa using hmem
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨by norm_num, twin_3⟩
    · exact ⟨by norm_num, twin_5⟩
    · exact ⟨by norm_num, twin_11⟩
    · exact ⟨by norm_num, twin_17⟩
    · exact ⟨by norm_num, twin_29⟩
    · exact ⟨by norm_num, twin_41⟩
    · exact ⟨by norm_num, twin_59⟩
    · exact ⟨by norm_num, twin_71⟩

/-- El conjunto de primos gemelos es no vacío (la infinitud sigue abierta). -/
theorem twin_primes_nonempty : {p : ℕ | IsTwinPrime p}.Nonempty :=
  ⟨3, twin_3⟩

/-- Hay exactamente ocho primos gemelos menores que 100. -/
theorem eight_twin_primes_below_100 :
    ((List.range 100).filter isTwinPrimeBool).length = 8 := by
  rw [twin_bool_list_lt_100]
  decide

/-- Los 35 primos gemelos estrictamente menores que 1000. -/
def twinPrimesLt1000 : List ℕ :=
  [3, 5, 11, 17, 29, 41, 59, 71, 101, 107, 137, 149, 179, 191, 197, 227, 239,
    269, 281, 311, 347, 419, 431, 461, 521, 569, 599, 617, 641, 659, 809, 821,
    827, 857, 881]

private theorem twin_bool_list_lt_1000 :
    (List.range 1000).filter isTwinPrimeBool = twinPrimesLt1000 := by
  native_decide

/-- Por debajo de 1000, `p` es primo gemelo ssi aparece en `twinPrimesLt1000`. -/
theorem isTwinPrime_lt_1000 {p : ℕ} (hlt : p < 1000) :
    IsTwinPrime p ↔ p ∈ twinPrimesLt1000 := by
  constructor
  · intro hT
    have : p ∈ (List.range 1000).filter isTwinPrimeBool :=
      List.mem_filter.2 ⟨List.mem_range.2 hlt, (isTwinPrime_iff_bool p).1 hT⟩
    rwa [twin_bool_list_lt_1000] at this
  · intro hmem
    have : p ∈ (List.range 1000).filter isTwinPrimeBool := by
      rwa [twin_bool_list_lt_1000]
    exact (isTwinPrime_iff_bool p).2 (List.mem_filter.1 this).2

/-- Hay exactamente 35 primos gemelos menores que 1000. -/
theorem thirtyFive_twin_primes_below_1000 :
    twinPrimesLt1000.length = 35 := by
  native_decide

/-- Todo elemento de `twinPrimesLt1000` es un primo gemelo. -/
theorem mem_twinPrimesLt1000 {p : ℕ} (hp : p ∈ twinPrimesLt1000) :
    IsTwinPrime p := by
  have hmem : p ∈ (List.range 1000).filter isTwinPrimeBool := by
    rwa [twin_bool_list_lt_1000]
  exact (isTwinPrime_iff_bool p).2 (List.mem_filter.1 hmem).2

end TwinPrimes
