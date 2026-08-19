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

instance (p : ℕ) : Decidable (IsWilsonPrime p) :=
  inferInstanceAs (Decidable (p.Prime ∧ p ^ 2 ∣ (p - 1).factorial + 1))

/-- Factorial módulo `m` (evita enteros enormes al comprobar la condición de Wilson). -/
def factMod : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, m => (factMod n m * (n + 1)) % m

theorem factMod_eq_factorial_mod (n m : ℕ) (hm : 1 < m) :
    factMod n m = n.factorial % m := by
  induction n with
  | zero =>
    change (1 : ℕ) = 1 % m
    exact (Nat.mod_eq_of_lt hm).symm
  | succ n ih =>
    simp only [factMod, Nat.factorial_succ]
    rw [ih]
    calc
      (n.factorial % m * (n + 1)) % m
          = (n.factorial % m * ((n + 1) % m)) % m := by
            rw [Nat.mul_mod, Nat.mod_mod]
          _ = (n.factorial * (n + 1)) % m := by
            rw [← Nat.mul_mod]
          _ = ((n + 1) * n.factorial) % m := by
            rw [Nat.mul_comm]

/-- Comprobación booleana eficiente de la condición de Wilson. -/
def isWilsonPrimeBool (p : ℕ) : Bool :=
  decide (Nat.Prime p) && (factMod (p - 1) (p * p) + 1) % (p * p) == 0

private theorem dvd_iff_factMod {a m : ℕ} (hm : 1 < m) :
    m ∣ a + 1 ↔ (a % m + 1) % m = 0 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_eq_of_lt hm]

theorem isWilsonPrime_iff_bool {p : ℕ} (hp : Nat.Prime p) :
    IsWilsonPrime p ↔ isWilsonPrimeBool p = true := by
  have hmod : 1 < p * p := by nlinarith [hp.two_le]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨-, hdiv⟩ := h
    have : (factMod (p - 1) (p * p) + 1) % (p * p) = 0 := by
      rw [factMod_eq_factorial_mod _ _ hmod]
      exact (dvd_iff_factMod (a := (p - 1).factorial) hmod).1 (by convert hdiv using 1; rw [pow_two])
    simp [isWilsonPrimeBool, hp, this]
  · have hprime : decide (Nat.Prime p) = true := decide_eq_true hp
    have hcond : (factMod (p - 1) (p * p) + 1) % (p * p) = 0 := by
      simpa [isWilsonPrimeBool, hprime] using h
    refine ⟨hp, ?_⟩
    rw [pow_two, dvd_iff_factMod (a := (p - 1).factorial) hmod,
      ← factMod_eq_factorial_mod _ _ hmod]
    exact hcond

theorem isWilsonPrime_iff_bool' {p : ℕ} :
    IsWilsonPrime p ↔ isWilsonPrimeBool p = true := by
  by_cases hp : Nat.Prime p
  · exact isWilsonPrime_iff_bool hp
  · simp [isWilsonPrimeBool, IsWilsonPrime, hp]

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

/-- Lista de primos de Wilson estrictamente menores que 563. -/
private theorem wilson_bool_list_lt_563 :
    (List.range' 2 561).filter isWilsonPrimeBool = [5, 13] := by
  native_decide

/-- Por debajo de 563, los únicos primos de Wilson son 5 y 13. -/
theorem isWilsonPrime_lt_563 {p : ℕ} (hlt : p < 563) :
    IsWilsonPrime p ↔ p = 5 ∨ p = 13 := by
  constructor
  · intro hW
    have hmem : p ∈ (List.range' 2 561).filter isWilsonPrimeBool := by
      rw [List.mem_filter, List.mem_range'_1]
      refine ⟨⟨hW.1.two_le, by omega⟩, isWilsonPrime_iff_bool'.1 hW⟩
    rw [wilson_bool_list_lt_563] at hmem
    simpa using hmem
  · rintro (rfl | rfl)
    · exact isWilsonPrime_five
    · exact isWilsonPrime_thirteen

/-- El conjunto de primos de Wilson menores que 563 es exactamente `{5, 13}`. -/
theorem wilson_primes_below_563 :
    {p : ℕ | p < 563 ∧ IsWilsonPrime p} = ({5, 13} : Set ℕ) := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨hlt, hW⟩
    exact (isWilsonPrime_lt_563 hlt).1 hW
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, isWilsonPrime_five⟩
    · exact ⟨by norm_num, isWilsonPrime_thirteen⟩

end WilsonPrime
