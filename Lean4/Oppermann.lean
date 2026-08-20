/-
Formalización adaptada de
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Oppermann.lean
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/LegendreConjecture.lean

Conjeturas abiertas sobre huecos de primos entre cuadrados.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

open Nat

namespace Oppermann

/-- Hay un primo estrictamente entre `lo` y `hi`. -/
def hasPrimeInIoo (lo hi : ℕ) : Bool :=
  (List.range' (lo + 1) (hi - (lo + 1))).any fun p => decide (Nat.Prime p)

theorem mem_range'_Ioo {lo hi p : ℕ} (hle : lo + 1 ≤ hi) :
    p ∈ List.range' (lo + 1) (hi - (lo + 1)) ↔ lo < p ∧ p < hi := by
  rw [List.mem_range'_1]
  constructor
  · intro ⟨h₁, h₂⟩
    refine ⟨Nat.lt_of_succ_le h₁, ?_⟩
    have : lo + 1 + (hi - (lo + 1)) = hi := Nat.add_sub_of_le hle
    omega
  · intro ⟨h₁, h₂⟩
    refine ⟨Nat.succ_le_of_lt h₁, ?_⟩
    have : lo + 1 + (hi - (lo + 1)) = hi := Nat.add_sub_of_le hle
    omega

theorem hasPrimeInIoo_iff {lo hi : ℕ} (hle : lo + 1 ≤ hi) :
    hasPrimeInIoo lo hi = true ↔ ∃ p, lo < p ∧ p < hi ∧ p.Prime := by
  unfold hasPrimeInIoo
  constructor
  · intro h
    obtain ⟨p, hp_mem, hp⟩ := List.any_eq_true.1 h
    refine ⟨p, ?_⟩
    have := (mem_range'_Ioo (p := p) hle).1 hp_mem
    exact ⟨this.1, this.2, of_decide_eq_true hp⟩
  · intro ⟨p, hlo, hhi, hp⟩
    refine List.any_eq_true.2 ⟨p, ?_, decide_eq_true hp⟩
    exact (mem_range'_Ioo (p := p) hle).2 ⟨hlo, hhi⟩

/-- Test booleano de Oppermann para un `x` fijo. -/
def oppermannHolds (x : ℕ) : Bool :=
  hasPrimeInIoo (x * (x - 1)) (x ^ 2) &&
    hasPrimeInIoo (x ^ 2) (x * (x + 1))

private theorem oppermann_bounds {x : ℕ} (hx : 2 ≤ x) :
    x * (x - 1) + 1 ≤ x ^ 2 ∧ x ^ 2 + 1 ≤ x * (x + 1) := by
  have hmul : x * (x - 1) = x * x - x := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  constructor
  · rw [hmul, pow_two]
    have : x ≤ x * x := Nat.le_mul_of_pos_left x (by omega)
    omega
  · rw [Nat.mul_add, Nat.mul_one, pow_two]
    omega

theorem oppermannHolds_iff {x : ℕ} (hx : 2 ≤ x) :
    oppermannHolds x = true ↔
      (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
      (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) := by
  obtain ⟨h₁, h₂⟩ := oppermann_bounds hx
  simp only [oppermannHolds, Bool.and_eq_true, hasPrimeInIoo_iff h₁, hasPrimeInIoo_iff h₂]

/-- Oppermann vale para todo `2 ≤ x ≤ 10000`. -/
private theorem oppermann_bool_upto_10000 :
    (List.range' 2 9999).all oppermannHolds = true := by
  native_decide

theorem oppermann_upto_10000 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 10000) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) := by
  have hmem : x ∈ List.range' 2 9999 := by
    rw [List.mem_range'_1]
    exact ⟨hx₂, by omega⟩
  have hbool : oppermannHolds x = true :=
    (List.all_eq_true.1 oppermann_bool_upto_10000) x hmem
  exact (oppermannHolds_iff hx₂).1 hbool

theorem oppermann_upto_2000 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 2000) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_10000 hx₂ (by omega)

theorem oppermann_upto_500 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 500) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_10000 hx₂ (by omega)

theorem oppermann_upto_200 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 200) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_10000 hx₂ (by omega)

theorem oppermann_upto_100 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 100) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_10000 hx₂ (by omega)

theorem oppermann_upto_50 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 50) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_10000 hx₂ (by omega)

/-- Primer caso a mano: entre 2 y 4 está 3; entre 4 y 6 está 5. -/
theorem oppermann_two_explicit :
    (∃ p, 2 * (2 - 1) < p ∧ p < 2 ^ 2 ∧ p.Prime) ∧
    (∃ p, 2 ^ 2 < p ∧ p < 2 * (2 + 1) ∧ p.Prime) :=
  ⟨⟨3, by decide, by decide, by decide⟩, ⟨5, by decide, by decide, by decide⟩⟩

/-- Segundo caso a mano: entre 6 y 9 está 7; entre 9 y 12 está 11. -/
theorem oppermann_three_explicit :
    (∃ p, 3 * (3 - 1) < p ∧ p < 3 ^ 2 ∧ p.Prime) ∧
    (∃ p, 3 ^ 2 < p ∧ p < 3 * (3 + 1) ∧ p.Prime) :=
  ⟨⟨7, by decide, by decide, by decide⟩, ⟨11, by decide, by decide, by decide⟩⟩

/-- Bertrand aplicado a `x²`: hay un primo en `(x², 2x²]`. Eso es un teorema. -/
theorem bertrand_after_square {x : ℕ} (hx : 0 < x) :
    ∃ p, p.Prime ∧ x ^ 2 < p ∧ p ≤ 2 * x ^ 2 := by
  have hn : x ^ 2 ≠ 0 := (Nat.pow_pos hx).ne'
  simpa [pow_two] using Nat.exists_prime_lt_and_le_two_mul (x ^ 2) hn

/--
El intervalo de Oppermann `(x², x(x+1))` es **estrictamente más corto** que el de Bertrand
`(x², 2x²]`. El resto `(x(x+1), 2x²]` es no vacío, así que el primo de Bertrand puede
caer fuera del intervalo de Oppermann.
-/
theorem bertrand_remainder_nonempty {x : ℕ} (hx : 2 ≤ x) :
    x * (x + 1) < 2 * x ^ 2 := by
  have : x + 1 < 2 * x := by omega
  calc
    x * (x + 1) < x * (2 * x) := Nat.mul_lt_mul_of_pos_left this (by omega)
    _ = 2 * (x * x) := by ring
    _ = 2 * x ^ 2 := by rw [pow_two]

/--
**Conjetura de Oppermann (abierta).**
Para todo `x ≥ 2` hay un primo en `(x(x-1), x²)` y otro en `(x², x(x+1))`.
Los casos `2 ≤ x ≤ 10000` están demostrados. El resto no se deduce de Bertrand:
`bertrand_remainder_nonempty`.
-/
theorem oppermann_conjecture (x : ℕ) (hx : 2 ≤ x) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) := by
  by_cases hle : x ≤ 10000
  · exact oppermann_upto_10000 hx hle
  · sorry

/-- Oppermann implica Legendre (teorema). -/
theorem oppermann_implies_legendre
    (hOpp : ∀ x, 2 ≤ x →
      (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
      (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ p, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime := by
  obtain ⟨⟨p, hp₁, hp₂, hpp⟩, _⟩ := hOpp (n + 1) (by omega)
  refine ⟨p, ?_, hp₂, hpp⟩
  have hmul : (n + 1) * ((n + 1) - 1) = n * (n + 1) := by
    rw [Nat.add_one_sub_one, Nat.mul_comm]
  rw [hmul] at hp₁
  have hsq : n ^ 2 ≤ n * (n + 1) := by
    rw [Nat.mul_add, Nat.mul_one, pow_two]
    omega
  omega

/--
**Conjetura de Legendre (abierta).**
Para todo `n ≥ 1` hay un primo estrictamente entre `n²` y `(n+1)²`.
-/
theorem legendre_conjecture (n : ℕ) (hn : 1 ≤ n) :
    ∃ p, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime := by
  by_cases hle : n ≤ 9999
  · obtain ⟨⟨p, hp₁, hp₂, hpp⟩, _⟩ :=
      oppermann_upto_10000 (x := n + 1) (by omega) (by omega)
    refine ⟨p, ?_, hp₂, hpp⟩
    have hmul : (n + 1) * ((n + 1) - 1) = n * (n + 1) := by
      rw [Nat.add_one_sub_one, Nat.mul_comm]
    rw [hmul] at hp₁
    have hsq : n ^ 2 ≤ n * (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one, pow_two]
      omega
    omega
  · sorry

/-- Test directo de Legendre. -/
def legendreHolds (n : ℕ) : Bool :=
  hasPrimeInIoo (n ^ 2) ((n + 1) ^ 2)

private theorem legendre_bool_upto_50 :
    (List.range' 1 50).all legendreHolds = true := by
  native_decide

theorem legendre_upto_50 {n : ℕ} (hn₁ : 1 ≤ n) (hn : n ≤ 50) :
    ∃ p, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime := by
  have hmem : n ∈ List.range' 1 50 := by
    rw [List.mem_range'_1]
    exact ⟨hn₁, by omega⟩
  have hle : n ^ 2 + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hbool : legendreHolds n = true :=
    (List.all_eq_true.1 legendre_bool_upto_50) n hmem
  exact (hasPrimeInIoo_iff hle).1 hbool

theorem legendre_one : ∃ p, 1 ^ 2 < p ∧ p < 2 ^ 2 ∧ p.Prime :=
  ⟨2, by decide, by decide, by decide⟩

theorem legendre_ten : ∃ p, 10 ^ 2 < p ∧ p < 11 ^ 2 ∧ p.Prime :=
  legendre_upto_50 (by norm_num) (by norm_num)

end Oppermann
