/-
Formalización adaptada de
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Oppermann.lean
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/LegendreConjecture.lean

Conjeturas abiertas sobre huecos de primos entre cuadrados.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

open Nat
open ArithmeticFunction
open scoped Nat.Prime
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

namespace Oppermann

/-! ## Intervalos y la función π -/

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

/-- Primer impar estrictamente mayor que `lo`. -/
def firstOddGt (lo : ℕ) : ℕ := lo + 1 + lo % 2

theorem firstOddGt_odd (lo : ℕ) : Odd (firstOddGt lo) := by
  unfold firstOddGt
  rcases Nat.mod_two_eq_zero_or_one lo with h | h
  · exact ⟨lo / 2, by omega⟩
  · exact ⟨lo / 2 + 1, by omega⟩

theorem lo_lt_firstOddGt (lo : ℕ) : lo < firstOddGt lo := by
  unfold firstOddGt
  omega

theorem firstOddGt_le_of_odd_gt {lo p : ℕ} (hp : Odd p) (h : lo < p) :
    firstOddGt lo ≤ p := by
  unfold firstOddGt
  rcases hp with ⟨k, hk⟩
  omega

/-- Búsqueda que salta los pares. En los intervalos de Oppermann (`lo ≥ 2`) no se pierde el 2. -/
def hasOddPrimeInIoo (lo hi : ℕ) : Bool :=
  (List.range' (firstOddGt lo) ((hi - firstOddGt lo + 1) / 2) 2).any fun p =>
    decide (Nat.Prime p)

private theorem last_odd_lt_hi {lo hi : ℕ} {i : ℕ}
    (hi_pos : i < (hi - firstOddGt lo + 1) / 2) :
    firstOddGt lo + 2 * i < hi := by
  have hmul : 2 * ((hi - firstOddGt lo + 1) / 2) ≤ hi - firstOddGt lo + 1 :=
    Nat.mul_div_le _ _
  have : 2 * i + 2 ≤ 2 * ((hi - firstOddGt lo + 1) / 2) := by
    have := Nat.succ_le_of_lt hi_pos
    nlinarith
  omega

theorem hasOddPrimeInIoo_iff {lo hi : ℕ} (hlo : 2 ≤ lo) (_hle : lo + 1 ≤ hi) :
    hasOddPrimeInIoo lo hi = true ↔ ∃ p, lo < p ∧ p < hi ∧ p.Prime := by
  unfold hasOddPrimeInIoo
  constructor
  · intro h
    obtain ⟨p, hp_mem, hp⟩ := List.any_eq_true.1 h
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hp_mem
    refine ⟨firstOddGt lo + 2 * i, ?_, last_odd_lt_hi hi, of_decide_eq_true hp⟩
    have := lo_lt_firstOddGt lo
    omega
  · intro ⟨p, hlt, hhi, hp⟩
    have hp_ne_two : p ≠ 2 := by omega
    have hp_odd : Odd p := (hp.eq_two_or_odd'.resolve_left hp_ne_two)
    have hstart : firstOddGt lo ≤ p := firstOddGt_le_of_odd_gt hp_odd hlt
    have hstep : 2 ∣ p - firstOddGt lo := by
      rcases firstOddGt_odd lo with ⟨k, hk⟩
      rcases hp_odd with ⟨k', hk'⟩
      omega
    obtain ⟨i, hi_eq⟩ := hstep
    have hp' : p = firstOddGt lo + 2 * i := by omega
    have hi_lt : i < (hi - firstOddGt lo + 1) / 2 := by
      have : 2 * i < hi - firstOddGt lo := by omega
      omega
    refine List.any_eq_true.2 ⟨p, ?_, decide_eq_true hp⟩
    exact List.mem_range'.2 ⟨i, hi_lt, hp'⟩

/-- `π a < π b` si y solo si hay un primo en el intervalo semiabierto `(a, b]`. -/
theorem primeCounting_lt_iff {a b : ℕ} :
    π a < π b ↔ ∃ p, a < p ∧ p ≤ b ∧ p.Prime := by
  constructor
  · intro h
    obtain ⟨p, hpIco, hp⟩ := exists_of_count_lt_count (p := Nat.Prime) h
    rw [Set.mem_Ico] at hpIco
    exact ⟨p, by omega, by omega, hp⟩
  · intro ⟨p, hap, hpb, hp⟩
    have hle : count Nat.Prime (a + 1) ≤ count Nat.Prime p :=
      count_monotone _ (Nat.succ_le_of_lt hap)
    have hlt : count Nat.Prime p < count Nat.Prime (b + 1) :=
      count_strict_mono hp (Nat.lt_succ_of_le hpb)
    simpa [primeCounting, primeCounting'] using hle.trans_lt hlt

/-- Hay un primo en `(lo, hi)` si y solo si `π(lo) < π(hi − 1)`. -/
theorem exists_prime_Ioo_iff_pi {lo hi : ℕ} (hhi : 1 ≤ hi) :
    (∃ p, lo < p ∧ p < hi ∧ p.Prime) ↔ π lo < π (hi - 1) := by
  constructor
  · intro ⟨p, hlo, hlt, hp⟩
    exact primeCounting_lt_iff.2 ⟨p, hlo, Nat.le_sub_one_of_lt hlt, hp⟩
  · intro h
    obtain ⟨p, hlo, hle, hp⟩ := primeCounting_lt_iff.1 h
    exact ⟨p, hlo, lt_of_le_of_lt hle (Nat.sub_lt hhi (by decide : (0 : ℕ) < 1)), hp⟩

theorem not_prime_sq {x : ℕ} (hx : 2 ≤ x) : ¬ (x ^ 2).Prime := by
  rw [pow_two]
  exact Nat.not_prime_mul (by omega) (by omega)

theorem not_prime_pronic {x : ℕ} (hx : 2 ≤ x) : ¬ (x * (x + 1)).Prime :=
  Nat.not_prime_mul (by omega) (by omega)

theorem primeCounting_pred_of_not_prime {n : ℕ} (hn : n ≠ 0) (hp : ¬ n.Prime) :
    π n.pred = π n := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    simp [primeCounting, primeCounting', count_succ, hp]

/-- Los extremos de Oppermann: `x(x−1) = x² − x` y `x(x+1) = x² + x`. -/
theorem oppermann_interval_eq {x : ℕ} :
    x * (x - 1) = x ^ 2 - x ∧ x * (x + 1) = x ^ 2 + x := by
  constructor
  · rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_two]
  · rw [Nat.mul_add, Nat.mul_one, pow_two]

/-- El primorial crece en `(m, m+k]` si y solo si hay un primo en ese intervalo. -/
theorem primorial_lt_add_iff {m k : ℕ} (_hk : 0 < k) :
    primorial m < primorial (m + k) ↔ ∃ p, m < p ∧ p ≤ m + k ∧ p.Prime := by
  rw [primorial_add m k]
  have hP := primorial_pos m
  constructor
  · intro h
    have hprod : 1 < ∏ p ∈ Finset.Ico (m + 1) (m + k + 1) with p.Prime, p :=
      (Nat.lt_mul_iff_one_lt_right hP).1 h
    by_contra hnone
    have hempty : (Finset.Ico (m + 1) (m + k + 1)).filter Prime = ∅ := by
      refine Finset.filter_eq_empty_iff.2 ?_
      intro p hp hp'
      simp only [Finset.mem_Ico] at hp
      exact hnone ⟨p, Nat.lt_of_succ_le hp.1, Nat.lt_succ_iff.mp hp.2, hp'⟩
    simp [hempty] at hprod
  · intro ⟨p, hp1, hp2, hpp⟩
    have hmem : p ∈ (Finset.Ico (m + 1) (m + k + 1)).filter Prime := by
      simp [Finset.mem_filter, Finset.mem_Ico, hpp, Nat.succ_le_of_lt hp1,
        Nat.lt_succ_of_le hp2]
    have hge : p ≤ ∏ q ∈ Finset.Ico (m + 1) (m + k + 1) with q.Prime, q :=
      Finset.single_le_prod' (fun q hq => (Finset.mem_filter.mp hq).2.one_lt.le) hmem
    exact (Nat.lt_mul_iff_one_lt_right hP).2 (hpp.one_lt.trans_le hge)

/-- Oppermann en forma de primorial: `x(x−1)# < x²# < x(x+1)#`. -/
theorem oppermann_iff_primorial {x : ℕ} (hx : 2 ≤ x) :
    ((∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
      (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime)) ↔
      primorial (x * (x - 1)) < primorial (x ^ 2) ∧
        primorial (x ^ 2) < primorial (x * (x + 1)) := by
  obtain ⟨hL, hR⟩ := oppermann_interval_eq (x := x)
  have hk : 0 < x := by omega
  have h₁ : x * (x - 1) + x = x ^ 2 := by
    have : x ≤ x * x := Nat.le_mul_of_pos_left x hk
    rw [hL, pow_two]
    omega
  have h₂ : x ^ 2 + x = x * (x + 1) := hR.symm
  constructor
  · intro ⟨⟨p, hp₁, hp₂, hpp⟩, ⟨q, hq₁, hq₂, hqp⟩⟩
    have hLπ : primorial (x * (x - 1)) < primorial (x * (x - 1) + x) :=
      (primorial_lt_add_iff hk).2 ⟨p, hp₁, by omega, hpp⟩
    have hRπ : primorial (x ^ 2) < primorial (x ^ 2 + x) :=
      (primorial_lt_add_iff hk).2 ⟨q, hq₁, by omega, hqp⟩
    rw [h₁] at hLπ
    rw [h₂] at hRπ
    exact ⟨hLπ, hRπ⟩
  · intro ⟨hπL, hπR⟩
    have hL' := (primorial_lt_add_iff (m := x * (x - 1)) hk).1 (h₁ ▸ hπL)
    have hR' := (primorial_lt_add_iff (m := x ^ 2) hk).1 (h₂ ▸ hπR)
    obtain ⟨p, hp₁, hp₂, hpp⟩ := hL'
    obtain ⟨q, hq₁, hq₂, hqp⟩ := hR'
    refine ⟨⟨p, hp₁, ?_, hpp⟩, ⟨q, hq₁, ?_, hqp⟩⟩
    · have : p ≠ x ^ 2 := fun heq => (not_prime_sq hx) (heq ▸ hpp)
      rw [h₁] at hp₂
      omega
    · have : q ≠ x * (x + 1) := fun heq => (not_prime_pronic hx) (heq ▸ hqp)
      rw [h₂] at hq₂
      omega

/-- Si hay primos en las ventanas de longitud `√(x²) = x` alrededor de `x²`, vale Oppermann. -/
theorem oppermann_of_sqrt_window {x : ℕ} (_hx : 2 ≤ x)
    (hL : ∃ p, x ^ 2 - (x ^ 2).sqrt < p ∧ p < x ^ 2 ∧ p.Prime)
    (hR : ∃ p, x ^ 2 < p ∧ p < x ^ 2 + (x ^ 2).sqrt ∧ p.Prime) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) := by
  rw [Nat.sqrt_eq'] at hL hR
  obtain ⟨h₁, h₂⟩ := oppermann_interval_eq (x := x)
  constructor
  · simpa [h₁] using hL
  · simpa [h₂] using hR

/-- `x(x+1) < (x+1)²`, así que el intervalo derecho de Oppermann cabe bajo el siguiente cuadrado. -/
theorem pronic_lt_succ_sq {x : ℕ} : x * (x + 1) < (x + 1) ^ 2 := by
  rw [pow_two, Nat.mul_add, Nat.mul_one]
  nlinarith

/-- Si `m < (x+1)²` y `minFac m > x`, entonces `m` es primo. -/
theorem prime_of_minFac_gt_of_lt_succ_sq {x m : ℕ} (hm : 1 < m)
    (hbound : m < (x + 1) ^ 2) (hfac : x < m.minFac) : m.Prime := by
  by_contra hnp
  have hsq := minFac_sq_le_self (by omega) hnp
  have hx1 : x + 1 ≤ m.minFac := Nat.succ_le_of_lt hfac
  have : (x + 1) ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hx1 2
  omega

/-- Si `m < x²` y `minFac m ≥ x`, entonces `m` es primo. -/
theorem prime_of_minFac_ge_of_lt_sq {x m : ℕ} (hm : 1 < m) (hbound : m < x ^ 2)
    (hfac : x ≤ m.minFac) : m.Prime := by
  by_contra hnp
  have hsq := minFac_sq_le_self (by omega) hnp
  have : x ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hfac 2
  omega

/-- Un compuesto en `(x², x(x+1))` tiene un factor primo `≤ x`. -/
theorem exists_prime_dvd_of_composite_right {x m : ℕ} (hx : 2 ≤ x)
    (hlo : x ^ 2 < m) (hhi : m < x * (x + 1)) (hnp : ¬ m.Prime) :
    ∃ p, p.Prime ∧ p ≤ x ∧ p ∣ m := by
  have hpos : 0 < m := Nat.zero_lt_of_lt hlo
  have hx4 : 4 ≤ x ^ 2 := by nlinarith
  have hm1 : m ≠ 1 := by omega
  refine ⟨m.minFac, minFac_prime hm1, ?_, minFac_dvd m⟩
  have hbound : m < (x + 1) ^ 2 := hhi.trans pronic_lt_succ_sq
  have hsqrt : m.sqrt < x + 1 := sqrt_lt'.mpr hbound
  have hle : m.minFac ≤ m.sqrt := le_sqrt'.2 (minFac_sq_le_self hpos hnp)
  omega

/-- Lado derecho: hay un primo en `(x², x(x+1))` syss algún `m` del intervalo tiene `minFac > x`. -/
theorem oppermann_right_iff_minFac {x : ℕ} (hx : 2 ≤ x) :
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) ↔
      ∃ m, x ^ 2 < m ∧ m < x * (x + 1) ∧ x < m.minFac := by
  constructor
  · intro ⟨p, hp₁, hp₂, hpp⟩
    refine ⟨p, hp₁, hp₂, ?_⟩
    rw [hpp.minFac_eq]
    have hx1 : 1 < x := lt_of_lt_of_le one_lt_two hx
    have : x < x ^ 2 := by
      rw [pow_two]
      simpa using Nat.mul_lt_mul_of_pos_right hx1 (Nat.zero_lt_of_lt hx1)
    omega
  · intro ⟨m, hm₁, hm₂, hfac⟩
    have hm : 1 < m := by
      have : 4 ≤ x ^ 2 := by nlinarith
      omega
    exact ⟨m, hm₁, hm₂, prime_of_minFac_gt_of_lt_succ_sq hm (hm₂.trans pronic_lt_succ_sq) hfac⟩

/-- Lado izquierdo: hay un primo en `(x(x−1), x²)` syss algún `m` del intervalo tiene `minFac ≥ x`. -/
theorem oppermann_left_iff_minFac {x : ℕ} (hx : 2 ≤ x) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ↔
      ∃ m, x * (x - 1) < m ∧ m < x ^ 2 ∧ x ≤ m.minFac := by
  constructor
  · intro ⟨p, hp₁, hp₂, hpp⟩
    refine ⟨p, hp₁, hp₂, ?_⟩
    rw [hpp.minFac_eq]
    have : x ≤ x * (x - 1) :=
      Nat.le_mul_of_pos_right x (by omega)
    omega
  · intro ⟨m, hm₁, hm₂, hfac⟩
    have hm : 1 < m := by
      have : 2 ≤ x * (x - 1) := by
        have : 1 ≤ x - 1 := by omega
        exact Nat.mul_le_mul hx this
      omega
    exact ⟨m, hm₁, hm₂, prime_of_minFac_ge_of_lt_sq hm hm₂ hfac⟩

/-- Si `1 < m`, entonces `x < minFac m` ↔ `m` es coprimo a `x#`. -/
theorem minFac_gt_iff_coprime_primorial {x m : ℕ} (hm : 1 < m) :
    x < m.minFac ↔ Coprime m (primorial x) := by
  constructor
  · intro h
    by_contra hnc
    obtain ⟨p, hp, hpm, hpP⟩ := (Prime.not_coprime_iff_dvd (m := m) (n := primorial x)).1 hnc
    have hp_le : p ≤ x := hp.dvd_primorial_iff.1 hpP
    have hmin : m.minFac ≤ p := minFac_le_of_dvd hp.two_le hpm
    omega
  · intro hcop
    by_contra! hle
    have hpf : (m.minFac).Prime := minFac_prime (Nat.ne_of_gt hm)
    have : ¬ Coprime m (primorial x) :=
      Nat.not_coprime_of_dvd_of_dvd hpf.one_lt (minFac_dvd m)
        (hpf.dvd_primorial_iff.2 hle)
    exact this hcop

/-- Si `1 < m`, entonces `x ≤ minFac m` ↔ `m` es coprimo a `(x − 1)#`. -/
theorem minFac_ge_iff_coprime_primorial_pred {x m : ℕ} (hx : 1 ≤ x) (hm : 1 < m) :
    x ≤ m.minFac ↔ Coprime m (primorial (x - 1)) := by
  have hiff := minFac_gt_iff_coprime_primorial (x := x - 1) hm
  have : x - 1 < m.minFac ↔ x ≤ m.minFac := by omega
  rwa [← this]

/-- Lado derecho vía criba: primo en `(x², x(x+1))` syss algún `m` es coprimo a `x#`. -/
theorem oppermann_right_iff_coprime_primorial {x : ℕ} (hx : 2 ≤ x) :
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) ↔
      ∃ m, x ^ 2 < m ∧ m < x * (x + 1) ∧ Coprime m (primorial x) := by
  rw [oppermann_right_iff_minFac hx]
  constructor
  · intro ⟨m, hm₁, hm₂, hfac⟩
    have hm : 1 < m := by
      have : 4 ≤ x ^ 2 := by nlinarith
      omega
    exact ⟨m, hm₁, hm₂, (minFac_gt_iff_coprime_primorial hm).1 hfac⟩
  · intro ⟨m, hm₁, hm₂, hcop⟩
    have hm : 1 < m := by
      have : 4 ≤ x ^ 2 := by nlinarith
      omega
    exact ⟨m, hm₁, hm₂, (minFac_gt_iff_coprime_primorial hm).2 hcop⟩

/-- Lado izquierdo vía criba: primo en `(x(x−1), x²)` syss algún `m` es coprimo a `(x−1)#`. -/
theorem oppermann_left_iff_coprime_primorial {x : ℕ} (hx : 2 ≤ x) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ↔
      ∃ m, x * (x - 1) < m ∧ m < x ^ 2 ∧ Coprime m (primorial (x - 1)) := by
  rw [oppermann_left_iff_minFac hx]
  constructor
  · intro ⟨m, hm₁, hm₂, hfac⟩
    have hm : 1 < m := by
      have : 2 ≤ x * (x - 1) := by
        have : 1 ≤ x - 1 := by omega
        exact Nat.mul_le_mul hx this
      omega
    exact ⟨m, hm₁, hm₂,
      (minFac_ge_iff_coprime_primorial_pred (by omega) hm).1 hfac⟩
  · intro ⟨m, hm₁, hm₂, hcop⟩
    have hm : 1 < m := by
      have : 2 ≤ x * (x - 1) := by
        have : 1 ≤ x - 1 := by omega
        exact Nat.mul_le_mul hx this
      omega
    exact ⟨m, hm₁, hm₂,
      (minFac_ge_iff_coprime_primorial_pred (by omega) hm).2 hcop⟩

/-- Oppermann para `x` syss ambos intervalos contienen un entero coprimo al primorial adecuado. -/
theorem oppermann_iff_coprime_primorial {x : ℕ} (hx : 2 ≤ x) :
    ((∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
      (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime)) ↔
      (∃ m, x * (x - 1) < m ∧ m < x ^ 2 ∧ Coprime m (primorial (x - 1))) ∧
        ∃ m, x ^ 2 < m ∧ m < x * (x + 1) ∧ Coprime m (primorial x) := by
  constructor
  · intro ⟨hL, hR⟩
    exact ⟨(oppermann_left_iff_coprime_primorial hx).1 hL,
      (oppermann_right_iff_coprime_primorial hx).1 hR⟩
  · intro ⟨hL, hR⟩
    exact ⟨(oppermann_left_iff_coprime_primorial hx).2 hL,
      (oppermann_right_iff_coprime_primorial hx).2 hR⟩

/-! ## Criba de Möbius (reducción del hueco) -/

/-- `∑_{d∣n} μ(d)` vale `1` si `n = 1` y `0` en otro caso. -/
theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℤ) = if n = 1 then (1 : ℤ) else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => (f : ℕ → ℤ) n) moebius_mul_coe_zeta
  -- (μ * ζ) n = 1 n
  change (μ * ζ : ArithmeticFunction ℤ) n = (1 : ArithmeticFunction ℤ) n at h
  rw [coe_mul_zeta_apply, one_apply] at h
  exact h

/-- Indicador de `Coprime m n` como suma de Möbius sobre divisores comunes. -/
theorem sum_moebius_dvd_eq_ite_coprime (m n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (if d ∣ m then (μ d : ℤ) else 0) =
      if Coprime m n then (1 : ℤ) else 0 := by
  classical
  rw [← Finset.sum_filter]
  have hset : n.divisors.filter (· ∣ m) = (Nat.gcd m n).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdn, _⟩, hdm⟩
      exact ⟨⟨hdm, hdn⟩, (Nat.gcd_pos_of_pos_right m (Nat.pos_of_ne_zero hn)).ne'⟩
    · rintro ⟨⟨hdm, hdn⟩, _⟩
      exact ⟨⟨hdn, hn⟩, hdm⟩
  simp [hset, sum_moebius_divisors, coprime_iff_gcd_eq_one]

/-- Múltiplos de `d` en el intervalo abierto `(lo, hi)`. -/
theorem card_dvd_Ioo (lo hi d : ℕ) (_hd : 0 < d) (hhi : 1 ≤ hi) :
    ((Finset.Ioo lo hi).filter (d ∣ ·)).card = (hi - 1) / d - lo / d := by
  have hIoo : Finset.Ioo lo hi = Finset.Ioc lo (hi - 1) := by
    ext m
    simp only [Finset.mem_Ioo, Finset.mem_Ioc]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, Nat.le_sub_one_of_lt h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, Nat.lt_of_le_pred hhi h2⟩⟩
  have h0n := Nat.Ioc_filter_dvd_card_eq_div (hi - 1) d
  have h0lo := Nat.Ioc_filter_dvd_card_eq_div lo d
  classical
  rw [hIoo]
  rcases le_or_gt lo (hi - 1) with hle | hlt
  · have hdisj : Disjoint (Finset.Ioc 0 lo) (Finset.Ioc lo (hi - 1)) :=
      Finset.disjoint_left.2 fun a ha hb => by
        simp only [Finset.mem_Ioc] at ha hb; omega
    have hunion : Finset.Ioc 0 lo ∪ Finset.Ioc lo (hi - 1) = Finset.Ioc 0 (hi - 1) := by
      ext a
      simp only [Finset.mem_union, Finset.mem_Ioc]
      constructor
      · rintro (h | h) <;> omega
      · intro h
        by_cases hap : a ≤ lo
        · left; omega
        · right; omega
    have hdisjf :
        Disjoint ((Finset.Ioc 0 lo).filter (d ∣ ·))
          ((Finset.Ioc lo (hi - 1)).filter (d ∣ ·)) :=
      hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hcard :
        ((Finset.Ioc 0 (hi - 1)).filter (d ∣ ·)).card =
          ((Finset.Ioc 0 lo).filter (d ∣ ·)).card +
            ((Finset.Ioc lo (hi - 1)).filter (d ∣ ·)).card := by
      rw [← hunion, Finset.filter_union, Finset.card_union_of_disjoint hdisjf]
    rw [h0n, h0lo] at hcard
    omega
  · have hempty : Finset.Ioc lo (hi - 1) = ∅ := Finset.Ioc_eq_empty_of_le (le_of_lt hlt)
    simp [hempty]
    have : (hi - 1) / d ≤ lo / d := Nat.div_le_div_right (Nat.le_of_lt hlt)
    omega

/-- Conteo de coprimos en `(lo, hi)` vía Möbius. -/
theorem card_coprime_Ioo_eq_moebius_sum (lo hi n : ℕ) (hn : n ≠ 0) (_hhi : 1 ≤ hi) :
    (((Finset.Ioo lo hi).filter (fun m => Coprime m n)).card : ℤ) =
      ∑ d ∈ n.divisors,
        μ d * (((Finset.Ioo lo hi).filter (d ∣ ·)).card : ℤ) := by
  classical
  have hsum :
      (((Finset.Ioo lo hi).filter (fun m => Coprime m n)).card : ℤ) =
        ∑ m ∈ Finset.Ioo lo hi,
          ∑ d ∈ n.divisors, (if d ∣ m then (μ d : ℤ) else 0) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [sum_moebius_dvd_eq_ite_coprime m n hn]
    split_ifs <;> simp
  rw [hsum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hterm :
      ∀ m, (if d ∣ m then (μ d : ℤ) else 0) =
        μ d * (if d ∣ m then (1 : ℤ) else 0) := by
    intro m; split_ifs <;> ring
  simp_rw [hterm, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_boole, Finset.card_filter]

theorem card_coprime_Ioo_eq_moebius_quotients (lo hi n : ℕ) (hn : n ≠ 0) (hhi : 1 ≤ hi) :
    (((Finset.Ioo lo hi).filter (fun m => Coprime m n)).card : ℤ) =
      ∑ d ∈ n.divisors, μ d * (((hi - 1) / d - lo / d : ℕ) : ℤ) := by
  rw [card_coprime_Ioo_eq_moebius_sum lo hi n hn hhi]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [card_dvd_Ioo lo hi d (Nat.pos_of_mem_divisors hd) hhi]

/-- Lado derecho de Oppermann ↔ suma de Möbius positiva sobre divisores de `x#`. -/
theorem oppermann_right_iff_moebius_pos {x : ℕ} (hx : 2 ≤ x) :
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) ↔
      0 < ∑ d ∈ (primorial x).divisors,
          μ d * ((((x * (x + 1) - 1) / d - x ^ 2 / d) : ℕ) : ℤ) := by
  have hhi : 1 ≤ x * (x + 1) := by
    have : 1 ≤ x := le_trans (by decide : 1 ≤ 2) hx
    exact Nat.mul_le_mul this (Nat.succ_le_succ (Nat.zero_le _))
  have hP : primorial x ≠ 0 := (primorial_pos x).ne'
  rw [oppermann_right_iff_coprime_primorial hx]
  constructor
  · intro ⟨m, hm₁, hm₂, hcop⟩
    have hmem :
        m ∈ (Finset.Ioo (x ^ 2) (x * (x + 1))).filter
          (fun t => Coprime t (primorial x)) := by
      exact Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨hm₁, hm₂⟩, hcop⟩
    have hpos :
        0 < ((Finset.Ioo (x ^ 2) (x * (x + 1))).filter
          (fun t => Coprime t (primorial x))).card :=
      Finset.card_pos.2 ⟨m, hmem⟩
    have heq :=
      card_coprime_Ioo_eq_moebius_quotients (x ^ 2) (x * (x + 1)) (primorial x) hP hhi
    exact heq ▸ Int.natCast_pos.2 hpos
  · intro hsum
    have heq :=
      card_coprime_Ioo_eq_moebius_quotients (x ^ 2) (x * (x + 1)) (primorial x) hP hhi
    have hcard :
        0 < ((Finset.Ioo (x ^ 2) (x * (x + 1))).filter
          (fun t => Coprime t (primorial x))).card := by
      have : 0 <
          (((Finset.Ioo (x ^ 2) (x * (x + 1))).filter
            (fun t => Coprime t (primorial x))).card : ℤ) := by
        rwa [heq]
      exact Int.natCast_pos.1 this
    obtain ⟨m, hm⟩ := Finset.card_pos.1 hcard
    simp only [Finset.mem_filter, Finset.mem_Ioo] at hm
    exact ⟨m, hm.1.1, hm.1.2, hm.2⟩

/-- Lado izquierdo de Oppermann ↔ suma de Möbius positiva sobre divisores de `(x−1)#`. -/
theorem oppermann_left_iff_moebius_pos {x : ℕ} (hx : 2 ≤ x) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ↔
      0 < ∑ d ∈ (primorial (x - 1)).divisors,
          μ d * ((((x ^ 2 - 1) / d - (x * (x - 1)) / d) : ℕ) : ℤ) := by
  have hhi : 1 ≤ x ^ 2 := by
    have : 1 ≤ x := le_trans (by decide : 1 ≤ 2) hx
    exact Nat.pow_le_pow_left this 2
  have hP : primorial (x - 1) ≠ 0 := (primorial_pos (x - 1)).ne'
  rw [oppermann_left_iff_coprime_primorial hx]
  constructor
  · intro ⟨m, hm₁, hm₂, hcop⟩
    have hmem :
        m ∈ (Finset.Ioo (x * (x - 1)) (x ^ 2)).filter
          (fun t => Coprime t (primorial (x - 1))) :=
      Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨hm₁, hm₂⟩, hcop⟩
    have hpos :
        0 < ((Finset.Ioo (x * (x - 1)) (x ^ 2)).filter
          (fun t => Coprime t (primorial (x - 1)))).card :=
      Finset.card_pos.2 ⟨m, hmem⟩
    have heq :=
      card_coprime_Ioo_eq_moebius_quotients (x * (x - 1)) (x ^ 2)
        (primorial (x - 1)) hP hhi
    exact heq ▸ Int.natCast_pos.2 hpos
  · intro hsum
    have heq :=
      card_coprime_Ioo_eq_moebius_quotients (x * (x - 1)) (x ^ 2)
        (primorial (x - 1)) hP hhi
    have hcard :
        0 < ((Finset.Ioo (x * (x - 1)) (x ^ 2)).filter
          (fun t => Coprime t (primorial (x - 1)))).card := by
      have : 0 <
          (((Finset.Ioo (x * (x - 1)) (x ^ 2)).filter
            (fun t => Coprime t (primorial (x - 1)))).card : ℤ) := by
        rwa [heq]
      exact Int.natCast_pos.1 this
    obtain ⟨m, hm⟩ := Finset.card_pos.1 hcard
    simp only [Finset.mem_filter, Finset.mem_Ioo] at hm
    exact ⟨m, hm.1.1, hm.1.2, hm.2⟩

/--
Cota tipo Jacobsthal: si todo intervalo abierto de longitud `x` contiene un entero
coprimo a `x#`, el lado derecho de Oppermann vale (tomar el intervalo `(x², x²+x)`).
-/
theorem oppermann_right_of_jacobsthal {x : ℕ} (hx : 2 ≤ x)
    (h : ∀ a, ∃ m, a < m ∧ m < a + x ∧ Coprime m (primorial x)) :
    ∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime := by
  obtain ⟨m, hm₁, hm₂, hcop⟩ := h (x ^ 2)
  have hhi : m < x * (x + 1) := by
    rw [(oppermann_interval_eq (x := x)).2]
    exact hm₂
  exact (oppermann_right_iff_coprime_primorial hx).2 ⟨m, hm₁, hhi, hcop⟩

/--
Cota tipo Jacobsthal a la izquierda: si todo intervalo abierto de longitud `x` contiene
un entero coprimo a `(x−1)#`, el lado izquierdo de Oppermann vale.
-/
theorem oppermann_left_of_jacobsthal {x : ℕ} (hx : 2 ≤ x)
    (h : ∀ a, ∃ m, a < m ∧ m < a + x ∧ Coprime m (primorial (x - 1))) :
    ∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime := by
  obtain ⟨m, hm₁, hm₂, hcop⟩ := h (x * (x - 1))
  have hadd : x * (x - 1) + x = x ^ 2 := by
    have hL := (oppermann_interval_eq (x := x)).1
    have : x ≤ x * x := Nat.le_mul_of_pos_left x (by omega)
    rw [hL, pow_two]
    omega
  have hhi : m < x ^ 2 := by
    rw [← hadd]
    exact hm₂
  exact (oppermann_left_iff_coprime_primorial hx).2 ⟨m, hm₁, hhi, hcop⟩

/-- Oppermann sigue de cotas Jacobsthal uniformes `j(x#) ≤ x` y `j((x−1)#) ≤ x`. -/
theorem oppermann_of_jacobsthal {x : ℕ} (hx : 2 ≤ x)
    (hL : ∀ a, ∃ m, a < m ∧ m < a + x ∧ Coprime m (primorial (x - 1)))
    (hR : ∀ a, ∃ m, a < m ∧ m < a + x ∧ Coprime m (primorial x)) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  ⟨oppermann_left_of_jacobsthal hx hL, oppermann_right_of_jacobsthal hx hR⟩

/--
Forma clásica (Wikipedia): Oppermann vale para `x` si y solo si
`π(x(x−1)) < π(x²) < π(x(x+1))`.
-/
theorem oppermann_iff_pi {x : ℕ} (hx : 2 ≤ x) :
    ((∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
      (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime)) ↔
      π (x * (x - 1)) < π (x ^ 2) ∧ π (x ^ 2) < π (x * (x + 1)) := by
  have hx0 : x ≠ 0 := by omega
  have hsq_pos : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
  have hpronic_pos : x * (x + 1) ≠ 0 := mul_ne_zero hx0 (by omega)
  have hsq1 : 1 ≤ x ^ 2 := Nat.one_le_iff_ne_zero.2 hsq_pos
  have hpr1 : 1 ≤ x * (x + 1) := Nat.one_le_iff_ne_zero.2 hpronic_pos
  have hleft := exists_prime_Ioo_iff_pi (lo := x * (x - 1)) (hi := x ^ 2) hsq1
  have hright := exists_prime_Ioo_iff_pi (lo := x ^ 2) (hi := x * (x + 1)) hpr1
  have hπsq : π (x ^ 2 - 1) = π (x ^ 2) := by
    simpa [Nat.pred_eq_sub_one] using
      primeCounting_pred_of_not_prime hsq_pos (not_prime_sq hx)
  have hπpr : π (x * (x + 1) - 1) = π (x * (x + 1)) := by
    simpa [Nat.pred_eq_sub_one] using
      primeCounting_pred_of_not_prime hpronic_pos (not_prime_pronic hx)
  rw [hleft, hright, hπsq, hπpr]

/-! ## Verificación finita -/

/-- Test booleano de Oppermann para un `x` fijo (solo impares: los intervalos tienen `lo ≥ 2`). -/
def oppermannHolds (x : ℕ) : Bool :=
  hasOddPrimeInIoo (x * (x - 1)) (x ^ 2) &&
    hasOddPrimeInIoo (x ^ 2) (x * (x + 1))

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
  have hlo₁ : 2 ≤ x * (x - 1) := by
    have : 1 ≤ x - 1 := by omega
    exact Nat.mul_le_mul hx this
  have hlo₂ : 2 ≤ x ^ 2 := by nlinarith
  simp only [oppermannHolds, Bool.and_eq_true, hasOddPrimeInIoo_iff hlo₁ h₁,
    hasOddPrimeInIoo_iff hlo₂ h₂]

/-- Oppermann vale para todo `2 ≤ x ≤ 50000`. -/
private theorem oppermann_bool_upto_50000 :
    (List.range' 2 49999).all oppermannHolds = true := by
  native_decide

theorem oppermann_upto_50000 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 50000) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) := by
  have hmem : x ∈ List.range' 2 49999 := by
    rw [List.mem_range'_1]
    exact ⟨hx₂, by omega⟩
  have hbool : oppermannHolds x = true :=
    (List.all_eq_true.1 oppermann_bool_upto_50000) x hmem
  exact (oppermannHolds_iff hx₂).1 hbool

theorem oppermann_upto_30000 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 30000) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_50000 hx₂ (by omega)

theorem oppermann_upto_20000 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 20000) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_30000 hx₂ (by omega)

theorem oppermann_upto_10000 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 10000) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_20000 hx₂ (by omega)

theorem oppermann_upto_2000 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 2000) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_20000 hx₂ (by omega)

theorem oppermann_upto_500 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 500) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_20000 hx₂ (by omega)

theorem oppermann_upto_200 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 200) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_20000 hx₂ (by omega)

theorem oppermann_upto_100 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 100) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_20000 hx₂ (by omega)

theorem oppermann_upto_50 {x : ℕ} (hx₂ : 2 ≤ x) (hx : x ≤ 50) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  oppermann_upto_20000 hx₂ (by omega)

/-- Forma π para `x = 2`: `π(2) < π(4) < π(6)`. -/
theorem oppermann_two_pi :
    π (2 * (2 - 1)) < π (2 ^ 2) ∧ π (2 ^ 2) < π (2 * (2 + 1)) := by
  decide

/-- Forma π para `x = 3`: `π(6) < π(9) < π(12)`. -/
theorem oppermann_three_pi :
    π (3 * (3 - 1)) < π (3 ^ 2) ∧ π (3 ^ 2) < π (3 * (3 + 1)) := by
  decide

/-- Primer caso a mano, vía crecimiento de `π`. -/
theorem oppermann_two_explicit :
    (∃ p, 2 * (2 - 1) < p ∧ p < 2 ^ 2 ∧ p.Prime) ∧
    (∃ p, 2 ^ 2 < p ∧ p < 2 * (2 + 1) ∧ p.Prime) :=
  (oppermann_iff_pi (by decide)).2 oppermann_two_pi

/-- Segundo caso a mano, vía crecimiento de `π`. -/
theorem oppermann_three_explicit :
    (∃ p, 3 * (3 - 1) < p ∧ p < 3 ^ 2 ∧ p.Prime) ∧
    (∃ p, 3 ^ 2 < p ∧ p < 3 * (3 + 1) ∧ p.Prime) :=
  (oppermann_iff_pi (by decide)).2 oppermann_three_pi

/-! ## Lo que sí se deduce de Mathlib (Bertrand) y lo que no -/

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
Si `π` crece en ambos intervalos de Oppermann, la conjetura vale para ese `x`.
Este es el único input analítico que falta para `x` grande.
-/
theorem oppermann_of_pi {x : ℕ} (hx : 2 ≤ x)
    (h : π (x * (x - 1)) < π (x ^ 2) ∧ π (x ^ 2) < π (x * (x + 1))) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  (oppermann_iff_pi hx).2 h

/--
Oppermann para `x` grande sigue de las sumas de Möbius positivas sobre `(x−1)#` y `x#`.
Las cotas de Jacobsthal (`j(n) = O(log² n)`, Iwaniec) no implican `j((x−1)#) ≤ x` (falla ya
para `x ≈ 12`). Axler (2014) da primos en `(n, n(1 + 198.2/log⁴ n)]` para `n > 1`; eso cubre
Oppermann analíticamente solo para `x` muy grande (`x ≳ 16 log⁴ x`). Ferreira (arXiv:2307.08725)
da el crecimiento asintótico en intervalos cortos pero no está en Mathlib.
-/
theorem oppermann_of_moebius_pos {x : ℕ} (hx : 2 ≤ x)
    (hL : 0 < ∑ d ∈ (primorial (x - 1)).divisors,
        μ d * ((((x ^ 2 - 1) / d - (x * (x - 1)) / d) : ℕ) : ℤ))
    (hR : 0 < ∑ d ∈ (primorial x).divisors,
        μ d * ((((x * (x + 1) - 1) / d - x ^ 2 / d) : ℕ) : ℤ)) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) :=
  ⟨((oppermann_left_iff_moebius_pos hx).2 hL),
    ((oppermann_right_iff_moebius_pos hx).2 hR)⟩

/-! ## Conjetura de Oppermann -/

/--
**Conjetura de Oppermann (abierta).**
Para todo `x ≥ 2` hay un primo en `(x(x−1), x²)` y otro en `(x², x(x+1))`.
Los casos `2 ≤ x ≤ 50000` están demostrados. Equivalencias sorry-free:
`oppermann_iff_pi`, `oppermann_iff_primorial`, `oppermann_of_sqrt_window`,
`oppermann_left_iff_minFac`, `oppermann_right_iff_minFac`,
`oppermann_left_iff_coprime_primorial`, `oppermann_right_iff_coprime_primorial`,
`oppermann_left_iff_moebius_pos`, `oppermann_right_iff_moebius_pos`.
Suficiente (más fuerte): `oppermann_of_jacobsthal`. Bertrand no basta
(`bertrand_remainder_nonempty`). Corolarios condicionales:
`oppermann_implies_legendre`, `oppermann_implies_brocard`.
-/
theorem oppermann_conjecture (x : ℕ) (hx : 2 ≤ x) :
    (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
    (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime) := by
  by_cases hle : x ≤ 50000
  · exact oppermann_upto_50000 hx hle
  · exact oppermann_of_moebius_pos hx (by sorry) (by sorry)

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

/-- Oppermann implica Brocard: hay al menos 4 primos entre cuadrados de primos consecutivos. -/
theorem oppermann_implies_brocard
    (hOpp : ∀ x, 2 ≤ x →
      (∃ p, x * (x - 1) < p ∧ p < x ^ 2 ∧ p.Prime) ∧
      (∃ p, x ^ 2 < p ∧ p < x * (x + 1) ∧ p.Prime))
    (n : ℕ) (hn : 1 ≤ n) :
    4 ≤ ((Finset.Ioo ((n.nth Nat.Prime) ^ 2) (((n + 1).nth Nat.Prime) ^ 2)).filter Nat.Prime).card := by
  set prev := n.nth Nat.Prime
  set next := (n + 1).nth Nat.Prime
  have hprev_prime : prev.Prime := Nat.prime_nth_prime n
  have hnext_prime : next.Prime := Nat.prime_nth_prime (n + 1)
  have hprev_ge : 3 ≤ prev :=
    Nat.nth_prime_one_eq_three ▸ (Nat.nth_le_nth Nat.infinite_setOf_prime).mpr hn
  have hlt : prev < next :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self n)
  have hgap : prev + 2 ≤ next := by
    have hodd_prev : Odd prev :=
      hprev_prime.odd_of_ne_two
        (Nat.ne_of_gt (lt_of_lt_of_le (by decide : (2 : ℕ) < 3) hprev_ge))
    have hodd_next : Odd next :=
      hnext_prime.odd_of_ne_two
        (Nat.ne_of_gt (lt_of_lt_of_le (by decide : (2 : ℕ) < 3)
          (hprev_ge.trans (le_of_lt hlt))))
    rcases hodd_prev with ⟨k, hk⟩
    rcases hodd_next with ⟨m, hm⟩
    omega
  obtain ⟨_, ⟨p1, hp1₁, hp1₂, hp1p⟩⟩ := hOpp prev (by omega)
  obtain ⟨⟨p2, hp2₁, hp2₂, hp2p⟩, ⟨p3, hp3₁, hp3₂, hp3p⟩⟩ := hOpp (prev + 1) (by omega)
  obtain ⟨⟨p4, hp4₁, hp4₂, hp4p⟩, _⟩ := hOpp (prev + 2) (by omega)
  have hb0 : prev * (prev + 1) < (prev + 1) ^ 2 := by nlinarith
  have hb1 : (prev + 1) * (prev + 2) < (prev + 2) ^ 2 := by nlinarith
  have hsq : (prev + 2) ^ 2 ≤ next ^ 2 := Nat.pow_le_pow_left hgap 2
  have hmul : (prev + 1) * ((prev + 1) - 1) = prev * (prev + 1) := by
    rw [Nat.add_one_sub_one, Nat.mul_comm]
  have hmul2 : (prev + 2) * ((prev + 2) - 1) = (prev + 1) * (prev + 2) := by
    rw [show (prev + 2) - 1 = prev + 1 by omega, Nat.mul_comm]
  rw [hmul] at hp2₁
  rw [hmul2] at hp4₁
  have h12 : p1 < p2 := by linarith
  have h23 : p2 < p3 := by linarith
  have h34 : p3 < p4 := by linarith
  refine le_trans (b := ({p1, p2, p3, p4} : Finset ℕ).card) ?_ ?_
  · simp [Finset.card_insert_of_notMem, h12.ne, (h12.trans h23).ne,
      (h12.trans (h23.trans h34)).ne, h23.ne, (h23.trans h34).ne, h34.ne]
  · apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hp1₁, by linarith [hp4₂, hsq]⟩, hp1p⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by linarith [hp1₁], by linarith [hp4₂, hsq]⟩, hp2p⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by linarith [hp1₁], by linarith [hp4₂, hsq]⟩, hp3p⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by linarith [hp1₁], by linarith [hp4₂, hsq]⟩, hp4p⟩

/-- Legendre para todo `n ≤ 49999`, como corolario de Oppermann hasta `50000`. -/
theorem legendre_upto_49999 {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 49999) :
    ∃ p, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime := by
  obtain ⟨⟨p, hp₁, hp₂, hpp⟩, _⟩ :=
    oppermann_upto_50000 (x := n + 1) (by omega) (by omega)
  refine ⟨p, ?_, hp₂, hpp⟩
  have hmul : (n + 1) * ((n + 1) - 1) = n * (n + 1) := by
    rw [Nat.add_one_sub_one, Nat.mul_comm]
  rw [hmul] at hp₁
  have hsq : n ^ 2 ≤ n * (n + 1) := by
    rw [Nat.mul_add, Nat.mul_one, pow_two]
    omega
  omega

/-- Legendre para todo `n ≤ 29999`, como corolario de Oppermann hasta `30000`. -/
theorem legendre_upto_29999 {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 29999) :
    ∃ p, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime :=
  legendre_upto_49999 hn (by omega)

/-- Legendre para todo `n ≤ 19999`, como corolario de Oppermann hasta `20000`. -/
theorem legendre_upto_19999 {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 19999) :
    ∃ p, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime :=
  legendre_upto_29999 hn (by omega)

/-- Legendre para todo `n ≤ 9999`, como corolario de Oppermann hasta `10000`. -/
theorem legendre_upto_9999 {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 9999) :
    ∃ p, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime :=
  legendre_upto_19999 hn (by omega)

/--
**Conjetura de Legendre (abierta).**
Para todo `n ≥ 1` hay un primo estrictamente entre `n²` y `(n+1)²`.
Sigue de Oppermann por `oppermann_implies_legendre`.
-/
theorem legendre_conjecture (n : ℕ) (hn : 1 ≤ n) :
    ∃ p, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime :=
  oppermann_implies_legendre oppermann_conjecture n hn

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
