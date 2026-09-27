/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange
public import FLT.TateCurve.Uniformization
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!+# Tate coordinates over nonarchimedean local fields

The valuation bound `|q| < 1` implies the convergence hypothesis of the coordinate
series. This file also identifies their correction term with the integral power
series `sInt 1` used in the formal Tate construction.
-/

@[expose] public section

open ValuativeRel
open scoped Topology

namespace TateCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The Tate `x`-coordinate series converges for a local-field Tate parameter. -/
theorem summable_tate_x_of_valuation_lt_one {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq : valuation K q < 1) : Summable (fun n : ℤ ↦ xTerm (q ^ n * u)) := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  exact summable_tate_x hq0 hu0 (tendsto_pow_nhds_zero hq)

/-- The Tate `y`-coordinate series converges for a local-field Tate parameter. -/
theorem summable_tate_y_of_valuation_lt_one {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq : valuation K q < 1) : Summable (fun n : ℤ ↦ yTerm (q ^ n * u)) := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  exact summable_tate_y hq0 hu0 (tendsto_pow_nhds_zero hq)

/-- The full geometric series on the open unit disc of a local field. -/
theorem hasSum_geometric_of_valuation_lt_one {q : K} (hq : valuation K q < 1) :
    HasSum (fun n : ℕ ↦ q ^ n) (1 / (1 - q)) := by
  have hq1 : q ≠ 1 := by
    rintro rfl
    simp at hq
  have h := (hasSum_nat_add_iff (f := fun n : ℕ ↦ q ^ n) 1).mp
    (hasSum_geometric_succ hq)
  convert h using 1
  simp only [Finset.sum_range_one, pow_zero]
  field_simp [sub_ne_zero.mpr (Ne.symm hq1)]
  ring

/-- The first weighted geometric series, obtained by multiplying two geometric series. -/
theorem hasSum_nat_mul_geometric_of_valuation_lt_one {q : K} (hq : valuation K q < 1) :
    HasSum (fun n : ℕ ↦ (n : K) * q ^ n) (xTerm q) := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have hg := hasSum_geometric_of_valuation_lt_one hq
  have hp := hg.summable.mul_of_nonarchimedean hg.summable
  have hc : ∀ n : ℕ, (∑ i ∈ Finset.range (n + 1), q ^ i * q ^ (n - i)) =
      ((n + 1 : ℕ) : K) * q ^ n := by
    intro n
    calc (∑ i ∈ Finset.range (n + 1), q ^ i * q ^ (n - i))
        = ∑ _i ∈ Finset.range (n + 1), q ^ n := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
      _ = _ := by simp [nsmul_eq_mul]
  have hs : HasSum (fun n : ℕ ↦ ((n + 1 : ℕ) : K) * q ^ n)
      ((1 / (1 - q)) * (1 / (1 - q))) := by
    have hsum := (summable_sum_mul_range_of_summable_mul hp).hasSum
    rw [← hg.summable.tsum_mul_tsum_eq_tsum_sum_range hg.summable hp, hg.tsum_eq] at hsum
    simpa only [hc] using hsum
  have hshift : HasSum (fun n : ℕ ↦ ((n + 1 : ℕ) : K) * q ^ (n + 1)) (xTerm q) := by
    convert hs.mul_right q using 1
    · funext n
      ring
    · simp only [xTerm, div_eq_mul_inv, ← inv_pow]
      ring
  simpa using (hasSum_nat_add_iff (f := fun n : ℕ ↦ (n : K) * q ^ n) 1).mp hshift

/-- The rational correction series equals the integral power series `s₁`.
The two Lambert expressions agree by interchanging their summable double series. -/
theorem tateCorrection_eq_evalInt {q : K} (hq : valuation K q < 1) :
    tateCorrection q = evalInt q (sInt 1) := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have hpow (n : ℕ) : valuation K (q ^ (n + 1)) < 1 := by
    rw [map_pow]
    exact (pow_le_pow_right_of_le_one' hq.le (Nat.succ_le_succ (Nat.zero_le n))).trans_lt
      (by simpa only [pow_one] using hq)
  have hd : Summable (fun p : ℕ × ℕ ↦ ((p.2 + 1 : ℕ) : K) *
      q ^ ((p.1 + 1) * (p.2 + 1))) := by
    refine summable_of_valuation_le_pow hq (fun p ↦ (p.1 + 1) * (p.2 + 1))
      (fun N ↦ ?_) (fun p ↦ ?_)
    · refine ((Set.finite_Iio N).prod (Set.finite_Iio N)).subset fun p hp ↦ ?_
      have h1 : p.1 < (p.1 + 1) * (p.2 + 1) :=
        (Nat.lt_succ_self _).trans_le (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
      have h2 : p.2 < (p.1 + 1) * (p.2 + 1) :=
        (Nat.lt_succ_self _).trans_le (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      exact ⟨h1.trans hp, h2.trans hp⟩
    · rw [map_mul, map_pow]
      simpa only [one_mul] using mul_le_mul_left (valuation_natCast_le_one (p.2 + 1))
        (valuation K q ^ ((p.1 + 1) * (p.2 + 1)))
  have hrow (n : ℕ) : (∑' m : ℕ, ((m + 1 : ℕ) : K) * q ^ ((n + 1) * (m + 1))) =
      xTerm (q ^ (n + 1)) := by
    have h : HasSum (fun m : ℕ ↦ ((m + 1 : ℕ) : K) * (q ^ (n + 1)) ^ (m + 1))
        (xTerm (q ^ (n + 1))) := by
      apply (hasSum_nat_add_iff (f := fun m : ℕ ↦ (m : K) * (q ^ (n + 1)) ^ m) 1).mpr
      simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, add_zero] using
        hasSum_nat_mul_geometric_of_valuation_lt_one (hpow n)
    simpa only [← pow_mul] using h.tsum_eq
  have hcol (m : ℕ) : (∑' n : ℕ, ((m + 1 : ℕ) : K) * q ^ ((n + 1) * (m + 1))) =
      ((m + 1 : ℕ) : K) * q ^ (m + 1) / (1 - q ^ (m + 1)) := by
    simpa only [← pow_mul, mul_div_assoc, Nat.mul_comm] using
      ((hasSum_geometric_succ (hpow m)).mul_left ((m + 1 : ℕ) : K)).tsum_eq
  have hcoeff : ∀ n, PowerSeries.coeff n (sInt 1) = ∑ d ∈ n.divisors, (d : ℤ) := by
    intro n
    simp only [sInt, PowerSeries.coeff_mk, ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
  calc tateCorrection q
      = ∑' n : ℕ, ∑' m : ℕ, ((m + 1 : ℕ) : K) * q ^ ((n + 1) * (m + 1)) := by
          simp only [tateCorrection, hrow]
    _ = ∑' m : ℕ, ∑' n : ℕ, ((m + 1 : ℕ) : K) * q ^ ((n + 1) * (m + 1)) :=
          (Summable.tsum_comm (f := fun n m : ℕ ↦
            ((m + 1 : ℕ) : K) * q ^ ((n + 1) * (m + 1))) hd).symm
    _ = ∑' m : ℕ, ((m + 1 : ℕ) : K) * q ^ (m + 1) / (1 - q ^ (m + 1)) :=
          tsum_congr hcol
    _ = evalInt q (sInt 1) := by
          simpa only [Int.cast_natCast] using
            tsum_lambert_eq_evalInt q hq (fun n ↦ (n : ℤ)) hcoeff

/-- The binomially weighted geometric series, proved using its integral formal identity.
The argument works in every residue characteristic. -/
theorem hasSum_choose_add_geometric_of_valuation_lt_one {q : K}
    (hq : valuation K q < 1) (d : ℕ) :
    HasSum (fun n : ℕ ↦ ((d + n).choose d : K) * q ^ n) ((1 / (1 - q)) ^ (d + 1)) := by
  have he : evalInt q (PowerSeries.mk (1 : ℕ → ℤ)) = 1 / (1 - q) := by
    simpa [evalInt] using (hasSum_geometric_of_valuation_lt_one hq).tsum_eq
  have hs := (summable_evalInt q hq (PowerSeries.mk fun n ↦ ((d + n).choose d : ℤ))).hasSum
  have hv : evalInt q (PowerSeries.mk fun n ↦ ((d + n).choose d : ℤ)) =
      (1 / (1 - q)) ^ (d + 1) := by
    rw [← PowerSeries.mk_one_pow_eq_mk_choose_add, evalInt_pow q hq, he]
  change HasSum _ (evalInt q (PowerSeries.mk fun n ↦ ((d + n).choose d : ℤ))) at hs
  rw [hv] at hs
  simpa only [PowerSeries.coeff_mk, Int.cast_natCast] using hs

/-- The second binomially weighted geometric series is the rational `y` summand. -/
theorem hasSum_choose_two_geometric_of_valuation_lt_one {q : K}
    (hq : valuation K q < 1) :
    HasSum (fun n : ℕ ↦ (n.choose 2 : K) * q ^ n) (yTerm q) := by
  have h := (hasSum_choose_add_geometric_of_valuation_lt_one hq 2).mul_left (q ^ 2)
  have he : (fun n : ℕ ↦ q ^ 2 * ((2 + n).choose 2 * q ^ n : K)) =
      fun n : ℕ ↦ ((n + 2).choose 2 : K) * q ^ (n + 2) := by
    funext n
    rw [Nat.add_comm 2 n]
    ring
  rw [he] at h
  have hv : q ^ 2 * (1 / (1 - q)) ^ (2 + 1) = yTerm q := by
    simp only [yTerm, div_pow, one_pow]
    ring
  rw [hv] at h
  simpa [Finset.sum_range_succ] using
    (hasSum_nat_add_iff (f := fun n : ℕ ↦ (n.choose 2 : K) * q ^ n) 2).mp h

end TateCurve
