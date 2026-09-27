/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange
public import FLT.TateCurve.Uniformization

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

end TateCurve
