/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Points

/-!
# Collinearity of Tate coordinates

The rational parametrization of the nodal cubic gives a collinearity identity
when three parameters have product one. Summing it over pairs of integers, with
third exponent the negative of their sum, gives the Tate collinearity identity.
The three changes of indices are bijections of `ℤ × ℤ`.
-/

@[expose] public section

open ValuativeRel

namespace TateCurve

section Algebra

variable {K : Type*} [Field K]

/-- The nodal cubic's rational coordinates are collinear when the parameters multiply to one. -/
private theorem nodal_collinear {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha1 : 1 - a ≠ 0) (hb1 : 1 - b ≠ 0) (hc1 : 1 - c ≠ 0)
    (habc : a * b * c = 1) :
    xTerm a * yTerm b - yTerm a * xTerm b +
      (xTerm b * yTerm c - yTerm b * xTerm c) +
      (xTerm c * yTerm a - yTerm c * xTerm a) = 0 := by
  have hc : c = (a * b)⁻¹ := by
    apply mul_left_cancel₀ (mul_ne_zero ha hb)
    rw [habc, mul_inv_cancel₀ (mul_ne_zero ha hb)]
  subst c
  have hab1 : 1 - a * b ≠ 0 := by
    intro h
    have hab := (sub_eq_zero.mp h).symm
    simp [hab] at hc1
  rw [xTerm_inv (mul_ne_zero ha hb), yTerm_inv_eq (mul_ne_zero ha hb)]
  unfold xTerm yTerm
  field_simp [ha1, hb1, hab1]
  ring

end Algebra

/-- Cycling the three exponents whose sum is zero is a bijection of pairs of integers. -/
private def cycleExponents : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, -p.1 - p.2)
  invFun p := (-p.1 - p.2, p.1)
  left_inv p := Prod.ext (by dsimp; omega) rfl
  right_inv p := Prod.ext rfl (by dsimp; omega)

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

set_option maxHeartbeats 800000 in
-- The six products of infinite sums and their reindexings exceed the default elaboration budget.
/-- Tate coordinates of three nonidentity classes with product one are collinear. -/
theorem tateCoordinates_collinear (q : Kˣ) (hq : valuation K (q : K) < 1)
    (u v w : Kˣ) (hu : u ∉ Subgroup.zpowers q) (hv : v ∉ Subgroup.zpowers q)
    (hw : w ∉ Subgroup.zpowers q) (huvw : u * v * w = 1) :
    tateX (u : K) (q : K) * tateY (v : K) (q : K) -
        tateY (u : K) (q : K) * tateX (v : K) (q : K) +
      (tateX (v : K) (q : K) * tateY (w : K) (q : K) -
        tateY (v : K) (q : K) * tateX (w : K) (q : K)) +
      (tateX (w : K) (q : K) * tateY (u : K) (q : K) -
        tateY (w : K) (q : K) * tateX (u : K) (q : K)) = 0 := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let X (a : Kˣ) := ∑' n : ℤ, xTerm ((q : K) ^ n * (a : K))
  let Y (a : Kˣ) := ∑' n : ℤ, yTerm ((q : K) ^ n * (a : K))
  let cross (a b : Kˣ) (p : ℤ × ℤ) :=
    xTerm ((q : K) ^ p.1 * (a : K)) * yTerm ((q : K) ^ p.2 * (b : K)) -
      yTerm ((q : K) ^ p.1 * (a : K)) * xTerm ((q : K) ^ p.2 * (b : K))
  have hX (a : Kˣ) : HasSum (fun n : ℤ ↦ xTerm ((q : K) ^ n * (a : K))) (X a) :=
    (summable_tate_x_of_valuation_lt_one q.ne_zero a.ne_zero hq).hasSum
  have hY (a : Kˣ) : HasSum (fun n : ℤ ↦ yTerm ((q : K) ^ n * (a : K))) (Y a) :=
    (summable_tate_y_of_valuation_lt_one q.ne_zero a.ne_zero hq).hasSum
  have hcross (a b : Kˣ) : HasSum (cross a b) (X a * Y b - Y a * X b) :=
    ((hX a).mul_of_nonarchimedean (hY b)).sub ((hY a).mul_of_nonarchimedean (hX b))
  have hs := ((hcross u v).add (cycleExponents.hasSum_iff.mpr (hcross v w))).add
    (cycleExponents.symm.hasSum_iff.mpr (hcross w u))
  have hzero (p : ℤ × ℤ) : cross u v p + cross v w (cycleExponents p) +
      cross w u (cycleExponents.symm p) = 0 := by
    apply nodal_collinear
      (mul_ne_zero (zpow_ne_zero _ q.ne_zero) u.ne_zero)
      (mul_ne_zero (zpow_ne_zero _ q.ne_zero) v.ne_zero)
      (one_sub_zpow_mul_ne_zero q u hu p.1)
      (one_sub_zpow_mul_ne_zero q v hv p.2)
      (one_sub_zpow_mul_ne_zero q w hw (-p.1 - p.2))
    calc
      (q : K) ^ p.1 * (u : K) * ((q : K) ^ p.2 * (v : K)) *
          ((q : K) ^ (-p.1 - p.2) * (w : K)) =
          ((q : K) ^ p.1 * (q : K) ^ p.2 * (q : K) ^ (-p.1 - p.2)) *
            ((u : K) * (v : K) * (w : K)) := by ring
      _ = 1 := by
        rw [← zpow_add₀ q.ne_zero, ← zpow_add₀ q.ne_zero,
          show p.1 + p.2 + (-p.1 - p.2) = 0 by ring, zpow_zero, one_mul]
        exact congrArg Units.val huvw
  have hdet : X u * Y v - Y u * X v + (X v * Y w - Y v * X w) +
      (X w * Y u - Y w * X u) = 0 := by
    have hs0 : HasSum (fun _ : ℤ × ℤ ↦ (0 : K))
        (X u * Y v - Y u * X v + (X v * Y w - Y v * X w) +
          (X w * Y u - Y w * X u)) := hs.congr_fun (fun p ↦ (hzero p).symm)
    exact hs0.unique hasSum_zero
  dsimp [tateX, tateY]
  dsimp [X, Y] at hdet
  linear_combination hdet

end TateCurve
