/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCuspParametrization

/-!
# The smooth parameter chart of a split node

For y²+a·xy=x³ with a nonzero, the smooth affine points have the unique
form (r(r+a),r²(r+a)), with r and r+a nonzero. The two omitted parameters
are the tangent directions at the node.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F]

/-- The normalized split nodal Weierstrass equation. -/
def splitNodeCurve (a : F) : WeierstrassCurve F := ⟨a, 0, 0, 0, 0⟩

/-- The equation of a normalized split node. -/
theorem splitNodeCurve_equation_iff (a x y : F) :
    (splitNodeCurve a).toAffine.Equation x y ↔ y * (y + a * x) = x ^ 3 := by
  rw [Affine.equation_iff']
  dsimp [splitNodeCurve, toAffine]
  constructor <;> intro h <;> linear_combination h

/-- A smooth affine point of the normalized node has nonzero x coordinate. -/
theorem splitNodeCurve_x_ne_zero {a x y : F}
    (h : (splitNodeCurve a).toAffine.Nonsingular x y) : x ≠ 0 := by
  intro hx
  have he := (splitNodeCurve_equation_iff a x y).mp h.1
  have hy : y = 0 := by simpa [hx, mul_self_eq_zero] using he
  exact (normalized_nonsingular_iff (splitNodeCurve a) rfl rfl rfl h.1).mp h ⟨hx, hy⟩

/-- Recover the affine coordinates from the line slope y/x. -/
theorem splitNodeCurve_coordinates_slope {a x y : F}
    (h : (splitNodeCurve a).toAffine.Nonsingular x y) :
    y / x * (y / x + a) = x ∧ (y / x) ^ 2 * (y / x + a) = y := by
  have hx := splitNodeCurve_x_ne_zero h
  have he := (splitNodeCurve_equation_iff a x y).mp h.1
  constructor
  · field_simp
    linear_combination he
  · field_simp
    linear_combination y * he

/-- The two nodal tangent directions are excluded from the smooth chart. -/
theorem splitNodeCurve_slope_ne {a x y : F}
    (h : (splitNodeCurve a).toAffine.Nonsingular x y) : y / x ≠ 0 ∧ y / x + a ≠ 0 := by
  have he := (splitNodeCurve_coordinates_slope h).1
  have hx := splitNodeCurve_x_ne_zero h
  exact ⟨fun hz => hx (by simpa [hz] using he.symm),
    fun hz => hx (by simpa [hz] using he.symm)⟩

/-- Every parameter outside the two tangent directions gives a smooth point. -/
theorem splitNodeCurve_nonsingular_param {a r : F} (hr : r ≠ 0) (hra : r + a ≠ 0) :
    (splitNodeCurve a).toAffine.Nonsingular (r * (r + a)) (r ^ 2 * (r + a)) := by
  have he : (splitNodeCurve a).toAffine.Equation (r * (r + a)) (r ^ 2 * (r + a)) := by
    rw [splitNodeCurve_equation_iff]
    ring
  exact (normalized_nonsingular_iff (splitNodeCurve a) rfl rfl rfl he).mpr
    (fun h => (mul_ne_zero hr hra) h.1)

/-- The multiplicative parameter as a field element, with value one at infinity. -/
def splitNodeParameter (a : F) : (splitNodeCurve a).toAffine.Point → F
  | .zero => 1
  | .some x y _ => (y / x) / (y / x + a)

/-- The multiplicative parameter never vanishes on a smooth point. -/
theorem splitNodeParameter_ne_zero (a : F) (P : (splitNodeCurve a).toAffine.Point) :
    splitNodeParameter a P ≠ 0 := by
  cases P with
  | zero => exact one_ne_zero
  | some x y h =>
    exact div_ne_zero (splitNodeCurve_slope_ne h).1 (splitNodeCurve_slope_ne h).2

/-- The normalized node parameter takes values in the units of the field. -/
noncomputable def splitNodeParameterUnit (a : F) (P : (splitNodeCurve a).toAffine.Point) : Fˣ :=
  Units.mk0 (splitNodeParameter a P) (splitNodeParameter_ne_zero a P)

/-- The parameter of an affine smooth chart point is r/(r+a). -/
theorem splitNodeParameter_param {a r : F} (hr : r ≠ 0) (hra : r + a ≠ 0)
    (h : (splitNodeCurve a).toAffine.Nonsingular (r * (r + a)) (r ^ 2 * (r + a))) :
    splitNodeParameter a (.some _ _ h) = r / (r + a) := by
  change _ / (_ + a) = _
  have he : r ^ 2 * (r + a) / (r * (r + a)) = r := by field_simp
  rw [he]

end FLT.Mazur
