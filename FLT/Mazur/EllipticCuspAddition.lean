/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCuspParametrization

/-!
# The additive group law on the smooth cusp

The actual secant and tangent formulas send the parameter x/y of a sum
to the sum of the parameters. The vertical case includes characteristic two.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F]

/-- A nonvertical line between cusp parameters has this slope, also for tangency. -/
theorem cuspCurve_slope {a b : F} (ha : a ≠ 0) (hs : a + b ≠ 0) :
    (cuspCurve F).toAffine.slope (a ^ 2) (b ^ 2) (a ^ 3) (b ^ 3) =
      (a ^ 2 + a * b + b ^ 2) / (a + b) := by
  by_cases hx : a ^ 2 = b ^ 2
  · have hab : a = b := (sq_eq_sq_iff_eq_or_eq_neg.mp hx).resolve_right
      (fun h => hs (by rw [h]; ring))
    subst b
    have hy : a ^ 3 ≠ (cuspCurve F).toAffine.negY (a ^ 2) (a ^ 3) := by
      simp only [Affine.negY, cuspCurve, toAffine, zero_mul, sub_zero]
      intro h
      apply hs
      apply (mul_right_cancel₀ (pow_ne_zero 2 ha))
      linear_combination h
    rw [Affine.slope_of_Y_ne rfl hy]
    simp only [cuspCurve, toAffine, Affine.negY, zero_mul, add_zero, sub_zero, sub_neg_eq_add]
    have hd : a ^ 3 + a ^ 3 ≠ 0 := by
      convert mul_ne_zero hs (pow_ne_zero 2 ha) using 1
      ring
    field_simp
    ring
  · rw [Affine.slope_of_X_ne hx]
    field_simp
    ring

omit [DecidableEq F] in
/-- The nonvertical addition formulas on the cusp simplify to another parametrized point. -/
theorem cuspCurve_add_coordinates {a b : F} (hs : a + b ≠ 0) :
    let l := (a ^ 2 + a * b + b ^ 2) / (a + b)
    (cuspCurve F).toAffine.addX (a ^ 2) (b ^ 2) l = (a * b / (a + b)) ^ 2 ∧
      (cuspCurve F).toAffine.addY (a ^ 2) (b ^ 2) (a ^ 3) l =
        (a * b / (a + b)) ^ 3 := by
  dsimp [Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, cuspCurve, toAffine]
  constructor <;> field_simp <;> ring

/-- The cusp parameter respects addition for affine smooth points. -/
theorem cuspParameter_add_some {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : (cuspCurve F).toAffine.Nonsingular (a ^ 2) (a ^ 3))
    (h₂ : (cuspCurve F).toAffine.Nonsingular (b ^ 2) (b ^ 3)) :
    cuspParameter (.some _ _ h₁ + .some _ _ h₂) = a⁻¹ + b⁻¹ := by
  by_cases hs : a + b = 0
  · have hab : a = -b := eq_neg_of_add_eq_zero_left hs
    rw [Affine.Point.add_of_Y_eq (by rw [hab]; ring) (by
      simp only [Affine.negY, cuspCurve, toAffine, zero_mul, sub_zero, hab]
      ring)]
    simp [cuspParameter, hab]
  · have hxy : ¬ (a ^ 2 = b ^ 2 ∧
        a ^ 3 = (cuspCurve F).toAffine.negY (b ^ 2) (b ^ 3)) := by
      rintro ⟨hx, hy⟩
      have hab : a = b := (sq_eq_sq_iff_eq_or_eq_neg.mp hx).resolve_right
        (fun h => hs (by rw [h]; ring))
      simp only [Affine.negY, cuspCurve, toAffine, zero_mul, sub_zero] at hy
      apply hs
      apply (mul_right_cancel₀ (pow_ne_zero 2 ha))
      rw [← hab] at hy ⊢
      linear_combination hy
    rw [Affine.Point.add_some hxy]
    change (cuspCurve F).toAffine.addX _ _ _ / (cuspCurve F).toAffine.addY _ _ _ _ = _
    rw [cuspCurve_slope ha hs, (cuspCurve_add_coordinates hs).1,
      (cuspCurve_add_coordinates hs).2]
    field_simp
    ring

/-- The parameter x/y is compatible with the existing affine point addition. -/
theorem cuspParameter_add (P Q : (cuspCurve F).toAffine.Point) :
    cuspParameter (P + Q) = cuspParameter P + cuspParameter Q := by
  cases P with
  | zero => simp only [← Affine.Point.zero_def, zero_add, cuspParameter]
  | some x y h =>
    cases Q with
    | zero => simp only [← Affine.Point.zero_def, add_zero, cuspParameter]
    | some x' y' h' =>
      obtain ⟨hx, hy⟩ := cuspCurve_coordinates_ne_zero h
      obtain ⟨hx', hy'⟩ := cuspCurve_coordinates_ne_zero h'
      obtain ⟨ex, ey⟩ := cuspCurve_coordinates_parameter h
      obtain ⟨ex', ey'⟩ := cuspCurve_coordinates_parameter h'
      have hh := cuspParameter_add_some (inv_ne_zero (div_ne_zero hx hy))
        (inv_ne_zero (div_ne_zero hx' hy'))
        (cuspCurve_nonsingular_param (div_ne_zero hx hy))
        (cuspCurve_nonsingular_param (div_ne_zero hx' hy'))
      simpa only [ex, ey, ex', ey', inv_inv, cuspParameter] using hh

/-- The smooth cusp group is the additive group of the field, in every characteristic. -/
noncomputable def cuspParameterAddEquiv : (cuspCurve F).toAffine.Point ≃+ F :=
  { cuspParameterEquiv with map_add' := cuspParameter_add }

end FLT.Mazur
