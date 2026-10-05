/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSplitNodeParametrization

/-!
# Multiplication of smooth split-node parameters

The parameter r/(r+a) turns the existing point addition on y²+a·xy=x³
into multiplication, including tangent and vertical lines in characteristic two.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- A nonvertical pair in the smooth split-node chart cannot consist of opposite points. -/
theorem splitNodeCurve_param_nonvertical {a r s : F} (hr : r ≠ 0) (hra : r + a ≠ 0)
    (hsum : r + s + a ≠ 0) :
    ¬ (r * (r + a) = s * (s + a) ∧ r ^ 2 * (r + a) =
      (splitNodeCurve a).toAffine.negY (s * (s + a)) (s ^ 2 * (s + a))) := by
  rintro ⟨hx, hy⟩
  have hrs : r = s := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (r - s) * (r + s + a) = 0 by
      linear_combination hx)).resolve_right hsum
  subst s
  simp only [Affine.negY, splitNodeCurve, toAffine, sub_zero] at hy
  apply mul_ne_zero (mul_ne_zero hr hra) hsum
  linear_combination hy

/-- The secant and tangent slopes share one formula in the smooth split-node chart. -/
theorem splitNodeCurve_slope {a r s : F} (hr : r ≠ 0) (hra : r + a ≠ 0)
    (hsum : r + s + a ≠ 0) :
    (splitNodeCurve a).toAffine.slope (r * (r + a)) (s * (s + a))
      (r ^ 2 * (r + a)) (s ^ 2 * (s + a)) =
      (r ^ 2 + r * s + s ^ 2 + a * (r + s)) / (r + s + a) := by
  by_cases hx : r * (r + a) = s * (s + a)
  · have hrs : r = s := by
      apply sub_eq_zero.mp
      exact (mul_eq_zero.mp (show (r - s) * (r + s + a) = 0 by
        linear_combination hx)).resolve_right hsum
    subst s
    have hy := fun h => splitNodeCurve_param_nonvertical hr hra hsum ⟨rfl, h⟩
    rw [Affine.slope_of_Y_ne rfl hy]
    have hd : r ^ 2 * (r + a) -
        (splitNodeCurve a).toAffine.negY (r * (r + a)) (r ^ 2 * (r + a)) ≠ 0 :=
      sub_ne_zero.mpr hy
    simp only [Affine.negY, splitNodeCurve, toAffine, add_zero, sub_zero] at hd ⊢
    field_simp
    ring
  · rw [Affine.slope_of_X_ne hx]
    field_simp
    ring

omit [DecidableEq F] in
/-- Nonvertical addition has slope parameter rs/(r+s+a). -/
theorem splitNodeCurve_add_coordinates {a r s : F} (hsum : r + s + a ≠ 0) :
    let l := (r ^ 2 + r * s + s ^ 2 + a * (r + s)) / (r + s + a)
    let t := r * s / (r + s + a)
    (splitNodeCurve a).toAffine.addX (r * (r + a)) (s * (s + a)) l = t * (t + a) ∧
      (splitNodeCurve a).toAffine.addY (r * (r + a)) (s * (s + a))
        (r ^ 2 * (r + a)) l = t ^ 2 * (t + a) := by
  dsimp [Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, splitNodeCurve, toAffine]
  constructor <;> field_simp <;> ring

/-- Split-node parameters multiply under addition of smooth affine points. -/
theorem splitNodeParameter_add_some {a r s : F}
    (hr : r ≠ 0) (hra : r + a ≠ 0) (hs : s ≠ 0) (hsa : s + a ≠ 0)
    (h₁ : (splitNodeCurve a).toAffine.Nonsingular (r * (r + a)) (r ^ 2 * (r + a)))
    (h₂ : (splitNodeCurve a).toAffine.Nonsingular (s * (s + a)) (s ^ 2 * (s + a))) :
    splitNodeParameter a (.some _ _ h₁ + .some _ _ h₂) = r / (r + a) * (s / (s + a)) := by
  by_cases hsum : r + s + a = 0
  · have hrs : r = -s - a := by linear_combination hsum
    rw [Affine.Point.add_of_Y_eq (by rw [hrs]; ring) (by
      simp only [Affine.negY, splitNodeCurve, toAffine, sub_zero, hrs]
      ring)]
    change 1 = _
    field_simp
    linear_combination a * hsum
  · rw [Affine.Point.add_some (splitNodeCurve_param_nonvertical hr hra hsum)]
    have ht : r * s / (r + s + a) ≠ 0 := div_ne_zero (mul_ne_zero hr hs) hsum
    have hta : r * s / (r + s + a) + a ≠ 0 := by
      have he : r * s / (r + s + a) + a = (r + a) * (s + a) / (r + s + a) := by
        field_simp
        ring
      rw [he]
      exact div_ne_zero (mul_ne_zero hra hsa) hsum
    simp only [splitNodeCurve_slope hr hra hsum,
      (splitNodeCurve_add_coordinates hsum).1, (splitNodeCurve_add_coordinates hsum).2]
    rw [splitNodeParameter_param ht hta]
    rw [show r * s / (r + s + a) + a = (r + a) * (s + a) / (r + s + a) by
      field_simp
      ring]
    field_simp

/-- The smooth split-node parameter respects the actual point group law. -/
theorem splitNodeParameter_add (a : F) (P Q : (splitNodeCurve a).toAffine.Point) :
    splitNodeParameter a (P + Q) = splitNodeParameter a P * splitNodeParameter a Q := by
  cases P with
  | zero => simp only [← Affine.Point.zero_def, zero_add, splitNodeParameter, one_mul]
  | some x y h =>
    cases Q with
    | zero => simp only [← Affine.Point.zero_def, add_zero, splitNodeParameter, mul_one]
    | some x' y' h' =>
      obtain ⟨hr, hra⟩ := splitNodeCurve_slope_ne h
      obtain ⟨hs, hsa⟩ := splitNodeCurve_slope_ne h'
      obtain ⟨ex, ey⟩ := splitNodeCurve_coordinates_slope h
      obtain ⟨ex', ey'⟩ := splitNodeCurve_coordinates_slope h'
      have hh := splitNodeParameter_add_some hr hra hs hsa
        (splitNodeCurve_nonsingular_param hr hra) (splitNodeCurve_nonsingular_param hs hsa)
      simpa only [ex, ey, ex', ey', splitNodeParameter] using hh

end FLT.Mazur
