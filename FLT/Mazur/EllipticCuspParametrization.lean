/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNormalizedSingularity
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Parametrizing the smooth points of the standard cusp

The parameter x/y sends infinity to zero and identifies the smooth points
of y²=x³ with the field. No restriction on the characteristic is needed.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable (F : Type*) [Field F]

/-- The standard cuspidal Weierstrass equation y²=x³. -/
def cuspCurve : WeierstrassCurve F := ⟨0, 0, 0, 0, 0⟩

variable {F}

/-- The equation of the standard cusp. -/
theorem cuspCurve_equation_iff (x y : F) :
    (cuspCurve F).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 := by
  simp [Affine.equation_iff', cuspCurve, sub_eq_zero]

/-- Both coordinates of a smooth affine point of the cusp are nonzero. -/
theorem cuspCurve_coordinates_ne_zero {x y : F}
    (h : (cuspCurve F).toAffine.Nonsingular x y) : x ≠ 0 ∧ y ≠ 0 := by
  have he := (cuspCurve_equation_iff x y).mp h.1
  have hn := (normalized_nonsingular_iff (cuspCurve F) rfl rfl rfl h.1).mp h
  constructor
  · intro hx
    have hy : y = 0 := by simpa [hx] using he
    exact hn ⟨hx, hy⟩
  · intro hy
    have hx : x = 0 := by simpa [hy] using he.symm
    exact hn ⟨hx, hy⟩

/-- Nonzero parameters give smooth affine points, including in characteristics two and three. -/
theorem cuspCurve_nonsingular_param {t : F} (ht : t ≠ 0) :
    (cuspCurve F).toAffine.Nonsingular (t⁻¹ ^ 2) (t⁻¹ ^ 3) := by
  have he : (cuspCurve F).toAffine.Equation (t⁻¹ ^ 2) (t⁻¹ ^ 3) := by
    rw [cuspCurve_equation_iff]
    ring
  exact (normalized_nonsingular_iff (cuspCurve F) rfl rfl rfl he).mpr
    (fun h => (pow_ne_zero 2 (inv_ne_zero ht)) h.1)

/-- The cusp parameter, with value zero at infinity. -/
def cuspParameter : (cuspCurve F).toAffine.Point → F
  | .zero => 0
  | .some x y _ => x / y

/-- The point with the given cusp parameter. -/
noncomputable def cuspPoint (t : F) : (cuspCurve F).toAffine.Point := by
  classical
  exact if ht : t = 0 then .zero
  else .some (t⁻¹ ^ 2) (t⁻¹ ^ 3) (cuspCurve_nonsingular_param ht)

/-- The affine coordinates are recovered from their cusp parameter. -/
theorem cuspCurve_coordinates_parameter {x y : F}
    (h : (cuspCurve F).toAffine.Nonsingular x y) :
    (x / y)⁻¹ ^ 2 = x ∧ (x / y)⁻¹ ^ 3 = y := by
  obtain ⟨hx, hy⟩ := cuspCurve_coordinates_ne_zero h
  have he := (cuspCurve_equation_iff x y).mp h.1
  rw [inv_div]
  constructor
  · field_simp
    exact he
  · field_simp [hx, hy]
    exact he

/-- Taking the parameter of the constructed point is the identity. -/
theorem cuspParameter_cuspPoint (t : F) : cuspParameter (cuspPoint t) = t := by
  classical
  by_cases ht : t = 0
  · simp [cuspPoint, ht, cuspParameter]
  · simp only [cuspPoint, dite_eq_right ht, cuspParameter]
    field_simp

/-- Reconstructing a smooth point from its parameter is the identity. -/
theorem cuspPoint_cuspParameter (P : (cuspCurve F).toAffine.Point) :
    cuspPoint (cuspParameter P) = P := by
  classical
  cases P with
  | zero => simp [cuspParameter, cuspPoint]
  | some x y h =>
    obtain ⟨hx, hy⟩ := cuspCurve_coordinates_ne_zero h
    obtain ⟨hxx, hyy⟩ := cuspCurve_coordinates_parameter h
    change cuspPoint (x / y) = _
    rw [cuspPoint, dite_eq_right (div_ne_zero hx hy)]
    exact (Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hxx, hyy⟩

/-- The smooth points of the standard cusp are parametrized by the field. -/
noncomputable def cuspParameterEquiv : (cuspCurve F).toAffine.Point ≃ F where
  toFun := cuspParameter
  invFun := cuspPoint
  left_inv := cuspPoint_cuspParameter
  right_inv := cuspParameter_cuspPoint

end FLT.Mazur
