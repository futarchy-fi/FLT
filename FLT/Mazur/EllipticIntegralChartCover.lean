/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticProjectiveReduction

/-!
# Two integral charts cover every elliptic point

On a primitive integral solution of the Weierstrass cubic, Y or Z is a unit.
Thus the usual affine chart and the chart at infinity suffice, even when the
special cubic is singular. Normalization takes place over the valuation ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- The two standard integral charts cover a primitive point on the cubic. -/
theorem PrimitiveLift.unit_Y_or_Z
    {P : (W.map (algebraMap A K)).toProjective.Point} (v : PrimitiveLift A P.point) :
    IsUnit (v.coords 1) ∨ IsUnit (v.coords 2) := by
  by_contra h
  obtain ⟨hy, hz⟩ := not_or.mp h
  have hy0 : residue A (v.coords 1) = 0 := by
    by_contra hh
    exact hy ((residue_ne_zero_iff_isUnit _).mp hh)
  have hz0 : residue A (v.coords 2) = 0 := by
    by_contra hh
    exact hz ((residue_ne_zero_iff_isUnit _).mp hh)
  have hx0 : residue A (v.coords 0) = 0 := by
    have he := (v.residue_equation A W)
    exact eq_zero_of_pow_eq_zero
      (((W.map (residue A)).toProjective.equation_of_Z_eq_zero hz0).mp he)
  obtain ⟨i, hi⟩ := v.residue_ne_zero A
  fin_cases i <;> contradiction

variable {A}

/-- Normalize a primitive representative using one of its unit coordinates. -/
def PrimitiveLift.normalize {P : PointClass K} (v : PrimitiveLift A P)
    (j : Fin 3) (hj : IsUnit (v.coords j)) : PrimitiveLift A P where
  coords := (↑hj.unit⁻¹ : A) • v.coords
  primitive := ⟨j, by
    change IsUnit ((↑hj.unit⁻¹ : A) * v.coords j)
    exact (Units.inv_mul_eq_one.mpr hj.unit_spec).symm ▸ isUnit_one⟩
  represents := by
    refine Eq.trans ?_ v.represents
    apply Quotient.sound
    refine ⟨Units.map (algebraMap A K) hj.unit⁻¹, ?_⟩
    funext i
    exact (map_mul (algebraMap A K) _ _).symm

/-- The selected coordinate of the normalized representative is exactly one. -/
@[simp] theorem PrimitiveLift.normalize_self {P : PointClass K} (v : PrimitiveLift A P)
    (j : Fin 3) (hj : IsUnit (v.coords j)) : (v.normalize j hj).coords j = 1 := by
  change (↑hj.unit⁻¹ : A) * v.coords j = 1
  exact Units.inv_mul_eq_one.mpr hj.unit_spec

variable (A)

/-- Every generic point extends to one of the two normalized integral charts. -/
theorem exists_integralChartLift (P : (W.map (algebraMap A K)).toProjective.Point) :
    ∃ (j : Fin 3) (v : PrimitiveLift A P.point), (j = 1 ∨ j = 2) ∧ v.coords j = 1 := by
  let v := primitiveLift A W P
  rcases v.unit_Y_or_Z A W with h | h
  · exact ⟨1, v.normalize 1 h, Or.inl rfl, v.normalize_self 1 h⟩
  · exact ⟨2, v.normalize 2 h, Or.inr rfl, v.normalize_self 2 h⟩

/-- Chart normalization preserves actual projective reduction. -/
theorem PrimitiveLift.normalize_reduction {P : PointClass K} (v : PrimitiveLift A P)
    (j : Fin 3) (hj : IsUnit (v.coords j)) : (v.normalize j hj).reduction = v.reduction :=
  PrimitiveLift.reduction_eq A _ _

end FLT.Mazur
