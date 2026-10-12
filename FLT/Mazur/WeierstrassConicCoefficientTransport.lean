/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXConicPuncturedParameters
public import FLT.Mazur.WeierstrassDividedShearData

/-!
# Conic transport retains the equation and both signed punctures

Changing an equal tangent coefficient preserves the whole conic algebra,
including both original coordinates and the two Laurent parameter maps.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassSuccessiveX WeierstrassDividedDepth
variable {R : Type*} [CommRing R] {a b : R} (c : R) (h : a = b)

/-- Transport the entire conic along an equality of tangent coefficients. -/
def conicCoefficientTransport : ConicCoordinate a c ≃ₐ[R] ConicCoordinate b c := by
  subst b
  exact AlgEquiv.refl

/-- Coefficient transport preserves the original incidence coordinate. -/
theorem conicCoefficientTransport_t :
    conicCoefficientTransport c h (conicT a c) = conicT b c := by
  subst b
  rfl

/-- Coefficient transport preserves the original slope coordinate. -/
theorem conicCoefficientTransport_v :
    conicCoefficientTransport c h (conicV a c) = conicV b c := by
  subst b
  rfl

variable (W V : WeierstrassCurve R) (ha : W.a₁ = V.a₁) (hc : c = 0)

/-- The positive puncture commutes with the full conic coefficient transport. -/
theorem conicPuncturedFirst_coefficientTransport :
    (conicPuncturedFirst V c hc).comp (conicCoefficientTransport c ha).toAlgHom =
      conicPuncturedFirst W c hc := by
  apply conic_hom_ext
  · simp only [AlgHom.comp_apply, 
      AlgEquiv.coe_toAlgHom, conicCoefficientTransport_t,
      conicPuncturedFirst, conicEvaluation_t, ha]
  · simp only [AlgHom.comp_apply, 
      AlgEquiv.coe_toAlgHom, conicCoefficientTransport_v,
      conicPuncturedFirst, conicEvaluation_v]

/-- The opposite puncture keeps its sign and slope under the same transport. -/
theorem conicPuncturedSecond_coefficientTransport :
    (conicPuncturedSecond V c hc).comp (conicCoefficientTransport c ha).toAlgHom =
      conicPuncturedSecond W c hc := by
  apply conic_hom_ext
  · simp only [AlgHom.comp_apply, 
      AlgEquiv.coe_toAlgHom, conicCoefficientTransport_t,
      conicPuncturedSecond, conicEvaluation_t, ha]
  · simp only [AlgHom.comp_apply, 
      AlgEquiv.coe_toAlgHom, conicCoefficientTransport_v,
      conicPuncturedSecond, conicEvaluation_v, ha]

/-- Root zero preserves the original tangent coefficient. -/
theorem rootShearZero_tangent (W : WeierstrassCurve R) :
    (rootShearCurve W 0).a₁ = W.a₁ := by
  rw [(rootShearCurve_coefficients 0).1, mul_zero, add_zero]

end FLT.Mazur.WeierstrassModificationX
