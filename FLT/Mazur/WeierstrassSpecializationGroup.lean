/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCoefficientGroup
public import FLT.Mazur.UniversalWeierstrassAuxiliaryLevel

/-!
# Original smooth cubics as coefficient pullbacks of the universal group

The map specializes to the five original coefficients. The group comparison
uses the established coefficient base-change isomorphism and only the proved
equality of equations, preserving the existing group operations on both sides.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]

/-- Equality of equations identifies their established group objects. -/
def equationGroupIso {W V : WeierstrassCurve R} (h : W = V)
    (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) : integralCurveGroup W hW ≅ integralCurveGroup V hV := by
  subst V
  exact Iso.refl _

variable (W : WeierstrassCurve R) (h₂ : IsUnit (2 : R)) (hΔ : IsUnit W.Δ)

/-- The actual parameter map given by the five original coefficients. -/
def specializationBase : Spec (.of R) ⟶ parameterBase :=
  Spec.map (CommRingCat.ofHom (specialize W h₂ hΔ))

/-- The original cubic group is the actual coefficient pullback of the universal group. -/
def specializationGroupIso : integralCurveGroup W hΔ ≅
    (Over.pullback (specializationBase W h₂ hΔ)).mapCommGrp.obj
      (integralCurveGroup smoothEquation smoothEquation_discriminant) := by
  let _ : Algebra ParameterRing R := (specialize W h₂ hΔ).toAlgebra
  have he : smoothEquation.map (algebraMap ParameterRing R) = W :=
    smoothEquation_specialize W h₂ hΔ
  let hv : IsUnit (smoothEquation.map (algebraMap ParameterRing R)).Δ := he.symm ▸ hΔ
  exact equationGroupIso he.symm hΔ hv ≪≫
    integralCurveCoefficientGroupIso smoothEquation smoothEquation_discriminant hv

end FLT.Mazur.UniversalWeierstrass
