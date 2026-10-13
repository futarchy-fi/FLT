/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSpecializationGroup
public import FLT.Mazur.OddWeierstrassSpecialization
public import FLT.Mazur.OddWeierstrassAuxiliaryLevel

/-!
# Original smooth cubics as coefficient pullbacks of the universal group

The map specializes to the five original coefficients. The group comparison
uses the established coefficient base-change isomorphism and only the proved
equality of equations, preserving the existing group operations on both sides.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart
open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant)
open UniversalWeierstrass (equationGroupIso)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]

variable (W : WeierstrassCurve R) (h₃ : IsUnit (3 : R)) (hΔ : IsUnit W.Δ)

/-- The actual parameter map given by the five original coefficients. -/
def specializationBase : Spec (.of R) ⟶ parameterBase :=
  Spec.map (CommRingCat.ofHom (specialize W h₃ hΔ))

/-- The original cubic group is the actual coefficient pullback of the universal group. -/
def specializationGroupIso : integralCurveGroup W hΔ ≅
    (Over.pullback (specializationBase W h₃ hΔ)).mapCommGrp.obj
      (integralCurveGroup oddChartEquation oddChart_discriminant) := by
  let _ : Algebra OddChartRing R := (specialize W h₃ hΔ).toAlgebra
  have he : oddChartEquation.map (algebraMap OddChartRing R) = W :=
    oddChartEquation_specialize W h₃ hΔ
  let hv : IsUnit (oddChartEquation.map (algebraMap OddChartRing R)).Δ := he.symm ▸ hΔ
  exact equationGroupIso he.symm hΔ hv ≪≫
    integralCurveCoefficientGroupIso oddChartEquation oddChart_discriminant hv

end FLT.Mazur.OddWeierstrassParameter
