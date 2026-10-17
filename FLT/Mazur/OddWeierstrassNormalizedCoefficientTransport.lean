/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryCoefficientNaturality
public import FLT.Mazur.OddWeierstrassAuxiliaryFixedCoefficient

/-!
# Equal normalized equations retain the actual coefficient projections

Equality of the equations determines the maps out of the universal coefficient
ring. The resulting equality transport commutes with the proper projections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open IntegralWeierstrassParameter (OddChartRing oddChartEquation)
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

/-- Equal equations and coefficient maps retain the actual odd cubic projection. -/
@[reassoc] theorem equationCoefficientProjection_transport
    (W V : WeierstrassCurve R) (f g : OddChartRing →+* R)
    (hf : W = oddChartEquation.map f) (hg : V = oddChartEquation.map g)
    (h : W = V) (he : f = g) :
    eqToHom (congrArg integralCurve h) ≫
        properCoefficientMap oddChartEquation V g hg =
      properCoefficientMap oddChartEquation W f hf := by
  cases h
  cases he
  exact Category.id_comp _

/-- The entire normalized equation determines the original normalized coefficient map. -/
theorem auxiliaryNormalizedCoefficientHom_eq_of_equation
    (g k : AuxiliarySectionRing →+* R)
    (h : auxiliaryNormalizedEquation g = auxiliaryNormalizedEquation k) :
    auxiliaryNormalizedCoefficientHom g = auxiliaryNormalizedCoefficientHom k := by
  apply parameterHom_eq_of_equation
  rw [auxiliaryNormalizedCoefficientHom_equation, auxiliaryNormalizedCoefficientHom_equation]
  exact h

/-- Equality of normalized equations commutes with their actual universal cubic projections. -/
@[reassoc] theorem auxiliaryNormalizedCoefficientProjection_transport
    (g k : AuxiliarySectionRing →+* R)
    (h : auxiliaryNormalizedEquation g = auxiliaryNormalizedEquation k) :
    eqToHom (congrArg integralCurve h) ≫ auxiliaryNormalizedCoefficientProjection k =
      auxiliaryNormalizedCoefficientProjection g :=
  equationCoefficientProjection_transport _ _ _ _ _ _ h
    (auxiliaryNormalizedCoefficientHom_eq_of_equation g k h)

end FLT.Mazur.OddWeierstrassParameter
