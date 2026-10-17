/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedSliceFixed
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeRelativePoint

/-!
# Normalization fixes the actual odd-chart coefficients on the normalized frame

The five coefficients determine maps out of the localized odd coefficient ring.
The identity frame change therefore preserves the entire original parameter map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open IntegralWeierstrassParameter (SmoothRing OddChartRing oddChartEquation)
variable {R : Type} [CommRing R]

/-- Equality of full equations determines the original odd-chart coefficient maps. -/
theorem parameterHom_eq_of_equation (f g : OddChartRing →+* R)
    (h : oddChartEquation.map f = oddChartEquation.map g) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (3 : SmoothRing))
  apply IntegralWeierstrassParameter.smoothRing_hom_ext
  intro i
  fin_cases i
  · exact congrArg WeierstrassCurve.a₁ h
  · exact congrArg WeierstrassCurve.a₂ h
  · exact congrArg WeierstrassCurve.a₃ h
  · exact congrArg WeierstrassCurve.a₄ h
  · exact congrArg WeierstrassCurve.a₆ h

variable (g : AuxiliarySectionRing →+* R) (hn : SatisfiesNormalization g)

include hn in
/-- The normalized odd coefficient map equals the original map on every normalized frame. -/
theorem auxiliaryNormalizedCoefficientHom_fixed :
    auxiliaryNormalizedCoefficientHom g = auxiliaryCoefficientHom g := by
  apply parameterHom_eq_of_equation
  rw [auxiliaryNormalizedCoefficientHom_equation, normalizedSlice_equation_fixed g hn,
    auxiliaryPullbackEquation_coefficient]

include hn in
/-- The actual normalized coefficient spectrum map also stays unchanged. -/
theorem auxiliaryNormalizedCoefficientBase_fixed :
    auxiliaryNormalizedCoefficientBase g = auxiliaryCoefficientBase g :=
  congrArg (fun z ↦ Spec.map (CommRingCat.ofHom z))
    (auxiliaryNormalizedCoefficientHom_fixed g hn)

/-- Every normalized arbitrary-source frame retains its actual original coefficient base. -/
theorem auxiliarySchemeNormalizedBase_fixed {T : Scheme} (f : T ⟶ levelThree.left)
    (h : SatisfiesNormalization f.appTop.hom) :
    auxiliarySchemeNormalizedPoint f ≫ levelThree.hom = f ≫ levelThree.hom := by
  rw [auxiliarySchemeNormalizedPoint_base,
    auxiliaryNormalizedCoefficientBase_fixed f.appTop.hom h]
  exact auxiliarySchemeSections_base f

end FLT.Mazur.OddWeierstrassParameter
