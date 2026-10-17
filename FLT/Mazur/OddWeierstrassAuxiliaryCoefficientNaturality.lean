/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassEquationCoefficientProjection
public import FLT.Mazur.OddWeierstrassAuxiliaryProperNaturality
public import FLT.Mazur.WeierstrassProperCoefficientComposition

/-!
# The original coefficient comparisons commute with coefficient transitions

The first projections of the actual original and normalized group comparisons
are the proper coefficient maps. Both retain their full coefficient squares.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart
open IntegralWeierstrassParameter (oddChartEquation)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S]
  (g : AuxiliarySectionRing →+* R)

/-- The actual proper projection of the original coefficient comparison. -/
def auxiliaryOriginalCoefficientProjection :
    integralCurve (auxiliaryPullbackEquation g) ⟶ integralCurve oddChartEquation :=
  properCoefficientMap oddChartEquation _ (auxiliaryCoefficientHom g)
    (auxiliaryPullbackEquation_coefficient g)

/-- The actual proper projection of the normalized coefficient comparison. -/
def auxiliaryNormalizedCoefficientProjection :
    integralCurve (auxiliaryNormalizedEquation g) ⟶ integralCurve oddChartEquation :=
  properCoefficientMap oddChartEquation _ (auxiliaryNormalizedCoefficientHom g)
    (auxiliaryNormalizedCoefficientHom_equation g).symm

/-- The original group comparison retains the original proper coefficient projection. -/
@[reassoc] theorem auxiliaryCoefficientGroupIso_proper_fst :
    (auxiliaryCoefficientGroupIso g).hom.hom.hom.hom.left ≫
        pullback.fst universalGroup.hom (auxiliaryCoefficientBase g) =
      auxiliaryOriginalCoefficientProjection g := by
  rw [auxiliaryCoefficientGroupIso_def]
  exact equationCoefficientComparison_fst _ _ _ _ _ _

/-- The normalized group comparison retains the normalized proper coefficient projection. -/
@[reassoc] theorem auxiliaryNormalizedCoefficientGroupIso_proper_fst :
    (auxiliaryNormalizedCoefficientGroupIso g).hom.hom.hom.hom.left ≫
        pullback.fst universalGroup.hom (auxiliaryNormalizedCoefficientBase g) =
      auxiliaryNormalizedCoefficientProjection g := by
  rw [auxiliaryNormalizedCoefficientGroupIso_def]
  exact equationCoefficientComparison_fst _ _ _ _ _ _

/-- Original proper coefficient projections commute with every ring homomorphism. -/
@[reassoc] theorem auxiliaryOriginalCoefficientProjection_natural (f : R →+* S) :
    auxiliaryOriginalCoefficientTransition g f ≫ auxiliaryOriginalCoefficientProjection g =
      auxiliaryOriginalCoefficientProjection (f.comp g) := by
  exact properCoefficientMap_comp oddChartEquation _ _ (auxiliaryCoefficientHom g) f
    (auxiliaryPullbackEquation_coefficient g) (auxiliaryPullbackEquation_natural g f)
    (auxiliaryPullbackEquation_coefficient (f.comp g))

/-- Normalized proper coefficient projections commute with every ring homomorphism. -/
@[reassoc] theorem auxiliaryNormalizedCoefficientProjection_natural (f : R →+* S) :
    auxiliaryNormalizedCoefficientTransition g f ≫ auxiliaryNormalizedCoefficientProjection g =
      auxiliaryNormalizedCoefficientProjection (f.comp g) := by
  have h : auxiliaryNormalizedEquation (f.comp g) =
      oddChartEquation.map (f.comp (auxiliaryNormalizedCoefficientHom g)) := by
    rw [auxiliaryNormalizedCoefficientHom_natural, auxiliaryNormalizedCoefficientHom_equation]
  have hc := properCoefficientMap_comp oddChartEquation _ _
    (auxiliaryNormalizedCoefficientHom g) f
    (auxiliaryNormalizedCoefficientHom_equation g).symm
    (auxiliaryNormalizedEquation_natural g f) h
  change properCoefficientMap _ _ f (auxiliaryNormalizedEquation_natural g f) ≫
    properCoefficientMap _ _ (auxiliaryNormalizedCoefficientHom g)
      (auxiliaryNormalizedCoefficientHom_equation g).symm =
    properCoefficientMap _ _ (auxiliaryNormalizedCoefficientHom (f.comp g))
      (auxiliaryNormalizedCoefficientHom_equation (f.comp g)).symm
  simpa only [auxiliaryNormalizedCoefficientHom_natural] using hc

end FLT.Mazur.OddWeierstrassParameter
