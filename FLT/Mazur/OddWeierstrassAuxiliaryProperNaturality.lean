/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizationGroup
public import FLT.Mazur.UniversalWeierstrassAuxiliaryProperNaturality
public import FLT.Mazur.OddWeierstrassAuxiliaryNormalizationNatural
public import FLT.Mazur.WeierstrassVariableChangeProperCoefficient

/-!
# Actual proper normalization commutes with arbitrary coefficient maps

Original and normalized equations retain their actual equality transports under
coefficient change. The complete proper normalization commutes with these maps,
so this comparison controls every section, not only the auxiliary labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S]

/-- The actual proper cubic normalization underlying the odd group comparison. -/
def auxiliaryProperNormalization (g : AuxiliarySectionRing →+* R) :
    integralCurve (auxiliaryNormalizedEquation g) ≅ integralCurve (auxiliaryPullbackEquation g) :=
  integralVariableChangeIso _ _ (auxiliaryFrameChange g) rfl

/-- The group comparison retains the entire proper normalization map. -/
theorem auxiliaryNormalizationGroupIso_hom (g : AuxiliarySectionRing →+* R) :
    (auxiliaryNormalizationGroupIso g).hom.hom.hom.hom.left =
      (auxiliaryProperNormalization g).hom := by
  rw [auxiliaryNormalizationGroupIso_def]
  exact integralVariableChangeGroupIso_hom _ _ _ _ _ _

/-- The inverse group comparison retains the entire inverse proper map. -/
theorem auxiliaryNormalizationGroupIso_inv (g : AuxiliarySectionRing →+* R) :
    (auxiliaryNormalizationGroupIso g).inv.hom.hom.hom.left =
      (auxiliaryProperNormalization g).inv := by
  rw [auxiliaryNormalizationGroupIso_def]
  exact integralVariableChangeGroupIso_inv _ _ _ _ _ _

variable (g : AuxiliarySectionRing →+* R) (f : R →+* S)

/-- The original coefficient equation retains its actual specialization equality. -/
theorem auxiliaryPullbackEquation_natural :
    auxiliaryPullbackEquation (f.comp g) = (auxiliaryPullbackEquation g).map f := by
  simp only [auxiliaryPullbackEquation, WeierstrassCurve.map_map]

/-- The actual coefficient transition between the original proper auxiliary cubics. -/
def auxiliaryOriginalCoefficientTransition :
    integralCurve (auxiliaryPullbackEquation (f.comp g)) ⟶
      integralCurve (auxiliaryPullbackEquation g) := by
  let _ : Algebra R S := f.toAlgebra
  exact eqToHom (congrArg integralCurve (auxiliaryPullbackEquation_natural g f)) ≫
    integralCoefficientMorphism (S := S) (auxiliaryPullbackEquation g)

/-- The actual coefficient transition between the normalized proper auxiliary cubics. -/
def auxiliaryNormalizedCoefficientTransition :
    integralCurve (auxiliaryNormalizedEquation (f.comp g)) ⟶
      integralCurve (auxiliaryNormalizedEquation g) := by
  let _ : Algebra R S := f.toAlgebra
  exact eqToHom (congrArg integralCurve (auxiliaryNormalizedEquation_natural g f)) ≫
    integralCoefficientMorphism (S := S) (auxiliaryNormalizedEquation g)

/-- The entire actual proper normalization commutes with every ring homomorphism. -/
@[reassoc] theorem auxiliaryProperNormalization_natural :
    auxiliaryNormalizedCoefficientTransition g f ≫ (auxiliaryProperNormalization g).hom =
      (auxiliaryProperNormalization (f.comp g)).hom ≫
        auxiliaryOriginalCoefficientTransition g f := by
  let _ : Algebra R S := f.toAlgebra
  have hc := integralVariableChangeTo_coefficient (S := S)
    (auxiliaryPullbackEquation g) (auxiliaryNormalizedEquation g) (auxiliaryFrameChange g) rfl
  have he := UniversalWeierstrass.properVariableChange_congr
    (auxiliaryPullbackEquation (f.comp g)) (auxiliaryNormalizedEquation (f.comp g))
    ((auxiliaryPullbackEquation g).map f) ((auxiliaryNormalizedEquation g).map f)
    (auxiliaryFrameChange (f.comp g)) ((auxiliaryFrameChange g).map f) rfl
    (variableChange_coefficient_equation (S := S) _ _ _ rfl)
    (auxiliaryPullbackEquation_natural g f) (auxiliaryNormalizedEquation_natural g f)
    (auxiliaryFrameChange_natural g f)
  change (eqToHom _ ≫ integralCoefficientMorphism (auxiliaryNormalizedEquation g)) ≫
      integralVariableChangeTo _ _ _ _ =
    integralVariableChangeTo _ _ _ _ ≫
      (eqToHom _ ≫ integralCoefficientMorphism (auxiliaryPullbackEquation g))
  rw [Category.assoc, hc, ← Category.assoc]
  exact (congrArg (fun z ↦ z ≫ integralCoefficientMorphism (S := S)
    (auxiliaryPullbackEquation g)) he.symm).trans (Category.assoc _ _ _)

/-- The inverse proper normalization also retains the original coefficient transitions. -/
@[reassoc] theorem auxiliaryProperNormalization_inv_natural :
    (auxiliaryProperNormalization (f.comp g)).inv ≫
        auxiliaryNormalizedCoefficientTransition g f =
      auxiliaryOriginalCoefficientTransition g f ≫ (auxiliaryProperNormalization g).inv := by
  apply (cancel_epi (auxiliaryProperNormalization (f.comp g)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← auxiliaryProperNormalization_natural]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.OddWeierstrassParameter
