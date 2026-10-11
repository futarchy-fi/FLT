/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingPuncturedSchemeMarking

/-!
# Original boundary labels commute with arbitrary source change

Every overlap label, projected to the original boundary cubic, is natural in
the test scheme. Therefore the normalized complete-family comparison retains
all its displayed original labels after any change of source scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))
  {T : Scheme} (j : T ⟶ smoothAuxiliaryOverlap t h₂ ht hf)

/-- The projection of every original overlap label retains its actual boundary base. -/
@[reassoc] theorem smoothOverlapMarking_base (a : Labels 4) :
    (smoothOverlapMarking t h₂ ht hf j a).left ≫
      pullback.fst (family t).hom (j ≫ smoothAuxiliaryProjection t h₂ ht hf) ≫
        (family t).hom = j ≫ smoothAuxiliaryProjection t h₂ ht hf := by
  rw [pullback.condition, ← Category.assoc]
  have h : (smoothOverlapMarking t h₂ ht hf j a).left ≫
      pullback.snd (family t).hom (j ≫ smoothAuxiliaryProjection t h₂ ht hf) = 𝟙 T :=
    (smoothOverlapMarking t h₂ ht hf j a).w
  rw [h]
  exact Category.id_comp _

/-- All original boundary labels commute with an arbitrary change of test scheme. -/
theorem smoothOverlapMarking_source {U : Scheme} (k : U ⟶ T) (a : Labels 4) :
    (smoothOverlapMarking t h₂ ht hf (k ≫ j) a).left ≫
      pullback.fst (family t).hom ((k ≫ j) ≫ smoothAuxiliaryProjection t h₂ ht hf) =
        k ≫ (smoothOverlapMarking t h₂ ht hf j a).left ≫
          pullback.fst (family t).hom (j ≫ smoothAuxiliaryProjection t h₂ ht hf) := by
  apply (smoothUniversal_isPullback t h₂ ht hf).hom_ext
  · simp only [Category.assoc, smoothOverlapMarking_universal]
  · simp only [Category.assoc, smoothOverlapMarking_base]

variable (R) (h₂ : IsUnit (2 : R)) {T U : Scheme}
  (j : T ⟶ puncturedAtlasScheme R h₂) (k : U ⟶ T)

/-- Every displayed normalized complete-family label is natural in the source scheme. -/
theorem puncturedAtlasSchemeFamilyIso_marking_natural (a : Labels 4) :
    (auxiliarySchemeMarking
      (auxiliarySchemeNormalizedPoint ((k ≫ j) ≫ puncturedAtlasPoint R h₂)) a).left ≫
        (puncturedAtlasSchemeFamilyIso R h₂ (k ≫ j)).hom.left ≫
          pullback.fst (family (PowerSeries.X : PowerSeries R)).hom
            (((k ≫ j) ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R) =
              k ≫ (auxiliarySchemeMarking
                (auxiliarySchemeNormalizedPoint (j ≫ puncturedAtlasPoint R h₂)) a).left ≫
                  (puncturedAtlasSchemeFamilyIso R h₂ j).hom.left ≫
                    pullback.fst (family (PowerSeries.X : PowerSeries R)).hom
                      ((j ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R) := by
  rw [puncturedAtlasSchemeFamilyIso_marking_fst, puncturedAtlasSchemeFamilyIso_marking_fst]
  have h := smoothOverlapMarking_source (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R) j k a
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ puncturedCurveInclusion R) h).trans
      (by simp only [Category.assoc]))

end FLT.Mazur.OneGonSmoothing
