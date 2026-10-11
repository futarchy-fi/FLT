/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingPuncturedGroupAtlas
public import FLT.Mazur.OneGonSmoothingSchemeNormalizedMarking
public import FLT.Mazur.OverPullbackSectionComposition

/-!
# The punctured arbitrary-source comparison retains labels and complete infinity

Every actual normalized universal label is the original punctured atlas label.
The complete-family comparison sends its identity section to the displayed
infinity section of the original complete smoothing, over every source scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type) [CommRing R] (h₂ : IsUnit (2 : R))
  {T : Scheme} (j : T ⟶ puncturedAtlasScheme R h₂)

/-- The actual normalized universal labeling is the original punctured atlas marking. -/
theorem puncturedAtlasNormalizedGroupIso_marking (a : Labels 4) :
    auxiliarySchemeMarking (auxiliarySchemeNormalizedPoint (j ≫ puncturedAtlasPoint R h₂)) a ≫
      (puncturedAtlasNormalizedGroupIso R h₂ j).hom.hom.hom.hom =
        puncturedAtlasMarking R h₂ j a :=
  smoothSchemeNormalizedGroupIso_marking _ _ _ _ _ a

/-- The punctured-to-complete comparison retains the actual inclusion of original cubics. -/
@[reassoc] theorem puncturedCompleteBoundaryIso_fst :
    (puncturedCompleteBoundaryIso R).hom.left ≫
      pullback.fst (family (PowerSeries.X : PowerSeries R)).hom (puncturedBaseInclusion R) =
        puncturedCurveInclusion R :=
  (puncturedComplete_isPullback R).isoPullback_hom_fst

/-- The arbitrary-source complete comparison retains its two original family projections. -/
@[reassoc] theorem puncturedAtlasCompleteOverIso_fst :
    (puncturedAtlasCompleteOverIso R h₂ j).hom.left ≫
      pullback.fst (family (PowerSeries.X : PowerSeries R)).hom
        ((j ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R) =
          pullback.fst (puncturedFamily R).hom (j ≫ puncturedAtlasProjection R h₂) ≫
            puncturedCurveInclusion R := by
  change (((Over.pullback (j ≫ puncturedAtlasProjection R h₂)).map
    (puncturedCompleteBoundaryIso R).hom).left ≫
      ((Over.pullbackComp (j ≫ puncturedAtlasProjection R h₂)
        (puncturedBaseInclusion R)).inv.app
          (family (PowerSeries.X : PowerSeries R))).left) ≫ _ = _
  rw [Category.assoc, OverPullbackSection.comp_inv_fst]
  simp only [Over.pullback_map_left, ← Category.assoc, pullback.lift_fst]
  rw [Category.assoc, puncturedCompleteBoundaryIso_fst]

/-- Every normalized label retains its original section on the actual complete smoothing. -/
@[reassoc] theorem puncturedAtlasSchemeFamilyIso_marking_fst (a : Labels 4) :
    (auxiliarySchemeMarking
      (auxiliarySchemeNormalizedPoint (j ≫ puncturedAtlasPoint R h₂)) a).left ≫
        (puncturedAtlasSchemeFamilyIso R h₂ j).hom.left ≫
          pullback.fst (family (PowerSeries.X : PowerSeries R)).hom
            ((j ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R) =
              (puncturedAtlasMarking R h₂ j a).left ≫
                pullback.fst (puncturedFamily R).hom (j ≫ puncturedAtlasProjection R h₂) ≫
                  puncturedCurveInclusion R := by
  change _ ≫ ((puncturedAtlasNormalizedGroupIso R h₂ j).hom.hom.hom.hom.left ≫
    (puncturedAtlasCompleteOverIso R h₂ j).hom.left) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, ← Over.comp_left,
    puncturedAtlasNormalizedGroupIso_marking, Category.assoc, puncturedAtlasCompleteOverIso_fst]

/-- The normalized identity remains the original complete-family infinity over any source. -/
@[reassoc] theorem puncturedAtlasSchemeFamilyIso_one_fst :
    (auxiliarySchemeMarking
      (auxiliarySchemeNormalizedPoint (j ≫ puncturedAtlasPoint R h₂)) 1).left ≫
        (puncturedAtlasSchemeFamilyIso R h₂ j).hom.left ≫
          pullback.fst (family (PowerSeries.X : PowerSeries R)).hom
            ((j ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R) =
              ((j ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R) ≫
                marking (PowerSeries.X : PowerSeries R) := by
  rw [puncturedAtlasSchemeFamilyIso_marking_fst, ← Category.assoc,
    smoothOverlapMarking_one_fst, Category.assoc, puncturedCurveInclusion_marking]
  simp only [Category.assoc, puncturedAtlasProjection]

/-- The displayed complete infinity comparison commutes with arbitrary source change. -/
theorem puncturedAtlasSchemeFamilyIso_one_natural {U : Scheme} (k : U ⟶ T) :
    (auxiliarySchemeMarking
      (auxiliarySchemeNormalizedPoint ((k ≫ j) ≫ puncturedAtlasPoint R h₂)) 1).left ≫
        (puncturedAtlasSchemeFamilyIso R h₂ (k ≫ j)).hom.left ≫
          pullback.fst (family (PowerSeries.X : PowerSeries R)).hom
            (((k ≫ j) ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R) =
              k ≫ (auxiliarySchemeMarking
                (auxiliarySchemeNormalizedPoint (j ≫ puncturedAtlasPoint R h₂)) 1).left ≫
                  (puncturedAtlasSchemeFamilyIso R h₂ j).hom.left ≫
                    pullback.fst (family (PowerSeries.X : PowerSeries R)).hom
                      ((j ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R) := by
  rw [puncturedAtlasSchemeFamilyIso_one_fst, puncturedAtlasSchemeFamilyIso_one_fst]
  simp only [Category.assoc]

end FLT.Mazur.OneGonSmoothing
