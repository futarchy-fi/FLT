/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingOverlapTorsionBasis
public import FLT.Mazur.OneGonSmoothingPuncturedAtlas

/-!
# The original punctured complete family retains its full auxiliary group atlas

The actual punctured auxiliary cover carries the complete boundary group and
all sixteen labels. Over any source scheme the normalized family compares with
the pullback of the original complete smoothing, through the actual puncture.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type) [CommRing R] (h₂ : IsUnit (2 : R))
  {T : Scheme} (j : T ⟶ puncturedAtlasScheme R h₂)

/-- The original boundary group over an arbitrary test of the punctured auxiliary atlas. -/
abbrev puncturedAtlasGroup :=
  smoothOverlapGroup (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R) j

/-- All sixteen labels as group sections on the actual punctured boundary family. -/
abbrev puncturedAtlasMarking :=
  smoothOverlapMarking (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R) j

/-- The full original four-torsion scheme is retained over every punctured atlas test. -/
abbrev puncturedAtlasTorsionBasis :=
  smoothOverlapTorsionBasis (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R) j

/-- The punctured atlas marking is faithful on every nonempty source scheme. -/
theorem puncturedAtlasMarking_injective [Nonempty T] :
    Function.Injective (puncturedAtlasMarking R h₂ j) :=
  smoothOverlapMarking_injective _ _ _ _ _

/-- The normalized family compares to the original punctured group on every source. -/
abbrev puncturedAtlasNormalizedGroupIso :=
  smoothSchemeNormalizedGroupIso (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R) j

/-- The actual arbitrary-source map to the normalized slice is the constructed normalization. -/
theorem puncturedAtlasNormalized_scheme :
    j ≫ puncturedAtlasNormalized R h₂ =
      auxiliarySchemeNormalizedSlicePoint (j ≫ puncturedAtlasPoint R h₂) :=
  smoothNormalizedOverlap_scheme _ _ _ _ _

/-- The punctured cubic compares with the complete-family pullback over the punctured base. -/
def puncturedCompleteBoundaryIso :
    puncturedFamily R ≅ (Over.pullback (puncturedBaseInclusion R)).obj
      (family (PowerSeries.X : PowerSeries R)) :=
  Over.isoMk (puncturedComplete_isPullback R).isoPullback
    (puncturedComplete_isPullback R).isoPullback_hom_snd

/-- The original punctured group family is the original complete smoothing after base change. -/
def puncturedAtlasCompleteOverIso :
    (puncturedAtlasGroup R h₂ j).X ≅
      (Over.pullback ((j ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R)).obj
        (family (PowerSeries.X : PowerSeries R)) := by
  change (Over.pullback (j ≫ puncturedAtlasProjection R h₂)).obj (puncturedFamily R) ≅ _
  exact (Over.pullback (j ≫ puncturedAtlasProjection R h₂)).mapIso
      (puncturedCompleteBoundaryIso R) ≪≫
    (Over.pullbackComp (j ≫ puncturedAtlasProjection R h₂) (puncturedBaseInclusion R)).symm.app
      (family (PowerSeries.X : PowerSeries R))

/-- On arbitrary source schemes the normalized atlas is the actual complete-family pullback. -/
def puncturedAtlasSchemeFamilyIso :
    (auxiliarySchemeGroup
      (auxiliarySchemeNormalizedPoint (j ≫ puncturedAtlasPoint R h₂))).X ≅
        (Over.pullback ((j ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R)).obj
          (family (PowerSeries.X : PowerSeries R)) :=
  smoothSchemeNormalizedOverIso (puncturedParameter R) (puncturedTwo_isUnit R h₂)
      (puncturedParameter_isUnit R) (puncturedFactor_isUnit R) j ≪≫
    puncturedAtlasCompleteOverIso R h₂ j

/-- The complete-family comparison retains the actual arbitrary source base. -/
@[reassoc] theorem puncturedAtlasSchemeFamilyIso_base :
    (puncturedAtlasSchemeFamilyIso R h₂ j).hom.left ≫
      ((Over.pullback ((j ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R)).obj
        (family (PowerSeries.X : PowerSeries R))).hom =
      (auxiliarySchemeGroup
        (auxiliarySchemeNormalizedPoint (j ≫ puncturedAtlasPoint R h₂))).X.hom :=
  (puncturedAtlasSchemeFamilyIso R h₂ j).hom.w

end FLT.Mazur.OneGonSmoothing
